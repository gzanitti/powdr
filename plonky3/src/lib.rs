//! Plonky3 adapter for powdr
//! Since plonky3 does not have fixed columns, we encode them as witness columns.
//! The encoded plonky3 columns are chosen to be the powdr witness columns followed by the powdr fixed columns
//! TODO: refactor powdr to remove the distinction between fixed and witness columns, so that we do not have to rearrange things here

use std::collections::BTreeMap;

use p3_field::{AbstractField, Field};
use p3_fri::{FriConfig, TwoAdicFriPcs};
use p3_goldilocks::{Goldilocks, MdsMatrixGoldilocks};

use p3_matrix::{dense::RowMajorMatrix, MatrixRowSlices};
use p3_merkle_tree::FieldMerkleTreeMmcs;
use p3_poseidon::Poseidon;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use powdr_ast::analyzed::{
    AlgebraicBinaryOperator, AlgebraicExpression, AlgebraicUnaryOperator, Analyzed, IdentityKind,
    PolynomialType,
};

use powdr_executor::witgen::WitgenCallback;

use p3_air::{Air, AirBuilder, BaseAir};
use powdr_number::{FieldElement, KnownField, LargeInt};
use rand::thread_rng;

use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_uni_stark::{prove, verify, Proof, StarkConfig};
use p3_util::log2_ceil_usize;

type Val = p3_goldilocks::Goldilocks;
type Challenge = BinomialExtensionField<Val, 2>;
type Perm = Poseidon<Val, MdsMatrixGoldilocks, 8, 7>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type ValMmcs =
    FieldMerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 4>;
type Challenger = DuplexChallenger<Val, Perm, 8>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Dft = Radix2DitParallel;
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

#[derive(Clone)]
pub struct Plonky3Prover<'a, T> {
    /// The analyzed PIL
    analyzed: &'a Analyzed<T>,
    /// The value of the fixed columns
    fixed: &'a [(String, Vec<T>)],
}

impl<'a, T> Plonky3Prover<'a, T> {
    pub fn new(analyzed: &'a Analyzed<T>, fixed: &'a [(String, Vec<T>)]) -> Self {
        Self { analyzed, fixed }
    }
}

fn cast_to_goldilocks<T: FieldElement>(v: T) -> Goldilocks {
    Goldilocks::from_canonical_u64(v.to_integer().try_into_u64().unwrap())
}

#[derive(Clone)]
pub(crate) struct PowdrCircuit<'a, T> {
    /// The analyzed PIL
    analyzed: &'a Analyzed<T>,
    /// The value of the fixed columns
    fixed: &'a [(String, Vec<T>)],
    /// The value of the witness columns, if set
    witness: Option<&'a [(String, Vec<T>)]>,
    /// Column name and index of the public cells
    publics: Vec<(String, usize)>,
    /// Callback to augment the witness in the later stages.
    _witgen_callback: Option<WitgenCallback<T>>,
}

impl<'a, T: FieldElement> PowdrCircuit<'a, T> {
    pub(crate) fn new(analyzed: &'a Analyzed<T>, fixed: &'a [(String, Vec<T>)]) -> Self {
        let mut publics = analyzed
            .public_declarations
            .values()
            .map(|public_declaration| {
                let witness_name = public_declaration.referenced_poly_name();
                let witness_offset = public_declaration.index as usize;
                (witness_name, witness_offset)
            })
            .collect::<Vec<_>>();
        // Sort, so that the order is deterministic
        publics.sort();

        Self {
            analyzed,
            fixed,
            witness: None,
            publics,
            _witgen_callback: None,
        }
    }

    fn witness(&self) -> &'a [(String, Vec<T>)] {
        self.witness.as_ref().unwrap()
    }

    pub(crate) fn with_witness(self, witness: &'a [(String, Vec<T>)]) -> Self {
        Self {
            witness: Some(witness),
            ..self
        }
    }

    pub(crate) fn with_witgen_callback(self, witgen_callback: WitgenCallback<T>) -> Self {
        Self {
            _witgen_callback: Some(witgen_callback),
            ..self
        }
    }

    /// Computes the instance column from the witness
    pub(crate) fn instance_column(&self) -> Vec<Goldilocks> {
        let witness = self
            .witness
            .as_ref()
            .expect("Witness needs to be set")
            .iter()
            .map(|(name, values)| (name, values))
            .collect::<BTreeMap<_, _>>();

        self.publics
            .iter()
            .map(|(col_name, i)| cast_to_goldilocks(witness.get(col_name).unwrap()[*i]))
            .collect()
    }

    fn to_plonky3_expr<AB: AirBuilder<F = Goldilocks>>(
        &self,
        e: &AlgebraicExpression<T>,
        builder: &AB,
    ) -> AB::Expr {
        let matrix = builder.main();

        let res = match e {
            AlgebraicExpression::Reference(r) => {
                let poly_id = r.poly_id;

                let row = match r.next {
                    true => matrix.row_slice(1),
                    false => matrix.row_slice(0),
                };

                // witness columns indexes are unchanged, fixed ones are offset
                let index = match poly_id.ptype {
                    PolynomialType::Committed => self
                        .witness()
                        .iter()
                        .position(|(name, _)| *name == r.name)
                        .unwrap(),
                    PolynomialType::Constant => {
                        self.witness().len()
                            + self
                                .fixed
                                .iter()
                                .position(|(name, _)| *name == r.name)
                                .unwrap()
                    }
                    PolynomialType::Intermediate => {
                        unreachable!("intermediate polynomials should have been inlined")
                    }
                };

                row[index].into()
            }
            AlgebraicExpression::PublicReference(_) => unimplemented!(
                "public references are not supported inside algebraic expressions in plonky3"
            ),
            AlgebraicExpression::Number(n) => AB::Expr::from(cast_to_goldilocks(*n)),
            AlgebraicExpression::BinaryOperation(left, op, right) => {
                let left = self.to_plonky3_expr(left, builder);
                let right = self.to_plonky3_expr(right, builder);

                match op {
                    AlgebraicBinaryOperator::Add => left + right,
                    AlgebraicBinaryOperator::Sub => left - right,
                    AlgebraicBinaryOperator::Mul => left * right,
                    AlgebraicBinaryOperator::Pow => {
                        unreachable!("exponentiations should have been evaluated")
                    }
                }
            }
            AlgebraicExpression::UnaryOperation(op, e) => {
                let e: <AB as AirBuilder>::Expr = self.to_plonky3_expr(e, builder);

                match op {
                    AlgebraicUnaryOperator::Minus => -e,
                }
            }
            AlgebraicExpression::Challenge(challenge) => {
                unimplemented!("Challenge API for {challenge:?} not accessible in plonky3")
            }
        };
        res
    }
}

impl<'a, T: FieldElement> Plonky3Prover<'a, T> {
    pub fn prove_ast(
        &self,
        witness: &[(String, Vec<T>)],
        witgen_callback: WitgenCallback<T>,
    ) -> Result<Vec<u8>, String> {
        assert_eq!(T::known_field(), Some(KnownField::GoldilocksField));

        let circuit = PowdrCircuit::new(self.analyzed, self.fixed)
            .with_witgen_callback(witgen_callback)
            .with_witness(witness);
        let publics = circuit.instance_column();

        let trace = circuit.preprocessed_trace().unwrap();

        let (config, perm) = self.get_config_and_perm();

        let mut challenger = Challenger::new(perm.clone());

        let proof = prove(&config, &circuit, &mut challenger, trace, &publics);

        let mut challenger = Challenger::new(perm);

        verify(&config, &circuit, &mut challenger, &proof, &publics).unwrap();
        Ok(serde_json::to_vec(&proof).unwrap())
    }

    fn get_config_and_perm(&self) -> (StarkConfig<Pcs, Challenge, Challenger>, Perm) {
        let perm = Perm::new_from_rng(4, 22, MdsMatrixGoldilocks, &mut thread_rng());

        let hash = MyHash::new(perm.clone());

        let compress = MyCompress::new(perm.clone());

        let val_mmcs = ValMmcs::new(hash, compress);

        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

        let dft = Dft {};

        let fri_config = FriConfig {
            log_blowup: 1,
            num_queries: 100,
            proof_of_work_bits: 16,
            mmcs: challenge_mmcs,
        };

        let pcs = Pcs::new(
            log2_ceil_usize(self.analyzed.degree() as usize),
            dft,
            val_mmcs,
            fri_config,
        );

        let config = MyConfig::new(pcs);

        (config, perm)
    }

    pub fn verify(&self, proof: &[u8], instances: &[Vec<T>]) -> Result<(), String> {
        let proof: Proof<_> = serde_json::from_slice(proof)
            .map_err(|e| format!("Failed to deserialize proof: {e}"))?;
        let publics = instances
            .iter()
            .flatten()
            .map(|v| cast_to_goldilocks(*v))
            .collect();

        let (config, perm) = self.get_config_and_perm();

        let mut challenger = Challenger::new(perm);

        verify(
            &config,
            &PowdrCircuit::new(self.analyzed, self.fixed),
            &mut challenger,
            &proof,
            &publics,
        )
        .map_err(|e| format!("Failed to verify proof: {e:?}"))
    }
}

impl<'a, T: FieldElement> BaseAir<Goldilocks> for PowdrCircuit<'a, T> {
    fn width(&self) -> usize {
        self.analyzed.commitment_count()
            + self.analyzed.constant_count()
            + self.analyzed.intermediate_count()
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<Goldilocks>> {
        let width = self.witness().len() + self.fixed.len();
        let joined_iter = self.witness().iter().chain(self.fixed);
        let len = self.analyzed.degree.unwrap();

        let values = (0..len)
            .flat_map(move |i| {
                joined_iter
                    .clone()
                    .map(move |(_, v)| cast_to_goldilocks(v[i as usize]))
            })
            .collect();

        Some(RowMajorMatrix::new(values, width))
    }
}

impl<'a, T: FieldElement, AB: AirBuilder<F = Goldilocks>> Air<AB> for PowdrCircuit<'a, T> {
    fn eval(&self, builder: &mut AB) {
        for identity in &self
            .analyzed
            .identities_with_inlined_intermediate_polynomials()
        {
            match identity.kind {
                IdentityKind::Polynomial => {
                    assert_eq!(identity.left.expressions.len(), 0);
                    assert_eq!(identity.right.expressions.len(), 0);
                    assert!(identity.right.selector.is_none());

                    let left =
                        self.to_plonky3_expr(identity.left.selector.as_ref().unwrap(), builder);

                    builder.assert_zero(left);
                }
                IdentityKind::Plookup => unimplemented!("Plonky3 does not support plookup"),
                IdentityKind::Permutation => unimplemented!("Plonky does not support permutations"),
                IdentityKind::Connect => unimplemented!("Plonky3 does not support connections"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use powdr_number::GoldilocksField;
    use powdr_pipeline::Pipeline;

    use crate::Plonky3Prover;

    /// Prove and verify execution using a trivial PCS (coefficients of the polynomials)
    fn run_test_goldilocks_trivial_pcs(pil: &str) {
        let mut pipeline = Pipeline::<GoldilocksField>::default().from_pil_string(pil.to_string());

        let pil = pipeline.compute_optimized_pil().unwrap();
        let fixed_cols = pipeline.compute_fixed_cols().unwrap();
        let witness_callback = pipeline.witgen_callback().unwrap();
        let witness = pipeline.compute_witness().unwrap();

        let proof = Plonky3Prover::new(&pil, &fixed_cols).prove_ast(&witness, witness_callback);

        assert!(proof.is_ok());
    }

    #[test]
    fn publics() {
        let content = "namespace Global(8); pol witness x; x * (x - 1) = 0; public out = x(7);";
        run_test_goldilocks_trivial_pcs(content);
    }

    #[test]
    #[should_panic = "assertion failed: width >= 1"]
    fn empty() {
        let content = "namespace Global(8);";
        run_test_goldilocks_trivial_pcs(content);
    }

    #[test]
    #[should_panic = "not implemented"]
    fn challenge() {
        let content = r#"
        let N: int = 8;
        namespace std::prover(N);
            let challenge = [];
            enum Query {
                Hint(int)
            }
        
        namespace Global(N); 
            let beta: expr = std::prover::challenge(0, 42); 
            col witness stage(0) x;
            col witness stage(1) y;
            x + beta = y + beta;
        "#;
        run_test_goldilocks_trivial_pcs(content);
    }

    #[test]
    fn polynomial_identity() {
        let content = "namespace Global(8); pol fixed z = [1, 2]*; pol witness a; a = z + 1;";
        run_test_goldilocks_trivial_pcs(content);
    }

    #[test]
    #[should_panic = "not implemented"]
    fn lookup() {
        let content = "namespace Global(8); pol fixed z = [0, 1]*; pol witness a; a in z;";
        run_test_goldilocks_trivial_pcs(content);
    }
}