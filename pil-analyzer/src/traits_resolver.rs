use std::collections::{HashMap, HashSet};

use powdr_ast::{
    analyzed::{Expression, FunctionValueDefinition, Symbol},
    parsed::{
        types::{TupleType, Type, TypeScheme},
        TraitDeclaration, TraitImplementation,
    },
};

use crate::type_unifier::Unifier;

pub struct TraitsResolver<'a> {
    definitions: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
}

impl<'a> TraitsResolver<'a> {
    pub fn new(
        definitions: &'a HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    ) -> Self {
        Self { definitions }
    }

    /// Checks for overlapping trait implementations.
    ///
    /// This method iterates through all the trait implementations.
    /// For each implementation, it checks that there are no traits with the same name and overlapping type variables.
    /// Overlapping implementations can lead to ambiguity in trait function calls, even when all types
    /// are fully concrete. This check helps prevent such ambiguities and ensures clear resolution
    /// of trait function calls.
    ///
    /// It also checks that the number of type variables in the implementation matches
    /// the number of type variables in the corresponding trait declaration.
    pub fn validate_trait_implementations(
        &self,
        implementations: &mut HashMap<String, Vec<TraitImplementation<Expression>>>,
    ) {
        for (trait_name, trait_impls) in implementations.iter_mut() {
            let trait_decl = self
                .definitions
                .get(&trait_name.clone())
                .unwrap_or_else(|| panic!("Trait {trait_name} not found"))
                .1
                .as_ref()
                .unwrap_or_else(|| panic!("Trait definition for {trait_name} not found"));

            let FunctionValueDefinition::TraitDeclaration(trait_decl) = trait_decl else {
                panic!("Invalid trait declaration");
            };

            self.validate_impl_definitions(trait_impls, trait_decl);
            self.ensure_unique_impls(trait_impls);
        }
    }

    /// Validates the trait implementation definitions in the given `implementations` map against the trait
    /// declarations in the `definitions` map.
    fn validate_impl_definitions(
        &self,
        implementations: &[TraitImplementation<Expression>],
        trait_decl: &TraitDeclaration,
    ) {
        for trait_impl in implementations {
            let Type::Tuple(TupleType { items: mut types }) = trait_impl.type_scheme.ty.clone()
            else {
                panic!("Type from trait scheme is not a tuple.")
            };
            let trait_name = trait_impl.name.clone();

            if types.len() != trait_decl.type_vars.len() {
                panic!(
                    "{}",
                    trait_impl.source_ref.with_error(format!(
                        "Trait {} has {} type parameters, but implementation has {}",
                        trait_name,
                        trait_decl.type_vars.len(),
                        types.len(),
                    ))
                );
            }

            let type_vars_in_tuple: Vec<_> = types
                .iter_mut()
                .flat_map(|t| t.contained_type_vars())
                .collect();

            let type_vars_in_scheme: Vec<_> = trait_impl.type_scheme.vars.vars().collect();

            for var in type_vars_in_scheme {
                if !type_vars_in_tuple.contains(&var) {
                    panic!(
                        "{}",
                        trait_impl.source_ref.with_error(format!(
                            "Impl {trait_name} introduces a type variable {var} that is not used",
                        ))
                    );
                }
            }
        }
    }

    /// Ensures that there are no overlapping trait implementations in the given `implementations` map.
    ///
    /// This function iterates through all the trait implementations comparing them with each other and ensuring that
    /// there are no traits with overlapping type variables.
    fn ensure_unique_impls(&self, implementations: &mut [TraitImplementation<Expression>]) {
        for i in 0..implementations.len() {
            let type_vars: HashSet<_> = implementations[i].type_scheme.vars.vars().collect();
            implementations[i]
                .type_scheme
                .ty
                .map_to_type_vars(&type_vars);

            for j in (i + 1)..implementations.len() {
                let type_vars: HashSet<_> = implementations[j].type_scheme.vars.vars().collect();
                implementations[j]
                    .type_scheme
                    .ty
                    .map_to_type_vars(&type_vars);

                self.unify_traits_types(
                    &implementations[i].type_scheme,
                    &implementations[j].type_scheme,
                )
                .map_err(|err| {
                    implementations[i]
                        .source_ref
                        .with_error(format!("Impls for {}: {err}", implementations[i].name))
                })
                .unwrap()
            }
        }
    }

    fn unify_traits_types(&self, ty1: &TypeScheme, ty2: &TypeScheme) -> Result<(), String> {
        let mut unifier = Unifier::new();
        let instantiated_ty1 = unifier.instantiate_scheme(ty1.clone());
        let instantiated_ty2 = unifier.instantiate_scheme(ty2.clone());

        match unifier.unify_types(instantiated_ty1.0.clone(), instantiated_ty2.0.clone()) {
            Ok(_) => Err(format!("Types {} and {} overlap", ty1.ty, ty2.ty)),
            Err(_) => Ok(()),
        }
    }
}

pub fn traits_unification(
    definitions: &HashMap<String, (Symbol, Option<FunctionValueDefinition>)>,
    //identities: &Vec<Identity<SelectedExpressions<Expression>>>, // TODO: To be added
    trait_impls: &mut HashMap<String, Vec<TraitImplementation<Expression>>>,
) {
    TraitsResolver::new(definitions).validate_trait_implementations(trait_impls);
}
