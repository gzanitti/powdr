pub mod asm;
pub mod build;
pub mod display;
pub mod folder;
pub mod types;
pub mod visitor;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    iter::{empty, once},
    ops,
    str::FromStr,
};

use auto_enums::auto_enum;
use derive_more::Display;
use powdr_number::{BigInt, BigUint, DegreeType};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use powdr_parser_util::SourceRef;

use crate::analyzed::Reference;

use self::{
    asm::{Part, SymbolPath},
    types::{FunctionType, Type, TypeBounds, TypeScheme},
    visitor::{Children, ExpressionVisitable},
};

#[derive(Display, Clone, Copy, PartialEq, Eq)]
pub enum SymbolCategory {
    /// A value, which has a type and can be referenced in expressions (a variable, function, constant, ...).
    Value,
    /// A type, for example the name of an enum or other user-defined type.
    Type,
    /// A type constructor, i.e. an enum variant, which can be used as a function or constant inside an expression
    /// or to deconstruct a value in a pattern.
    TypeConstructor,
    /// A trait declaration, which can be used as a type.
    TraitDeclaration,
}
impl SymbolCategory {
    /// Returns if a symbol of a given category can satisfy a request for a certain category.
    pub fn compatible_with_request(&self, request: SymbolCategory) -> bool {
        match self {
            SymbolCategory::Value => request == SymbolCategory::Value,
            SymbolCategory::Type => request == SymbolCategory::Type,
            SymbolCategory::TypeConstructor => {
                // Type constructors can also satisfy requests for values.
                request == SymbolCategory::TypeConstructor || request == SymbolCategory::Value
            }
            SymbolCategory::TraitDeclaration => request == SymbolCategory::TraitDeclaration,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PILFile(pub Vec<PilStatement>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum PilStatement {
    /// File name
    Include(SourceRef, String),
    /// Name of namespace and optional polynomial degree (constant)
    Namespace(SourceRef, SymbolPath, Option<Expression>),
    LetStatement(
        SourceRef,
        String,
        Option<TypeScheme<Expression>>,
        Option<Expression>,
    ),
    PolynomialDefinition(SourceRef, PolynomialName, Expression),
    PublicDeclaration(
        SourceRef,
        /// The name of the public value.
        String,
        /// The polynomial/column that contains the public value.
        NamespacedPolynomialReference,
        /// If the polynomial is an array, this is the array element index.
        Option<Expression>,
        /// The row number of the public value.
        Expression,
    ),
    PolynomialConstantDeclaration(SourceRef, Vec<PolynomialName>),
    PolynomialConstantDefinition(SourceRef, String, FunctionDefinition),
    PolynomialCommitDeclaration(
        SourceRef,
        // Stage
        Option<u32>,
        // Names
        Vec<PolynomialName>,
        // Value (prover query / hint)
        Option<FunctionDefinition>,
    ),
    PlookupIdentity(
        SourceRef,
        SelectedExpressions<Expression>,
        SelectedExpressions<Expression>,
    ),
    PermutationIdentity(
        SourceRef,
        SelectedExpressions<Expression>,
        SelectedExpressions<Expression>,
    ),
    ConnectIdentity(SourceRef, Vec<Expression>, Vec<Expression>),
    EnumDeclaration(SourceRef, EnumDeclaration<Expression>),
    TraitImplementation(SourceRef, TraitImplementation<Expression>),
    TraitDeclaration(SourceRef, TraitDeclaration<Expression>),
    Expression(SourceRef, Expression),
}

impl PilStatement {
    /// If the statement is a symbol definition, returns all (local) names of defined symbols
    /// and their category.
    /// Note it does not return nested definitions (for an enum for example).
    pub fn symbol_definition_names(&self) -> impl Iterator<Item = (&String, SymbolCategory)> + '_ {
        self.symbol_definition_names_and_contained()
            .filter_map(|(name, sub_name, category)| match sub_name {
                Some(_) => None,
                None => Some((name, category)),
            })
    }

    /// If the statement is a symbol definition, returns all (local) names of defined symbols
    /// and their category.
    /// For an enum, returns the name of the enum and all the variants, where the first
    /// component is the name of the enum and the second the name of the variant.
    pub fn symbol_definition_names_and_contained(
        &self,
    ) -> Box<dyn Iterator<Item = (&String, Option<&String>, SymbolCategory)> + '_> {
        match self {
            PilStatement::PolynomialDefinition(_, PolynomialName { name, .. }, _)
            | PilStatement::PolynomialConstantDefinition(_, name, _)
            | PilStatement::PublicDeclaration(_, name, _, _, _)
            | PilStatement::LetStatement(_, name, _, _) => {
                Box::new(once((name, None, SymbolCategory::Value)))
            }
            PilStatement::EnumDeclaration(_, EnumDeclaration { name, variants, .. }) => Box::new(
                once((name, None, SymbolCategory::Type)).chain(
                    variants
                        .iter()
                        .map(move |v| (name, Some(&v.name), SymbolCategory::TypeConstructor)),
                ),
            ),
            PilStatement::TraitDeclaration(
                _,
                TraitDeclaration {
                    name, functions, ..
                },
            ) => Box::new(
                once((name, None, SymbolCategory::TraitDeclaration)).chain(
                    functions
                        .iter()
                        .map(move |f| (name, Some(&f.name), SymbolCategory::Value)),
                ),
            ),
            PilStatement::PolynomialConstantDeclaration(_, polynomials)
            | PilStatement::PolynomialCommitDeclaration(_, _, polynomials, _) => Box::new(
                polynomials
                    .iter()
                    .map(|p| (&p.name, None, SymbolCategory::Value)),
            ),

            PilStatement::Include(_, _)
            | PilStatement::Namespace(_, _, _)
            | PilStatement::PlookupIdentity(_, _, _)
            | PilStatement::PermutationIdentity(_, _, _)
            | PilStatement::ConnectIdentity(_, _, _)
            | PilStatement::Expression(_, _)
            | PilStatement::TraitImplementation(_, _) => Box::new(empty()),
        }
    }
}

impl Children<Expression> for PilStatement {
    /// Returns an iterator over all (top-level) expressions in this statement.
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            PilStatement::PlookupIdentity(_, left, right)
            | PilStatement::PermutationIdentity(_, left, right) => {
                Box::new(left.children().chain(right.children()))
            }
            PilStatement::ConnectIdentity(_start, left, right) => {
                Box::new(left.iter().chain(right.iter()))
            }
            PilStatement::Expression(_, e) | PilStatement::Namespace(_, _, Some(e)) => {
                Box::new(once(e))
            }
            PilStatement::PolynomialDefinition(_, PolynomialName { array_size, .. }, e) => {
                Box::new(array_size.iter().chain(once(e)))
            }

            PilStatement::EnumDeclaration(_, enum_decl) => enum_decl.children(),
            PilStatement::TraitImplementation(_, trait_impl) => trait_impl.children(),
            PilStatement::TraitDeclaration(_, trait_decl) => trait_decl.children(),

            PilStatement::LetStatement(_, _, type_scheme, value) => Box::new(
                type_scheme
                    .iter()
                    .flat_map(|t| t.ty.children())
                    .chain(value),
            ),

            PilStatement::PublicDeclaration(_, _, _, i, e) => Box::new(i.iter().chain(once(e))),

            PilStatement::PolynomialConstantDefinition(_, _, def)
            | PilStatement::PolynomialCommitDeclaration(_, _, _, Some(def)) => def.children(),
            PilStatement::PolynomialCommitDeclaration(_, _, _, None)
            | PilStatement::Include(_, _)
            | PilStatement::Namespace(_, _, None)
            | PilStatement::PolynomialConstantDeclaration(_, _) => Box::new(empty()),
        }
    }

    /// Returns an iterator over all (top-level) expressions in this statement.
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            PilStatement::PlookupIdentity(_, left, right)
            | PilStatement::PermutationIdentity(_, left, right) => {
                Box::new(left.children_mut().chain(right.children_mut()))
            }
            PilStatement::ConnectIdentity(_start, left, right) => {
                Box::new(left.iter_mut().chain(right.iter_mut()))
            }
            PilStatement::Expression(_, e) | PilStatement::Namespace(_, _, Some(e)) => {
                Box::new(once(e))
            }

            PilStatement::PolynomialDefinition(_, PolynomialName { array_size, .. }, e) => {
                Box::new(array_size.iter_mut().chain(once(e)))
            }

            PilStatement::EnumDeclaration(_, enum_decl) => enum_decl.children_mut(),
            PilStatement::TraitImplementation(_, trait_impl) => trait_impl.children_mut(),
            PilStatement::TraitDeclaration(_, trait_decl) => trait_decl.children_mut(),

            PilStatement::LetStatement(_, _, ty, value) => {
                Box::new(ty.iter_mut().flat_map(|t| t.ty.children_mut()).chain(value))
            }

            PilStatement::PublicDeclaration(_, _, _, i, e) => Box::new(i.iter_mut().chain(once(e))),

            PilStatement::PolynomialConstantDefinition(_, _, def)
            | PilStatement::PolynomialCommitDeclaration(_, _, _, Some(def)) => def.children_mut(),
            PilStatement::PolynomialCommitDeclaration(_, _, _, None)
            | PilStatement::Include(_, _)
            | PilStatement::Namespace(_, _, None)
            | PilStatement::PolynomialConstantDeclaration(_, _) => Box::new(empty()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct EnumDeclaration<E = u64> {
    pub name: String,
    pub type_vars: TypeBounds,
    pub variants: Vec<EnumVariant<E>>,
}

impl<R> Children<Expression<R>> for EnumDeclaration<u64> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(empty())
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(empty())
    }
}

impl<R> Children<Expression<R>> for EnumDeclaration<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(self.variants.iter().flat_map(|v| v.children()))
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(self.variants.iter_mut().flat_map(|v| v.children_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct EnumVariant<E = u64> {
    pub name: String,
    pub fields: Option<Vec<Type<E>>>,
}

impl<E: Clone> EnumVariant<E> {
    /// Returns the type of the constructor function for this variant
    /// given the enum type.
    pub fn constructor_type(&self, enum_decl: &EnumDeclaration) -> TypeScheme<E> {
        let name = SymbolPath::from_str(&enum_decl.name).unwrap();
        let vars = enum_decl.type_vars.clone();
        let generic_args =
            (!vars.is_empty()).then(|| vars.vars().cloned().map(Type::TypeVar).collect::<Vec<_>>());

        let named_type = Type::NamedType(name, generic_args);

        let ty = match &self.fields {
            None => named_type,
            Some(fields) => Type::Function(FunctionType {
                params: (*fields).clone(),
                value: named_type.into(),
            }),
        };

        TypeScheme { vars, ty }
    }
}

impl<R> Children<Expression<R>> for EnumVariant<u64> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(empty())
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(empty())
    }
}

impl<R> Children<Expression<R>> for EnumVariant<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(
            self.fields
                .iter()
                .flat_map(|f| f.iter())
                .flat_map(|f| f.children()),
        )
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(
            self.fields
                .iter_mut()
                .flat_map(|f| f.iter_mut())
                .flat_map(|f| f.children_mut()),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TraitImplementation<Expr> {
    pub name: SymbolPath,
    pub type_scheme: TypeScheme,
    pub functions: Vec<NamedExpression<Expr>>,
}

impl<R> Children<Expression<R>> for TraitImplementation<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(self.functions.iter().flat_map(|m| m.body.children()))
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(
            self.functions
                .iter_mut()
                .flat_map(|m| m.body.children_mut()),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct NamedExpression<Expr> {
    pub name: String,
    pub body: Box<Expr>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TraitDeclaration<E = u64> {
    pub name: String,
    pub type_vars: Vec<String>,
    pub functions: Vec<TraitFunction<E>>,
}

impl TraitDeclaration<u64> {
    pub fn function_by_name(&self, name: &str) -> Option<&TraitFunction> {
        self.functions.iter().find(|f| f.name == name)
    }
}

impl<R> Children<Expression<R>> for TraitDeclaration<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        Box::new(self.functions.iter().flat_map(|f| f.children()))
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        Box::new(self.functions.iter_mut().flat_map(|f| f.children_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TraitFunction<E = u64> {
    pub name: String,
    pub ty: Type<E>,
}

impl<R> Children<Expression<R>> for TraitFunction<Expression<R>> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<R>> + '_> {
        self.ty.children()
    }
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<R>> + '_> {
        self.ty.children_mut()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct SelectedExpressions<E = Expression<NamespacedPolynomialReference>> {
    pub selector: Option<E>,
    pub expressions: Box<E>,
}

impl<T> Default for SelectedExpressions<Expression<T>> {
    fn default() -> Self {
        Self {
            selector: Default::default(),
            expressions: Box::new(ArrayLiteral { items: vec![] }.into()),
        }
    }
}

impl<T> Children<Expression<T>> for SelectedExpressions<Expression<T>> {
    /// Returns an iterator over all (top-level) expressions in this SelectedExpressions.
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<T>> + '_> {
        Box::new(self.selector.iter().chain(self.expressions.children()))
    }

    /// Returns an iterator over all (top-level) expressions in this SelectedExpressions.
    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<T>> + '_> {
        Box::new(
            self.selector
                .iter_mut()
                .chain(self.expressions.children_mut()),
        )
    }
}

#[derive(Debug, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub enum Expression<Ref = NamespacedPolynomialReference> {
    Reference(SourceRef, Ref),
    PublicReference(SourceRef, String),
    // A number literal and its type.
    Number(SourceRef, Number),
    String(SourceRef, String),
    Tuple(SourceRef, Vec<Self>),
    LambdaExpression(SourceRef, LambdaExpression<Self>),
    ArrayLiteral(SourceRef, ArrayLiteral<Self>),
    UnaryOperation(SourceRef, UnaryOperation<Self>),
    BinaryOperation(SourceRef, BinaryOperation<Self>),
    IndexAccess(SourceRef, IndexAccess<Self>),
    FunctionCall(SourceRef, FunctionCall<Self>),
    FreeInput(SourceRef, Box<Self>),
    MatchExpression(SourceRef, MatchExpression<Self>),
    IfExpression(SourceRef, IfExpression<Self>),
    BlockExpression(SourceRef, BlockExpression<Self>),
}

/// Comparison function for expressions that ignore source information.
macro_rules! impl_partial_eq_for_expression {
    ($($variant:ident),*) => {
        impl<Ref: PartialEq> PartialEq for Expression<Ref> {
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    $(
                        (Expression::$variant(_, a), Expression::$variant(_, b)) => a == b,
                    )*
                    // This catches the case where variants are different and returns false
                    $(
                        (Expression::$variant(_, _), _) => false,
                    )*
                }
            }
        }
    }
}

impl_partial_eq_for_expression!(
    Reference,
    PublicReference,
    Number,
    String,
    Tuple,
    LambdaExpression,
    ArrayLiteral,
    BinaryOperation,
    UnaryOperation,
    IndexAccess,
    FunctionCall,
    FreeInput,
    MatchExpression,
    IfExpression,
    BlockExpression
);

pub trait SourceReference {
    fn source_reference(&self) -> &SourceRef;
    fn source_reference_mut(&mut self) -> &mut SourceRef;
}

macro_rules! impl_source_reference {
    ($enum:ident, $($variant:ident),*) => {
        impl<E> SourceReference for $enum<E> {
            fn source_reference(&self) -> &SourceRef {
                match self {
                    $( $enum::$variant(src, _) => src, )*
                }
            }

            fn source_reference_mut(&mut self) -> &mut SourceRef {
                match self {
                    $( $enum::$variant(src, _) => src, )*
                }
            }
        }
    }
}

impl_source_reference!(
    Expression,
    Reference,
    PublicReference,
    Number,
    String,
    Tuple,
    LambdaExpression,
    ArrayLiteral,
    BinaryOperation,
    UnaryOperation,
    IndexAccess,
    FunctionCall,
    FreeInput,
    MatchExpression,
    IfExpression,
    BlockExpression
);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct UnaryOperation<E = Expression<NamespacedPolynomialReference>> {
    pub op: UnaryOperator,
    pub expr: Box<E>,
}

impl<Ref> From<UnaryOperation<Expression<Ref>>> for Expression<Ref> {
    fn from(operation: UnaryOperation<Expression<Ref>>) -> Self {
        Expression::UnaryOperation(SourceRef::unknown(), operation)
    }
}

impl<E> Children<E> for UnaryOperation<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(self.expr.as_ref()))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(self.expr.as_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct BinaryOperation<E = Expression<NamespacedPolynomialReference>> {
    pub left: Box<E>,
    pub op: BinaryOperator,
    pub right: Box<E>,
}

impl<Ref> From<BinaryOperation<Expression<Ref>>> for Expression<Ref> {
    fn from(operation: BinaryOperation<Expression<Ref>>) -> Self {
        Expression::BinaryOperation(SourceRef::unknown(), operation)
    }
}

impl<E> Children<E> for BinaryOperation<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new([self.left.as_ref(), self.right.as_ref()].into_iter())
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new([self.left.as_mut(), self.right.as_mut()].into_iter())
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct Number {
    #[schemars(skip)]
    pub value: BigUint,
    pub type_: Option<Type>,
}

impl<Ref> From<Number> for Expression<Ref> {
    fn from(number: Number) -> Self {
        Expression::Number(SourceRef::unknown(), number)
    }
}

impl<Ref> From<BigUint> for Expression<Ref> {
    fn from(value: BigUint) -> Self {
        Number { value, type_: None }.into()
    }
}

impl<Ref> From<u32> for Expression<Ref> {
    fn from(value: u32) -> Self {
        BigUint::from(value).into()
    }
}
pub type ExpressionPrecedence = u64;

impl<Ref> Expression<Ref> {
    pub fn new_binary(left: Self, op: BinaryOperator, right: Self) -> Self {
        Expression::BinaryOperation(
            SourceRef::unknown(),
            BinaryOperation {
                left: Box::new(left),
                op,
                right: Box::new(right),
            },
        )
    }

    /// Visits this expression and all of its sub-expressions and returns true
    /// if `f` returns true on any of them.
    pub fn any(&self, mut f: impl FnMut(&Self) -> bool) -> bool {
        use std::ops::ControlFlow;
        self.pre_visit_expressions_return(&mut |e| {
            if f(e) {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        })
        .is_break()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct MatchExpression<E = Expression<NamespacedPolynomialReference>> {
    pub scrutinee: Box<E>,
    pub arms: Vec<MatchArm<E>>,
}

impl<Ref> From<MatchExpression<Expression<Ref>>> for Expression<Ref> {
    fn from(match_expr: MatchExpression<Expression<Ref>>) -> Self {
        Expression::MatchExpression(SourceRef::unknown(), match_expr)
    }
}

impl<E> Children<E> for MatchExpression<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(
            once(self.scrutinee.as_ref()).chain(self.arms.iter().flat_map(|arm| arm.children())),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(
            once(self.scrutinee.as_mut())
                .chain(self.arms.iter_mut().flat_map(|arm| arm.children_mut())),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct BlockExpression<E> {
    pub statements: Vec<StatementInsideBlock<E>>,
    pub expr: Option<Box<E>>,
}

impl<Ref> From<BlockExpression<Expression<Ref>>> for Expression<Ref> {
    fn from(block: BlockExpression<Expression<Ref>>) -> Self {
        Expression::BlockExpression(SourceRef::unknown(), block)
    }
}

impl<E> Children<E> for BlockExpression<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(
            self.statements
                .iter()
                .flat_map(|s| s.children())
                .chain(self.expr.iter().map(|boxed| &**boxed)),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(
            self.statements
                .iter_mut()
                .flat_map(|s| s.children_mut())
                .chain(self.expr.iter_mut().map(|boxed| &mut **boxed)),
        )
    }
}

impl Expression<NamespacedPolynomialReference> {
    pub fn try_to_identifier(&self) -> Option<&String> {
        if let Expression::Reference(_, r) = self {
            r.try_to_identifier()
        } else {
            None
        }
    }
}

impl<Ref> ops::Add for Expression<Ref> {
    type Output = Expression<Ref>;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, BinaryOperator::Add, rhs)
    }
}

impl<Ref> ops::Sub for Expression<Ref> {
    type Output = Expression<Ref>;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, BinaryOperator::Sub, rhs)
    }
}
impl<Ref> ops::Mul for Expression<Ref> {
    type Output = Expression<Ref>;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::new_binary(self, BinaryOperator::Mul, rhs)
    }
}

impl<Ref> std::iter::Sum for Expression<Ref> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|a, b| a + b).unwrap_or_else(|| 0u32.into())
    }
}

impl From<NamespacedPolynomialReference> for Expression {
    fn from(value: NamespacedPolynomialReference) -> Self {
        Self::Reference(SourceRef::unknown(), value)
    }
}

impl<R> Expression<R> {
    /// Returns an iterator over all (top-level) expressions in this expression.
    /// This specifically does not implement Children because otherwise it would
    /// have a wrong implementation of ExpressionVisitable (which is implemented
    /// generically for all types that implement Children<Expr>).
    #[auto_enum(Iterator)]
    pub fn children(&self) -> impl Iterator<Item = &Expression<R>> + '_ {
        match self {
            Expression::Reference(_, _)
            | Expression::PublicReference(_, _)
            | Expression::String(_, _) => empty(),
            Expression::Number(_, _) => empty(),
            Expression::Tuple(_, v) => v.iter(),
            Expression::LambdaExpression(_, lambda) => lambda.children(),
            Expression::ArrayLiteral(_, array) => array.children(),
            Expression::BinaryOperation(_, binary_op) => binary_op.children(),
            Expression::UnaryOperation(_, unary_op) => unary_op.children(),
            Expression::IndexAccess(_, index_access) => index_access.children(),
            Expression::FunctionCall(_, function_call) => function_call.children(),
            Expression::FreeInput(_, e) => once(e.as_ref()),
            Expression::MatchExpression(_, match_expr) => match_expr.children(),
            Expression::IfExpression(_, if_expr) => if_expr.children(),
            Expression::BlockExpression(_, block_expr) => block_expr.children(),
        }
    }

    /// Returns an iterator over all (top-level) expressions in this expression.
    /// This specifically does not implement Children because otherwise it would
    /// have a wrong implementation of ExpressionVisitable (which is implemented
    /// generically for all types that implement Children<Expr>).
    #[auto_enum(Iterator)]
    pub fn children_mut(&mut self) -> impl Iterator<Item = &mut Expression<R>> + '_ {
        match self {
            Expression::Reference(_, _)
            | Expression::PublicReference(_, _)
            | Expression::String(_, _) => empty(),
            Expression::Number(_, _) => empty(),
            Expression::Tuple(_, v) => v.iter_mut(),
            Expression::LambdaExpression(_, lambda) => lambda.children_mut(),
            Expression::ArrayLiteral(_, array) => array.children_mut(),
            Expression::BinaryOperation(_, binary_op) => binary_op.children_mut(),
            Expression::UnaryOperation(_, unary_op) => unary_op.children_mut(),
            Expression::IndexAccess(_, index_access) => index_access.children_mut(),
            Expression::FunctionCall(_, function_call) => function_call.children_mut(),
            Expression::FreeInput(_, e) => once(e.as_mut()),
            Expression::MatchExpression(_, match_expr) => match_expr.children_mut(),
            Expression::IfExpression(_, if_expr) => if_expr.children_mut(),
            Expression::BlockExpression(_, block_expr) => block_expr.children_mut(),
        }
    }

    /// Returns true if the expression contains a reference to a next value
    pub fn contains_next_ref(&self) -> bool {
        self.expr_any(|e| {
            matches!(
                e,
                Expression::UnaryOperation(
                    _,
                    UnaryOperation {
                        op: UnaryOperator::Next,
                        ..
                    }
                )
            )
        })
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Default, Clone)]
pub struct PolynomialName {
    pub name: String,
    pub array_size: Option<Expression>,
}

impl From<String> for PolynomialName {
    fn from(name: String) -> Self {
        Self {
            name,
            array_size: None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Default, Clone, PartialOrd, Ord)]
/// A polynomial with an optional namespace
/// This is different from SymbolPath mainly due to different formatting.
pub struct NamespacedPolynomialReference {
    pub path: SymbolPath,
    pub type_args: Option<Vec<Type<Expression>>>,
}

impl From<SymbolPath> for NamespacedPolynomialReference {
    fn from(value: SymbolPath) -> Self {
        Self {
            path: value,
            type_args: Default::default(),
        }
    }
}

impl NamespacedPolynomialReference {
    pub fn from_identifier(name: String) -> Self {
        SymbolPath::from_parts(vec![Part::Named(name)]).into()
    }

    pub fn try_to_identifier(&self) -> Option<&String> {
        if self.type_args.is_none() {
            self.path.try_to_identifier()
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema)]
pub struct LambdaExpression<E = Expression<NamespacedPolynomialReference>> {
    pub kind: FunctionKind,
    pub params: Vec<Pattern>,
    pub body: Box<E>,
    /// The IDs of the variables outside the functions that are referenced,
    /// i.e. the environment that is captured by the closure.
    /// This is filled in by the expression processor.
    #[schemars(skip)]
    pub outer_var_references: BTreeSet<u64>,
}

impl<Ref> From<LambdaExpression<Expression<Ref>>> for Expression<Ref> {
    fn from(lambda: LambdaExpression<Expression<Ref>>) -> Self {
        Expression::LambdaExpression(SourceRef::unknown(), lambda)
    }
}

impl<E> Children<E> for LambdaExpression<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(self.body.as_ref()))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(self.body.as_mut()))
    }
}

#[derive(
    Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
pub enum FunctionKind {
    Pure,
    Constr,
    Query,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema)]
pub struct ArrayLiteral<E = Expression<NamespacedPolynomialReference>> {
    pub items: Vec<E>,
}

impl<Ref> From<ArrayLiteral<Expression<Ref>>> for Expression<Ref> {
    fn from(array: ArrayLiteral<Expression<Ref>>) -> Self {
        Expression::ArrayLiteral(SourceRef::unknown(), array)
    }
}

impl<E> Children<E> for ArrayLiteral<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(self.items.iter())
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(self.items.iter_mut())
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize, JsonSchema,
)]
pub enum UnaryOperator {
    Minus,
    LogicalNot,
    Next,
}

impl UnaryOperator {
    /// Returns true if the operator is a prefix-operator and false if it is a postfix operator.
    pub fn is_prefix(&self) -> bool {
        match self {
            UnaryOperator::Minus | UnaryOperator::LogicalNot => true,
            UnaryOperator::Next => false,
        }
    }
}

#[derive(
    Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize, JsonSchema,
)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    BinaryAnd,
    BinaryXor,
    BinaryOr,
    ShiftLeft,
    ShiftRight,
    LogicalOr,
    LogicalAnd,
    Less,
    LessEqual,
    Equal,
    Identity,
    NotEqual,
    GreaterEqual,
    Greater,
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinaryOperatorAssociativity {
    Left,
    Right,
    RequireParentheses,
}

trait Precedence {
    fn precedence(&self) -> Option<ExpressionPrecedence>;
}

impl Precedence for UnaryOperator {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        use UnaryOperator::*;
        let precedence = match self {
            // NOTE: Any modification must be done with care to not overlap with BinaryOperator's precedence
            Next => 1,
            Minus | LogicalNot => 2,
        };

        Some(precedence)
    }
}

impl Precedence for BinaryOperator {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        use BinaryOperator::*;
        let precedence = match self {
            // NOTE: Any modification must be done with care to not overlap with LambdaExpression's precedence
            // Unary Oprators
            // **
            Pow => 3,
            // * / %
            Mul | Div | Mod => 4,
            // + -
            Add | Sub => 5,
            // << >>
            ShiftLeft | ShiftRight => 6,
            // &
            BinaryAnd => 7,
            // ^
            BinaryXor => 8,
            // |
            BinaryOr => 9,
            // = == != < > <= >=
            Identity | Equal | NotEqual | Less | Greater | LessEqual | GreaterEqual => 10,
            // &&
            LogicalAnd => 11,
            // ||
            LogicalOr => 12,
            // .. ..=
            // ??
        };

        Some(precedence)
    }
}

impl<E> Precedence for Expression<E> {
    fn precedence(&self) -> Option<ExpressionPrecedence> {
        match self {
            Expression::UnaryOperation(_, operation) => operation.op.precedence(),
            Expression::BinaryOperation(_, operation) => operation.op.precedence(),
            _ => None,
        }
    }
}

impl BinaryOperator {
    pub fn associativity(&self) -> BinaryOperatorAssociativity {
        use BinaryOperator::*;
        use BinaryOperatorAssociativity::*;
        match self {
            Identity | Equal | NotEqual | Less | Greater | LessEqual | GreaterEqual => {
                RequireParentheses
            }
            Pow => Right,

            // .. ..= => RequireParentheses,
            _ => Left,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct IndexAccess<E = Expression<NamespacedPolynomialReference>> {
    pub array: Box<E>,
    pub index: Box<E>,
}

impl<Ref> From<IndexAccess<Expression<Ref>>> for Expression<Ref> {
    fn from(ia: IndexAccess<Expression<Ref>>) -> Self {
        Expression::IndexAccess(SourceRef::unknown(), ia)
    }
}

impl<E> Children<E> for IndexAccess<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(self.array.as_ref()).chain(once(self.index.as_ref())))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(self.array.as_mut()).chain(once(self.index.as_mut())))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct FunctionCall<E = Expression<NamespacedPolynomialReference>> {
    pub function: Box<E>,
    pub arguments: Vec<E>,
}

impl<Ref> From<FunctionCall<Expression<Ref>>> for Expression<Ref> {
    fn from(call: FunctionCall<Expression<Ref>>) -> Self {
        Expression::FunctionCall(SourceRef::unknown(), call)
    }
}

impl<E> Children<E> for FunctionCall<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(self.function.as_ref()).chain(self.arguments.iter()))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(self.function.as_mut()).chain(self.arguments.iter_mut()))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct MatchArm<E = Expression<NamespacedPolynomialReference>> {
    pub pattern: Pattern,
    pub value: E,
}

impl<E> Children<E> for MatchArm<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(once(&self.value))
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(once(&mut self.value))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct IfExpression<E = Expression<NamespacedPolynomialReference>> {
    pub condition: Box<E>,
    pub body: Box<E>,
    pub else_body: Box<E>,
}

impl<Ref> From<IfExpression<Expression<Ref>>> for Expression<Ref> {
    fn from(ifexpr: IfExpression<Expression<Ref>>) -> Self {
        Expression::IfExpression(SourceRef::unknown(), ifexpr)
    }
}

impl<E> Children<E> for IfExpression<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(
            once(&self.condition)
                .chain(once(&self.body))
                .chain(once(&self.else_body))
                .map(|e| e.as_ref()),
        )
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(
            once(&mut self.condition)
                .chain(once(&mut self.body))
                .chain(once(&mut self.else_body))
                .map(|e| e.as_mut()),
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub enum StatementInsideBlock<E = Expression<NamespacedPolynomialReference>> {
    LetStatement(LetStatementInsideBlock<E>),
    Expression(E),
}

impl<E> Children<E> for StatementInsideBlock<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        match self {
            StatementInsideBlock::LetStatement(l) => Box::new(l.children()),
            StatementInsideBlock::Expression(e) => Box::new(once(e)),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        match self {
            StatementInsideBlock::LetStatement(l) => Box::new(l.children_mut()),
            StatementInsideBlock::Expression(e) => Box::new(once(e)),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct LetStatementInsideBlock<E = Expression<NamespacedPolynomialReference>> {
    pub pattern: Pattern,
    pub ty: Option<Type<u64>>,
    pub value: Option<E>,
}

impl<E> Children<E> for LetStatementInsideBlock<E> {
    fn children(&self) -> Box<dyn Iterator<Item = &E> + '_> {
        Box::new(self.value.iter())
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut E> + '_> {
        Box::new(self.value.iter_mut())
    }
}

/// The definition of a function (excluding its name):
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum FunctionDefinition {
    /// Array expression.
    Array(ArrayExpression),
    /// Generic expression
    Expression(Expression),
    /// A type declaration.
    TypeDeclaration(EnumDeclaration<Expression>),
    /// A trait declaration.
    TraitDeclaration(TraitDeclaration<Expression>),
}

impl Children<Expression> for FunctionDefinition {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression> + '_> {
        match self {
            FunctionDefinition::Array(ae) => ae.children(),
            FunctionDefinition::Expression(e) => Box::new(once(e)),
            FunctionDefinition::TypeDeclaration(_enum_declaration) => todo!(),
            FunctionDefinition::TraitDeclaration(trait_declaration) => trait_declaration.children(),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression> + '_> {
        match self {
            FunctionDefinition::Array(ae) => ae.children_mut(),
            FunctionDefinition::Expression(e) => Box::new(once(e)),
            FunctionDefinition::TypeDeclaration(_enum_declaration) => todo!(),
            FunctionDefinition::TraitDeclaration(trait_declaration) => {
                trait_declaration.children_mut()
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub enum ArrayExpression<Ref = NamespacedPolynomialReference> {
    Value(Vec<Expression<Ref>>),
    RepeatedValue(Vec<Expression<Ref>>),
    Concat(Box<ArrayExpression<Ref>>, Box<ArrayExpression<Ref>>),
}

impl ArrayExpression {
    pub fn value(v: Vec<Expression>) -> Self {
        Self::Value(v)
    }

    pub fn repeated_value(v: Vec<Expression>) -> Self {
        Self::RepeatedValue(v)
    }

    pub fn concat(self, other: Self) -> Self {
        Self::Concat(Box::new(self), Box::new(other))
    }

    fn pad_with(self, pad: Expression) -> Self {
        Self::concat(self, Self::repeated_value(vec![pad]))
    }

    pub fn pad_with_zeroes(self) -> Self {
        self.pad_with(0u32.into())
    }

    fn last(&self) -> Option<&Expression> {
        match self {
            ArrayExpression::Value(v) => v.last(),
            ArrayExpression::RepeatedValue(v) => v.last(),
            ArrayExpression::Concat(_, right) => right.last(),
        }
    }

    // return None if `self` is empty
    pub fn pad_with_last(self) -> Option<Self> {
        self.last().cloned().map(|last| self.pad_with(last))
    }
}

impl<Ref> ArrayExpression<Ref> {
    /// solve for `*`
    fn solve(&self, degree: DegreeType) -> DegreeType {
        assert!(
            self.number_of_repetitions() <= 1,
            "`*` can be used only once in rhs of array definition"
        );
        let len = self.constant_length();
        assert!(
            len <= degree,
            "Array literal is too large ({len}) for degree ({degree})."
        );
        // Fill up the remaining space with the repeated array
        degree - len
    }

    /// The number of times the `*` operator is used
    fn number_of_repetitions(&self) -> usize {
        match self {
            ArrayExpression::RepeatedValue(_) => 1,
            ArrayExpression::Value(_) => 0,
            ArrayExpression::Concat(left, right) => {
                left.number_of_repetitions() + right.number_of_repetitions()
            }
        }
    }

    /// The combined length of the constant-size parts of the array expression.
    fn constant_length(&self) -> DegreeType {
        match self {
            ArrayExpression::RepeatedValue(_) => 0,
            ArrayExpression::Value(e) => e.len() as DegreeType,
            ArrayExpression::Concat(left, right) => {
                left.constant_length() + right.constant_length()
            }
        }
    }
}

/// An array of elements that might be repeated.
pub struct RepeatedArray<'a> {
    /// The pattern to be repeated
    pattern: &'a [Expression<Reference>],
    /// The number of values to be filled by repeating the pattern, possibly truncating it at the end
    size: DegreeType,
}

impl<'a> RepeatedArray<'a> {
    pub fn new(pattern: &'a [Expression<Reference>], size: DegreeType) -> Self {
        if pattern.is_empty() {
            assert!(
                size == 0,
                "impossible to fill {size} values with an empty pattern"
            )
        }
        Self { pattern, size }
    }

    /// Returns the number of elements in this array (including repetitions).
    pub fn size(&self) -> DegreeType {
        self.size
    }

    /// Returns the pattern to be repeated
    pub fn pattern(&self) -> &'a [Expression<Reference>] {
        self.pattern
    }
}

impl ArrayExpression<Reference> {
    pub fn to_repeated_arrays<'a>(
        &'a self,
        degree: DegreeType,
    ) -> Box<dyn Iterator<Item = RepeatedArray<'a>> + 'a> {
        let size_of_repeated_part = self.solve(degree);
        self.to_repeated_arrays_rec(size_of_repeated_part)
    }

    fn to_repeated_arrays_rec<'a>(
        &'a self,
        size_of_repeated_part: DegreeType,
    ) -> Box<dyn Iterator<Item = RepeatedArray<'a>> + 'a> {
        match self {
            ArrayExpression::Value(pattern) => {
                Box::new(once(RepeatedArray::new(pattern, pattern.len() as u64)))
            }
            ArrayExpression::RepeatedValue(pattern) => {
                Box::new(once(RepeatedArray::new(pattern, size_of_repeated_part)))
            }
            ArrayExpression::Concat(left, right) => Box::new(
                left.to_repeated_arrays_rec(size_of_repeated_part)
                    .chain(right.to_repeated_arrays_rec(size_of_repeated_part)),
            ),
        }
    }
}

impl<Ref> Children<Expression<Ref>> for ArrayExpression<Ref> {
    fn children(&self) -> Box<dyn Iterator<Item = &Expression<Ref>> + '_> {
        match self {
            ArrayExpression::Value(v) | ArrayExpression::RepeatedValue(v) => Box::new(v.iter()),
            ArrayExpression::Concat(left, right) => {
                Box::new(left.children().chain(right.children()))
            }
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Expression<Ref>> + '_> {
        match self {
            ArrayExpression::Value(v) | ArrayExpression::RepeatedValue(v) => Box::new(v.iter_mut()),
            ArrayExpression::Concat(left, right) => {
                Box::new(left.children_mut().chain(right.children_mut()))
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub enum Pattern {
    CatchAll(SourceRef), // "_", matches a single value
    Ellipsis(SourceRef), // "..", matches a series of values, only valid inside array patterns
    #[schemars(skip)]
    Number(SourceRef, BigInt),
    String(SourceRef, String),
    Tuple(SourceRef, Vec<Pattern>),
    Array(SourceRef, Vec<Pattern>),
    // A pattern that binds a variable. Variable references are parsed as
    // Enum and are then re-mapped to Variable if they do not reference
    // an enum variant.
    Variable(SourceRef, String),
    Enum(SourceRef, SymbolPath, Option<Vec<Pattern>>),
}

impl Pattern {
    /// Returns an iterator over all variables in this pattern.
    pub fn variables(&self) -> Box<dyn Iterator<Item = &String> + '_> {
        match self {
            Pattern::Variable(_, v) => Box::new(once(v)),
            _ => Box::new(self.children().flat_map(|p| p.variables())),
        }
    }

    /// Return true if the pattern is irrefutable, i.e. matches all possible values of its type.
    pub fn is_irrefutable(&self) -> bool {
        match self {
            Pattern::Ellipsis(_) => unreachable!(),
            Pattern::CatchAll(_) | Pattern::Variable(_, _) => true,
            Pattern::Number(_, _) | Pattern::String(_, _) | Pattern::Enum(_, _, _) => false,
            Pattern::Array(_, items) => {
                // Only "[..]"" is irrefutable
                matches!(&items[..], [Pattern::Ellipsis(_)])
            }
            Pattern::Tuple(_, p) => p.iter().all(|p| p.is_irrefutable()),
        }
    }
}

impl Children<Pattern> for Pattern {
    fn children(&self) -> Box<dyn Iterator<Item = &Pattern> + '_> {
        match self {
            Pattern::CatchAll(_)
            | Pattern::Ellipsis(_)
            | Pattern::Number(_, _)
            | Pattern::String(_, _)
            | Pattern::Variable(_, _) => Box::new(empty()),
            Pattern::Tuple(_, p) | Pattern::Array(_, p) => Box::new(p.iter()),
            Pattern::Enum(_, _, fields) => Box::new(fields.iter().flatten()),
        }
    }

    fn children_mut(&mut self) -> Box<dyn Iterator<Item = &mut Pattern> + '_> {
        match self {
            Pattern::CatchAll(_)
            | Pattern::Ellipsis(_)
            | Pattern::Number(_, _)
            | Pattern::String(_, _)
            | Pattern::Variable(_, _) => Box::new(empty()),
            Pattern::Tuple(_, p) | Pattern::Array(_, p) => Box::new(p.iter_mut()),
            Pattern::Enum(_, _, fields) => Box::new(fields.iter_mut().flatten()),
        }
    }
}

impl SourceReference for Pattern {
    fn source_reference(&self) -> &SourceRef {
        match self {
            Pattern::CatchAll(s)
            | Pattern::Ellipsis(s)
            | Pattern::Number(s, _)
            | Pattern::String(s, _)
            | Pattern::Variable(s, _)
            | Pattern::Tuple(s, _)
            | Pattern::Array(s, _)
            | Pattern::Enum(s, _, _) => s,
        }
    }
    fn source_reference_mut(&mut self) -> &mut SourceRef {
        match self {
            Pattern::CatchAll(s)
            | Pattern::Ellipsis(s)
            | Pattern::Number(s, _)
            | Pattern::String(s, _)
            | Pattern::Variable(s, _)
            | Pattern::Tuple(s, _)
            | Pattern::Array(s, _)
            | Pattern::Enum(s, _, _) => s,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternSpace {
    Any,
    Number(HashSet<BigInt>, bool), // todo just bool
    String(HashSet<String>, bool),
    Enum(HashSet<String>, BTreeMap<String, Vec<PatternSpace>>), // TODO hashset to string
    Tuple(Vec<PatternSpace>, bool),
    Array(Vec<PatternSpace>, bool),
    Empty,
}

impl PatternSpace {
    fn union(&self, pattern: &Pattern) -> Self {
        match (self, pattern) {
            (PatternSpace::Any, Pattern::CatchAll(_))
            | (PatternSpace::Any, Pattern::Variable(_, _)) => PatternSpace::Any,
            (PatternSpace::Any, _) => PatternSpace::Any.substract(pattern), // TODO this can be replaces for from
            (PatternSpace::Number(ns, _ext), Pattern::CatchAll(_))
            | (PatternSpace::Number(ns, _ext), Pattern::Variable(_, _)) => {
                PatternSpace::Number(ns.clone(), true)
            }
            (PatternSpace::String(ss, _ext), Pattern::CatchAll(_))
            | (PatternSpace::String(ss, _ext), Pattern::Variable(_, _)) => {
                PatternSpace::String(ss.clone(), true)
            }
            (PatternSpace::Tuple(ss, _ext), Pattern::CatchAll(_))
            | (PatternSpace::Tuple(ss, _ext), Pattern::Variable(_, _)) => {
                PatternSpace::Tuple(ss.clone(), true)
            }
            (PatternSpace::Array(ss, _ext), Pattern::CatchAll(_))
            | (PatternSpace::Array(ss, _ext), Pattern::Variable(_, _)) => {
                PatternSpace::Array(ss.clone(), true)
            }
            (PatternSpace::Number(ns, empty), Pattern::Number(_, n)) => {
                if *empty {
                    self.clone()
                } else {
                    PatternSpace::Number(
                        ns.union(&HashSet::from_iter(vec![n.clone()]))
                            .cloned()
                            .collect(),
                        false,
                    )
                }
            }
            (PatternSpace::String(ss, empty), Pattern::String(_, s)) => {
                if *empty {
                    self.clone()
                } else {
                    PatternSpace::String(
                        ss.union(&HashSet::from_iter(vec![s.clone()]))
                            .cloned()
                            .collect(),
                        false,
                    )
                }
            }
            (PatternSpace::Enum(es, vs), Pattern::Enum(_, e, v)) => {
                let mut new_es = es.clone();
                let mut cvs = vs.clone(); // &mut to avoid clones
                new_es.insert(e.to_string());
                //let variant = e.to_string().rsplit("::").next().unwrap().to_string();
                match (vs.contains_key(&e.to_string()), v) {
                    (true, Some(v)) => {
                        let mut new_vs = vs.get(&e.to_string()).unwrap().clone();
                        for (index, p) in v.iter().enumerate() {
                            let res = new_vs[index].union(p);
                            new_vs[index] = res;
                        }
                        cvs.insert(e.to_string(), new_vs);
                    }
                    (false, Some(v)) => {
                        let mut new_vs = Vec::new();
                        for p in v {
                            let res = PatternSpace::Empty.union(p);
                            new_vs.push(res);
                        }
                        cvs.insert(e.to_string(), new_vs);
                    }
                    (_, None) => {
                        cvs.insert(e.to_string(), vec![PatternSpace::Empty]);
                    }
                }

                PatternSpace::Enum(new_es, cvs)
            }
            (PatternSpace::Tuple(ps, empty), Pattern::Tuple(_, ps2)) => {
                if *empty {
                    self.clone()
                } else {
                    PatternSpace::Tuple(
                        ps.into_iter()
                            .zip(ps2.into_iter())
                            .map(|(p1, p2)| p1.union(&p2))
                            .collect(),
                        *empty,
                    )
                }
            }
            (PatternSpace::Array(ps, empty), Pattern::Array(_, ps2)) => {
                if *empty {
                    self.clone()
                } else {
                    PatternSpace::Array(
                        ps.into_iter()
                            .zip(ps2.into_iter())
                            .map(|(p1, p2)| p1.union(&p2))
                            .collect(),
                        *empty,
                    )
                }
            }
            (PatternSpace::Empty, _) => PatternSpace::Any.substract(pattern),
            _ => PatternSpace::Empty,
        }
    }

    fn substract(&self, pattern: &Pattern) -> PatternSpace {
        match (self, pattern) {
            (PatternSpace::Number(ns, _ext), Pattern::CatchAll(_))
            | (PatternSpace::Number(ns, _ext), Pattern::Variable(_, _)) => {
                PatternSpace::Number(ns.clone(), true)
            }
            (PatternSpace::String(ss, _ext), Pattern::CatchAll(_))
            | (PatternSpace::String(ss, _ext), Pattern::Variable(_, _)) => {
                PatternSpace::String(ss.clone(), true)
            }
            (_, Pattern::CatchAll(_)) | (_, Pattern::Variable(_, _)) => PatternSpace::Empty,
            (PatternSpace::Any, Pattern::Number(_, n)) => {
                PatternSpace::Number(HashSet::from_iter(vec![n.clone()]), false)
            }
            (PatternSpace::Any, Pattern::String(_, s)) => {
                PatternSpace::String(HashSet::from_iter(vec![s.clone()]), false)
            }
            (PatternSpace::Any, Pattern::Enum(_, e, v)) => match v {
                Some(vec) => {
                    let mut variants = BTreeMap::new();
                    let mut result = Vec::new();
                    for variant in vec {
                        let res = PatternSpace::Any.substract(variant);
                        result.push(res);
                    }
                    variants.insert(e.to_string(), result);
                    PatternSpace::Enum(HashSet::from_iter(vec![e.to_string()]), variants)
                }
                None => {
                    let mut variants = BTreeMap::new();
                    variants.insert(e.to_string(), vec![PatternSpace::Empty]);
                    PatternSpace::Enum(HashSet::from_iter(vec![e.to_string()]), variants)
                }
            },

            (PatternSpace::Any, Pattern::Tuple(_, items)) => PatternSpace::Tuple(
                items
                    .iter()
                    .map(|p| PatternSpace::Any.substract(p))
                    .collect(),
                false,
            ),
            (PatternSpace::Any, Pattern::Array(_, items)) => PatternSpace::Array(
                items
                    .iter()
                    .map(|p| PatternSpace::Any.substract(p))
                    .collect(),
                false,
            ),

            (PatternSpace::Number(ns, empty), Pattern::Number(_, n)) => PatternSpace::Number(
                HashSet::from_iter(ns.iter().cloned().chain(std::iter::once(n.clone()))),
                *empty,
            ),
            (PatternSpace::String(ss, empty), Pattern::String(_, s)) => PatternSpace::String(
                HashSet::from_iter(ss.iter().cloned().chain(std::iter::once(s.clone()))),
                *empty,
            ),
            (PatternSpace::Enum(es, vs), Pattern::Enum(_, e, v)) => {
                let name = e.to_string();
                let mut new_es = es.clone(); // I don't like you
                new_es.insert(name.clone());

                let new_vs = match v {
                    Some(vec) if es.contains(&name) => {
                        let mut new_vs = vs.clone();
                        let variants = new_vs.get_mut(&name).unwrap();
                        for (pattern, space) in vec.iter().zip(variants.iter_mut()) {
                            *space = space.substract(pattern);
                        }
                        new_vs
                    }
                    Some(vec) => {
                        let mut new_vs = vs.clone();
                        let mut variants = Vec::new();
                        for variant in vec {
                            let res = PatternSpace::Any.substract(variant);
                            variants.push(res);
                        }
                        new_vs.insert(name, variants);
                        new_vs
                    }
                    None => {
                        let mut new_vs = vs.clone();
                        new_vs.insert(name, vec![PatternSpace::Empty]);
                        new_vs
                    }
                };

                PatternSpace::Enum(new_es, new_vs)
            }
            (PatternSpace::Tuple(ts, empty), Pattern::Tuple(_, t)) => PatternSpace::Tuple(
                ts.iter()
                    .zip(t)
                    .map(|(space, pattern)| space.substract(pattern))
                    .collect(),
                *empty,
            ),
            (PatternSpace::Array(ars, empty), Pattern::Array(_, ar)) => PatternSpace::Array(
                ars.iter()
                    .zip(ar)
                    .map(|(space, pattern)| space.substract(pattern))
                    .collect(),
                *empty,
            ),
            (PatternSpace::Empty, _) => PatternSpace::Empty,
            _ => PatternSpace::Empty, // TODO error?
        }
    }

    fn is_empty(&self, enums: &HashMap<String, Vec<(String, bool)>>) -> bool {
        match self {
            PatternSpace::Any => false,
            PatternSpace::Number(_ns, empty) => *empty,
            PatternSpace::String(_ss, empty) => *empty,
            PatternSpace::Enum(es, vs) => {
                let e = es.iter().next().unwrap();
                let parts: Vec<&str> = e.split("::").collect();
                let enum_name = parts[..parts.len() - 1].join("::");
                let mut variants = vs.get(e).unwrap().clone();

                let mut unique_patterns = Vec::new();
                variants.retain(|item| {
                    if !unique_patterns.iter().any(|x| x == item) {
                        unique_patterns.push(item.clone());
                        true
                    } else {
                        false
                    }
                });

                let all_empty = variants.iter().all(|f| f.is_empty(enums));
                let all_covered = enums
                    .get(&enum_name)
                    .unwrap()
                    .iter()
                    .filter(|(_, b)| *b)
                    .collect::<Vec<_>>()
                    .len()
                    == variants.len();

                all_empty && all_covered
            }
            PatternSpace::Tuple(ts, empty) => *empty || ts.iter().all(|f| f.is_empty(enums)),
            PatternSpace::Array(ars, empty) => *empty || ars.iter().all(|f| f.is_empty(enums)),
            PatternSpace::Empty => true,
        }
    }
}

fn analyze_patterns(
    patterns: &[Pattern],
    enums: &HashMap<String, Vec<(String, bool)>>,
) -> (bool, Vec<usize>, usize) {
    let mut remaining_space = PatternSpace::Any;
    let mut useless_indices = Vec::new();

    //let empty: bool = space.is_empty(enums);
    for (index, p) in patterns.iter().enumerate() {
        if remaining_space.is_empty(enums) {
            useless_indices.push(index);
        } else {
            println!();
            println!("_________________________________________");
            println!("ACA: old space {:?}", remaining_space);
            println!("ACA: pattern {:?}", p);
            let mut new_space = remaining_space.union(p);
            // if let Pattern::CatchAll(_) = p {
            //     new_space = PatternSpace::Empty;
            // }
            println!();
            println!("ACA: {:?}", new_space);
            println!("_________________________________________");
            println!();
            if new_space == remaining_space {
                useless_indices.push(index);
            }

            remaining_space = new_space;
        }
    }

    (remaining_space.is_empty(enums), useless_indices, 0)
}

pub fn analyze_match_patterns(
    patterns: &[Pattern],
    enums: HashMap<String, Vec<(String, bool)>>,
) -> MatchAnalysisReport {
    let (is_exhaustive, redundant_indices, _remaining_space) = analyze_patterns(patterns, &enums);

    MatchAnalysisReport {
        is_exhaustive,
        redundant_patterns: redundant_indices,
    }
}

#[derive(Debug)]
pub struct MatchAnalysisReport {
    pub is_exhaustive: bool,
    pub redundant_patterns: Vec<usize>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize, JsonSchema)]
pub struct TypedExpression<Ref = NamespacedPolynomialReference, E = Expression<Ref>> {
    pub e: Expression<Ref>,
    pub type_scheme: Option<TypeScheme<E>>,
}

#[cfg(test)]
mod tests {

    use std::vec;

    use super::*;

    #[test]
    fn test_basic_usefullness() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "B".to_string()),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_basic_usefullness_repeated() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "A".to_string()),
        ];

        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns, vec![1, 2]);
    }

    #[test]
    fn test_usefullness_new_catchall() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "B".to_string()),
            Pattern::String(SourceRef::unknown(), "B".to_string()),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns, vec![2]);
    }

    #[test]
    fn test_usefullness_already_exhaustive_patterns() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::CatchAll(SourceRef::unknown()),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, true);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_usefullness_extra_catchall() {
        let patterns = vec![
            Pattern::String(SourceRef::unknown(), "A".to_string()),
            Pattern::CatchAll(SourceRef::unknown()),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, true);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_catchall_in_array() {
        let patterns = vec![
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ],
            ),
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 3.into()),
                ],
            ),
            Pattern::CatchAll(SourceRef::unknown()),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, true);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_catchall_in_tuple() {
        let patterns = vec![
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::CatchAll(SourceRef::unknown()),
                    Pattern::CatchAll(SourceRef::unknown()),
                ],
            ),
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, true);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_usefullness_ellipsis_in_arms() {
        let patterns = vec![
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                    Pattern::Number(SourceRef::unknown(), 3.into()),
                    Pattern::Number(SourceRef::unknown(), 4.into()),
                ],
            ),
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Ellipsis(SourceRef::unknown()),
                    Pattern::Number(SourceRef::unknown(), 4.into()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_ellipsis_new_pattern() {
        let patterns = vec![
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::CatchAll(SourceRef::unknown()),
                ],
            ),
            Pattern::Array(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_usefullness_tuples() {
        let patterns = vec![
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                    Pattern::Number(SourceRef::unknown(), 3.into()),
                    Pattern::Number(SourceRef::unknown(), 4.into()),
                ],
            ),
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 9.into()),
                    Pattern::Number(SourceRef::unknown(), 8.into()),
                    Pattern::Number(SourceRef::unknown(), 7.into()),
                    Pattern::Number(SourceRef::unknown(), 6.into()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_tuples_catchall() {
        let patterns = vec![
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                    Pattern::Number(SourceRef::unknown(), 3.into()),
                    Pattern::Number(SourceRef::unknown(), 4.into()),
                ],
            ),
            Pattern::Tuple(
                SourceRef::unknown(),
                vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                    Pattern::CatchAll(SourceRef::unknown()),
                    Pattern::Number(SourceRef::unknown(), 4.into()),
                ],
            ),
        ];
        let enums = HashMap::new();
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_enums() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("A".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("B".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
        ];
        let mut enums = HashMap::new();
        enums.insert(
            "A".to_string(),
            vec![("A".to_string(), true), ("B".to_string(), true)],
        );
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_enums_catchall() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("B".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
            Pattern::CatchAll(SourceRef::unknown()),
        ];
        let mut enums = HashMap::new();
        enums.insert(
            "A".to_string(),
            vec![("A".to_string(), false), ("B".to_string(), true)],
        );
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, true);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_enums_none_exhaustive() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("A".to_string()),
                ]),
                None,
            ),
            Pattern::CatchAll(SourceRef::unknown()),
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("B".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
        ];

        let mut enums = HashMap::new();
        enums.insert(
            "A".to_string(),
            vec![("A".to_string(), true), ("B".to_string(), true)],
        );
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, true);
        assert_eq!(report.redundant_patterns, vec![2]);
    }

    #[test]
    fn test_usefullness_enums_none() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("A".to_string()),
                ]),
                None,
            ),
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("B".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
        ];
        let mut enums = HashMap::new();
        enums.insert(
            "A".to_string(),
            vec![("A".to_string(), true), ("B".to_string(), true)],
        );
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_enums_symbolpath() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("A".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 2.into()),
                ]),
            ),
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("A".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 3.into()),
                ]),
            ),
        ];
        let mut enums = HashMap::new();
        enums.insert("A".to_string(), vec![("A".to_string(), true)]);
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }

    #[test]
    fn test_usefullness_enums_symbolpath_catchall() {
        let patterns = vec![
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("A".to_string()),
                ]),
                Some(vec![
                    Pattern::CatchAll(SourceRef::unknown()),
                    Pattern::CatchAll(SourceRef::unknown()),
                ]),
            ),
            Pattern::Enum(
                SourceRef::unknown(),
                SymbolPath::from_parts(vec![
                    Part::Named("A".to_string()),
                    Part::Named("A".to_string()),
                ]),
                Some(vec![
                    Pattern::Number(SourceRef::unknown(), 1.into()),
                    Pattern::Number(SourceRef::unknown(), 3.into()),
                ]),
            ),
        ];
        let mut enums = HashMap::new();
        enums.insert("A".to_string(), vec![("A".to_string(), true)]);
        let report = analyze_match_patterns(&patterns, enums);
        assert_eq!(report.is_exhaustive, true);
        assert_eq!(report.redundant_patterns, vec![1]);
    }

    #[test]
    fn test_usefullness_tuples_and_enums() {
        let elem1 = Pattern::Tuple(
            SourceRef::unknown(),
            vec![
                Pattern::CatchAll(SourceRef::unknown()),
                Pattern::Enum(
                    SourceRef::unknown(),
                    SymbolPath::from_parts(vec![
                        Part::Named("Option".to_string()),
                        Part::Named("None".to_string()),
                    ]),
                    None,
                ),
            ],
        );
        let elem2 = Pattern::CatchAll(SourceRef::unknown());
        let arm1 = Pattern::Tuple(SourceRef::unknown(), vec![elem1, elem2]);

        let elem1 = Pattern::CatchAll(SourceRef::unknown());
        let elem2 = Pattern::Tuple(
            SourceRef::unknown(),
            vec![
                Pattern::CatchAll(SourceRef::unknown()),
                Pattern::Enum(
                    SourceRef::unknown(),
                    SymbolPath::from_parts(vec![
                        Part::Named("Option".to_string()),
                        Part::Named("None".to_string()),
                    ]),
                    None,
                ),
            ],
        );
        let arm2 = Pattern::Tuple(SourceRef::unknown(), vec![elem1, elem2]);

        let elem1 = Pattern::Tuple(
            SourceRef::unknown(),
            vec![
                Pattern::Variable(SourceRef::unknown(), "l_short".to_string()),
                Pattern::Enum(
                    SourceRef::unknown(),
                    SymbolPath::from_parts(vec![
                        Part::Named("Option".to_string()),
                        Part::Named("Some".to_string()),
                    ]),
                    Some(vec![Pattern::Variable(
                        SourceRef::unknown(),
                        "l_last".to_string(),
                    )]),
                ),
            ],
        );
        let elem2 = Pattern::Tuple(
            SourceRef::unknown(),
            vec![
                Pattern::Variable(SourceRef::unknown(), "r_short".to_string()),
                Pattern::Enum(
                    SourceRef::unknown(),
                    SymbolPath::from_parts(vec![
                        Part::Named("Option".to_string()),
                        Part::Named("Some".to_string()),
                    ]),
                    Some(vec![Pattern::Variable(
                        SourceRef::unknown(),
                        "r_last".to_string(),
                    )]),
                ),
            ],
        );
        let arm3 = Pattern::Tuple(SourceRef::unknown(), vec![elem1, elem2]);

        let patterns = vec![arm1, arm2, arm3];
        let mut enums = HashMap::new();
        enums.insert(
            "Option".to_string(),
            vec![("None".to_string(), true), ("Some".to_string(), true)],
        );
        let report = analyze_match_patterns(&patterns, enums);
        println!("{:?}", report);
        assert_eq!(report.is_exhaustive, false);
        assert_eq!(report.redundant_patterns.is_empty(), true);
    }
}
