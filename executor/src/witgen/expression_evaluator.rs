use std::marker::PhantomData;

use ast::parsed::{BinaryOperator, UnaryOperator};
use number::FieldElement;
use pil_analyzer::{Expression, PolynomialReference};

use super::{affine_expression::AffineResult, IncompleteCause};

pub trait SymbolicVariables<T> {
    /// Value of a polynomial (fixed or witness).
    fn value<'a>(&self, poly: &'a PolynomialReference) -> AffineResult<&'a PolynomialReference, T>;
}

pub struct ExpressionEvaluator<T, SV> {
    variables: SV,
    marker: PhantomData<T>,
}

impl<T, SV> ExpressionEvaluator<T, SV>
where
    SV: SymbolicVariables<T>,
    T: FieldElement,
{
    pub fn new(variables: SV) -> Self {
        Self {
            variables,
            marker: PhantomData,
        }
    }
    /// Tries to evaluate the expression to an expression affine in the witness polynomials,
    /// taking current values of polynomials into account.
    /// @returns an expression affine in the witness polynomials
    pub fn evaluate<'a>(
        &self,
        expr: &'a Expression<T>,
    ) -> AffineResult<&'a PolynomialReference, T> {
        // @TODO if we iterate on processing the constraints in the same row,
        // we could store the simplified values.
        match expr {
            Expression::Constant(_) => panic!("Constants should have been replaced."),
            Expression::PolynomialReference(poly) => self.variables.value(poly),
            Expression::Number(n) => Ok((*n).into()),
            Expression::BinaryOperation(left, op, right) => {
                self.evaluate_binary_operation(left, op, right)
            }
            Expression::UnaryOperation(op, expr) => self.evaluate_unary_operation(op, expr),
            e => Err(IncompleteCause::ExpressionEvaluationUnimplemented(
                e.to_string(),
            )),
        }
    }

    fn evaluate_binary_operation<'a>(
        &self,
        left: &'a Expression<T>,
        op: &BinaryOperator,
        right: &'a Expression<T>,
    ) -> AffineResult<&'a PolynomialReference, T> {
        match (self.evaluate(left), op, self.evaluate(right)) {
            // Special case for multiplication: It is enough for one to be known zero.
            (Ok(zero), BinaryOperator::Mul, _) | (_, BinaryOperator::Mul, Ok(zero))
                if zero.constant_value() == Some(0.into()) =>
            {
                Ok(zero)
            }
            (Ok(left), op, Ok(right)) => match op {
                BinaryOperator::Add => Ok(left + right),
                BinaryOperator::Sub => Ok(left - right),
                BinaryOperator::Mul => {
                    if let Some(f) = left.constant_value() {
                        Ok(right * f)
                    } else if let Some(f) = right.constant_value() {
                        Ok(left * f)
                    } else {
                        Err(IncompleteCause::QuadraticTerm)
                    }
                }
                BinaryOperator::Div => {
                    if let (Some(l), Some(r)) = (left.constant_value(), right.constant_value()) {
                        // TODO Maybe warn about division by zero here.
                        if l == 0.into() {
                            Ok(T::from(0).into())
                        } else {
                            // TODO We have to do division in the proper field.
                            Ok((l / r).into())
                        }
                    } else {
                        Err(IncompleteCause::DivisionTerm)
                    }
                }
                BinaryOperator::Pow => {
                    if let (Some(l), Some(r)) = (left.constant_value(), right.constant_value()) {
                        Ok(l.pow(r.to_integer()).into())
                    } else {
                        Err(IncompleteCause::ExponentiationTerm)
                    }
                }
                BinaryOperator::Mod
                | BinaryOperator::BinaryAnd
                | BinaryOperator::BinaryXor
                | BinaryOperator::BinaryOr
                | BinaryOperator::ShiftLeft
                | BinaryOperator::ShiftRight => {
                    if let (Some(left), Some(right)) =
                        (left.constant_value(), right.constant_value())
                    {
                        let result: T = match op {
                            BinaryOperator::Mod => left.integer_mod(right),
                            BinaryOperator::BinaryAnd => {
                                (left.to_integer() & right.to_integer()).into()
                            }
                            BinaryOperator::BinaryXor => {
                                (left.to_integer() ^ right.to_integer()).into()
                            }
                            BinaryOperator::BinaryOr => {
                                (left.to_integer() | right.to_integer()).into()
                            }
                            BinaryOperator::ShiftLeft => {
                                (left.to_integer() << right.to_degree()).into()
                            }
                            BinaryOperator::ShiftRight => {
                                (left.to_integer() >> right.to_degree()).into()
                            }
                            _ => panic!(),
                        };
                        Ok(result.into())
                    } else {
                        panic!()
                    }
                }
            },
            (Ok(_), _, Err(reason)) | (Err(reason), _, Ok(_)) => Err(reason),
            (Err(r1), _, Err(r2)) => Err(r1.combine(r2)),
        }
    }

    fn evaluate_unary_operation<'a>(
        &self,
        op: &UnaryOperator,
        expr: &'a Expression<T>,
    ) -> AffineResult<&'a PolynomialReference, T> {
        self.evaluate(expr).map(|v| match op {
            UnaryOperator::Plus => v,
            UnaryOperator::Minus => -v,
        })
    }
}
