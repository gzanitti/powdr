enum Constraint {
    Identity(expr, expr),
    Plookup(expr, expr[], expr, expr[]),
    Permutation(expr, expr[], expr, expr[]),
    Connection(expr[], expr[])
}