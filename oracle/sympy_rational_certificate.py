"""Exact symbolic certificate oracle using SymPy Rational values.

No floating-point arithmetic and no mutable proof state.
"""

import sympy as sp

alpha, mu, x = sp.symbols("alpha mu x")
residual = alpha - mu * x**2
cross_gap = mu * x**4 - alpha * x**2
factor_certificate = sp.expand(cross_gap - x**2 * (mu * x**2 - alpha))

CASES = (
    (sp.Rational(1, 2), sp.Rational(3), sp.Rational(1)),
    (sp.Rational(1, 3), sp.Rational(5, 2), sp.Rational(-2)),
    (sp.Rational(2), sp.Rational(9), sp.Rational(1, 2)),
)

assert factor_certificate == 0
assert all(
    (a - m * xv**2 < 0) and (m * xv**4 - a * xv**2 > 0)
    for a, m, xv in CASES
)

print("SymPy exact Rational certificates: PASS")
