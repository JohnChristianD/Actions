# Exact finite algebra certificate oracle.
# Native Ruby Rational arithmetic; no floating-point values and no mutation.

CERTIFICATE = ->(alpha, mu, x) do
  residual = alpha - mu * x * x
  cross_gap = mu * ((x * x) * (x * x)) - alpha * (x * x)
  [residual < 0, cross_gap > 0]
end

CASES = [
  [Rational(1, 2), Rational(3), Rational(1)],
  [Rational(1, 3), Rational(5, 2), Rational(-2)],
  [Rational(2), Rational(9), Rational(1, 2)]
].map { |a, m, x| CERTIFICATE.call(a, m, x) }

abort 'exact Rational certificate failure' unless CASES.all? { |negative, cross| negative && cross }

puts 'Ruby exact Rational certificates: PASS'
