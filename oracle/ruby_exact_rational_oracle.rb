# Exact finite ordered oracle.
# Native Ruby Rational arithmetic; local-only oracle, never a CI job.

oracle = ->(alpha, mu, x) do
  residual = alpha - mu * x * x
  cross_gap = mu * ((x * x) * (x * x)) - alpha * (x * x)
  [residual < 0, cross_gap > 0]
end

cases = [
  [Rational(1, 2), Rational(3), Rational(1)],
  [Rational(1, 3), Rational(5, 2), Rational(-2)],
  [Rational(2), Rational(9), Rational(1, 2)]
].map { |a, m, x| oracle.call(a, m, x) }

abort 'Ruby exact Rational oracle failure' unless cases.all? { |negative, cross| negative && cross }

puts 'Ruby exact Rational oracle: PASS'
