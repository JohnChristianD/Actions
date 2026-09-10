cert = fn alpha, mu, x ->
  residual = alpha - mu * x * x
  cross_gap = mu * ((x * x) * (x * x)) - alpha * (x * x)
  {residual < 0, cross_gap > 0}
end

cases = [
  {Rational.new(1, 2), Rational.new(3, 1), Rational.new(1, 1)},
  {Rational.new(1, 3), Rational.new(5, 2), Rational.new(-2, 1)},
  {Rational.new(2, 1), Rational.new(9, 1), Rational.new(1, 2)}
]

unless Enum.all?(cases, fn {a, m, x} ->
  {negative, cross} = cert.(a, m, x)
  negative and cross
end) do
  raise "exact Rational certificate failure"
end

IO.puts("Elixir exact Rational q certificates: PASS")
