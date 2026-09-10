defmodule QR do
  def norm(n, d) when d < 0, do: norm(-n, -d)
  def norm(n, d) do
    g = Integer.gcd(abs(n), abs(d))
    {Kernel.div(n, g), Kernel.div(d, g)}
  end
  def add({a, b}, {c, d}), do: norm(a * d + c * b, b * d)
  def mul({a, b}, {c, d}), do: norm(a * c, b * d)
  def sub(a, b), do: add(a, {-elem(b, 0), elem(b, 1)})
  def neg({n, d}), do: {-n, d}
  def lt(a, b), do: (sub(b, a) |> elem(0)) > 0
  def text({n, d}), do: Integer.to_string(n) <> "/" <> Integer.to_string(d)
end

cert = fn alpha, mu, x ->
  x2 = QR.mul(x, x)
  residual = QR.sub(alpha, QR.mul(mu, x2))
  x4 = QR.mul(x2, x2)
  cross_gap = QR.sub(QR.mul(mu, x4), QR.mul(alpha, x2))
  {QR.lt(residual, {0, 1}), QR.lt({0, 1}, cross_gap)}
end

cases = [
  {{1, 2}, {3, 1}, {1, 1}},
  {{1, 3}, {5, 2}, {-2, 1}},
  {{2, 1}, {9, 1}, {1, 2}}
]

unless Enum.all?(cases, fn {a, m, x} ->
  {negative, cross} = cert.(a, m, x)
  negative and cross
end) do
  raise "exact Rational certificate failure"
end

IO.puts("Elixir exact Rational q certificates: PASS")
