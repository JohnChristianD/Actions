defmodule Q do
  def norm(n, d) when d < 0, do: norm(-n, -d)
  def norm(n, d) do
    g = Integer.gcd(abs(n), abs(d))
    {div(n, g), div(d, g)}
  end

  def add({a, b}, {c, d}), do: norm(a * d + c * b, b * d)
  def mul({a, b}, {c, d}), do: norm(a * c, b * d)
  def div({a, b}, {c, d}), do: norm(a * d, b * c)
  def from_int(n), do: {n, 1}
  def text({n, 1}), do: Integer.to_string(n)
  def text({n, d}), do: Integer.to_string(n) <> "/" <> Integer.to_string(d)
end

defmodule Oracle do
  def sigmoid_r(z), do: Q.div(Q.add(Q.from_int(2), z), Q.from_int(4))

  def tanh_r(z) do
    zz = Q.mul(z, z)
    num = Q.mul(Q.from_int(2), z)
    den = Q.add(Q.from_int(2), zz)
    Q.div(num, den)
  end

  def lstm(x, h, c) do
    z = Q.add(x, h)
    f = sigmoid_r(z)
    i = sigmoid_r(z)
    o = sigmoid_r(z)
    g = tanh_r(z)
    c2 = Q.add(Q.mul(f, c), Q.mul(i, g))
    {Q.mul(o, tanh_r(c2)), c2}
  end
end

q = fn n, d -> Q.norm(n, d) end
cases = [{q.(1, 5), q.(-1, 10), q.(3, 10)},
         {q.(1, 1), q.(1, 5), q.(-2, 5)},
         {q.(-7, 10), q.(1, 2), q.(1, 10)}]

for {x, h, c} <- cases do
  {lh, lc} = Oracle.lstm(x, h, c)
  IO.puts(Enum.join(Enum.map([{x, x}, {h, h}, {c, c}, {lh, lh}, {lc, lc}], fn {{n, d}, _} -> Q.text({n, d}) end), ","))
end
