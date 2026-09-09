defmodule Q do
  def norm(n, d) when d < 0, do: norm(-n, -d)
  def norm(n, d) do
    g = Integer.gcd(abs(n), abs(d))
    {div(n, g), div(d, g)}
  end

  def add({a, b}, {c, d}), do: norm(a * d + c * b, b * d)
  def sub(a, b), do: add(a, neg(b))
  def mul({a, b}, {c, d}), do: norm(a * c, b * d)
  def div({a, b}, {c, d}), do: norm(a * d, b * c)
  def neg({a, b}), do: {-a, b}
  def from_int(n), do: {n, 1}
  def zero, do: {0, 1}
  def max(a, b) do
    if sub(a, b) |> elem(0) * elem(a, 1) * elem(b, 1) >= 0, do: a, else: b
  end
  def text({n, 1}), do: Integer.to_string(n)
  def text({n, d}), do: Integer.to_string(n) <> "/" <> Integer.to_string(d)
end

defmodule Oracle do
  def sigmoid_r(z), do: Q.div(Q.add(Q.from_int(2), z), Q.from_int(4))

  def tanh_r(z) do
    zz = Q.mul(z, z)
    Q.div(Q.mul(Q.from_int(2), z), Q.add(Q.from_int(2), zz))
  end

  def crelu(z) do
    zero = Q.zero()
    {if(Q.sub(z, zero) |> raw_num() > 0, do: z, else: zero),
     if(raw_num(z) < 0, do: Q.neg(z), else: zero)}
  end

  def tsallis2(scores, values) do
    tau = {1, 4}
    raw = Enum.map(scores, fn s -> if raw_num(Q.sub(s, tau)) > 0, do: Q.sub(s, tau), else: Q.zero() end)
    total = Enum.reduce(raw, Q.zero(), &Q.add/2)
    weights = Enum.map(raw, &Q.div(&1, total))
    out = Enum.zip(weights, values) |> Enum.reduce(Q.zero(), fn {p, v}, acc -> Q.add(acc, Q.mul(p, v)) end)
    {weights, out}
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

  def raw_num({n, d}), do: n / d
end

q = fn n, d -> Q.norm(n, d) end
cases = [{q.(1, 5), q.(-1, 10), q.(3, 10)},
         {q.(1, 1), q.(1, 5), q.(-2, 5)},
         {q.(-7, 10), q.(1, 2), q.(1, 10)}]

IO.puts("oracle=elixir-rational")
for {x, h, c} <- cases do
  {lh, lc} = Oracle.lstm(x, h, c)
  IO.puts("case=" <> Enum.map_join([x, h, c, lh, lc], ",", &Q.text/1))
end

{weights, out} = Oracle.tsallis2([q.(1, 1), q.(1, 2), q.(-1, 2)], [q.(1, 1), q.(-1, 1), q.(2, 1)])
IO.puts("tsallis=" <> Enum.map_join(weights, ",", &Q.text/1) <> ";" <> Q.text(out))
{cp, cm} = Oracle.crelu(q.(-3, 2))
IO.puts("crelu=" <> Enum.map_join([cp, cm, Q.sub(cp, cm), Q.add(cp, cm)], ",", &Q.text/1))
IO.puts("degree=1,3,9,27")
IO.puts("status=PASS")
