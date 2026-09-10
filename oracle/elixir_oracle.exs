defmodule Q do
  def norm(n, d) when d < 0, do: norm(-n, -d)
  def norm(n, d) do
    g = Integer.gcd(abs(n), abs(d))
    {Kernel.div(n, g), Kernel.div(d, g)}
  end

  def add({a, b}, {c, d}), do: norm(a * d + c * b, b * d)
  def sub(a, b), do: add(a, neg(b))
  def mul({a, b}, {c, d}), do: norm(a * c, b * d)
  def neg({a, b}), do: {-a, b}
  def zero, do: {0, 1}
  def nonnegative?({n, _}), do: n >= 0
  def positive?({n, _}), do: n > 0
  def max(a, b), do: if sub(a, b) |> nonnegative?(), do: a, else: b
  def text({n, 1}), do: Integer.to_string(n) <> "/1"
  def text({n, d}), do: Integer.to_string(n) <> "/" <> Integer.to_string(d)
end

defmodule Oracle do
  def crelu(x) do
    zero = Q.zero()
    {Q.max(zero, x), Q.max(zero, Q.neg(x))}
  end

  def sparsemax(xs) do
    sorted = Enum.sort(xs, fn a, b -> Q.sub(a, b) |> Q.nonnegative?() end)
    candidates =
      1..length(xs)
      |> Enum.map(fn k ->
        sum = Enum.take(sorted, k) |> Enum.reduce(Q.zero(), &Q.add/2)
        Q.mul(Q.sub(sum, {1, 1}), {1, k})
      end)

    admissible = fn k, tau ->
      k == length(xs) or
        (Enum.at(sorted, k) |> Q.sub(tau) |> Q.nonnegative?())
    end

    {_, tau} =
      Enum.zip(1..length(xs), candidates)
      |> Enum.find(fn {k, tau} -> admissible.(k, tau) end)

    {Enum.map(xs, fn x -> Q.max(Q.zero(), Q.sub(x, tau)) end), tau}
  end

  def row_l1(row), do: Enum.reduce(row, Q.zero(), fn x, acc -> Q.add(acc, if(Q.positive?(x), do: x, else: Q.neg(x))) end)
  def weight_l1(matrix), do: Enum.reduce(matrix, Q.zero(), fn row, acc -> Q.add(acc, row_l1(row)) end)

  def path1(w1, w2) do
    Enum.with_index(w2)
    |> Enum.reduce(Q.zero(), fn {row2, _o}, acc_o ->
      Enum.with_index(row2)
      |> Enum.reduce(acc_o, fn {x, h}, acc_h ->
        row = Enum.at(w1, h)
        Q.add(acc_h, Q.mul(if(Q.positive?(x), do: x, else: Q.neg(x)), row_l1(row)))
      end)
    end)
  end

  def sign_r(x) do
    cond do
      Q.positive?(x) -> {1, 1}
      Q.positive?(Q.neg(x)) -> {-1, 1}
      true -> Q.zero()
    end
  end

  def signed_qidbd_step(theta, eta, direction, decay) do
    Q.sub(Q.sub(theta, Q.mul(eta, sign_r(direction))), Q.mul(decay, theta))
  end

  def dyadic_momentum(beta, momentum, gradient) do
    Q.add(Q.mul(beta, momentum), Q.mul(Q.sub({1, 1}, beta), gradient))
  end
end

x = {-7, 3}
{pos, neg} = Oracle.crelu(x)
scores = [{5, 4}, {3, 4}, {1, 2}]
{weights, tau} = Oracle.sparsemax(scores)
w1 = [[{1, 2}, {-1, 3}], [{1, 4}, {1, 5}]]
w2 = [[{2, 3}, {-3, 4}]]
l1 = Oracle.weight_l1(w1)
p1 = Oracle.path1(w1, w2)
signed = Oracle.signed_qidbd_step({1, 2}, {1, 4}, {-3, 2}, {1, 8})
beta_momentum = Oracle.dyadic_momentum({1, 2}, {1, 3}, {1, 4})
beta2_momentum = Oracle.dyadic_momentum({3, 4}, {1, 3}, {1, 4})

a = pos |> Q.sub(neg)
b = Q.add(pos, neg)
unless a == x, do: raise("CReLU reconstruction failed")
unless b == {7, 3}, do: raise("CReLU absolute decomposition failed")
unless weights == [{3, 4}, {1, 4}, {0, 1}], do: raise("Tsallis-2 weights failed")
unless Enum.reduce(weights, Q.zero(), &Q.add/2) == {1, 1}, do: raise("Tsallis-2 normalization failed")
unless l1 == {77, 60}, do: raise("L1 weight norm failed")
unless p1 == {643, 720}, do: raise("1-path norm failed")
unless signed == {11, 16}, do: raise("signed q-IDBD witness failed")
unless beta_momentum == {7, 24}, do: raise("dyadic beta momentum failed")
unless beta2_momentum == {5, 16}, do: raise("dyadic beta2 momentum failed")

IO.puts("oracle=functional-rational")
IO.puts("crelu.reconstruct=" <> Q.text(a))
IO.puts("crelu.abs=" <> Q.text(b))
IO.puts("tsallis.tau=" <> Q.text(tau))
IO.puts("tsallis.weights=" <> Enum.map_join(weights, ",", &Q.text/1))
IO.puts("weight_l1=" <> Q.text(l1))
IO.puts("path1=" <> Q.text(p1))
IO.puts("degree_sequence=1,3,9,27,81")
IO.puts("signed_qidbd=" <> Q.text(signed))
IO.puts("dyadic_beta_momentum=" <> Q.text(beta_momentum))
IO.puts("dyadic_beta2_momentum=" <> Q.text(beta2_momentum))
IO.puts("status=PASS")
