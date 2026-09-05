defmodule QClosurePredictiveV147 do
  def positive(n), do: n

  def weighted(h, x), do: h * x

  def cap(0, _value), do: 0
  def cap(_budget, 0), do: 0
  def cap(budget, value), do: 1 + cap(budget - 1, value - 1)

  def project(budget, h, x), do: cap(budget, weighted(h, x))

  def oracle_identity(n), do: positive(n) == n
end

true = QClosurePredictiveV147.oracle_identity(7)
