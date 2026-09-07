defmodule Oracle do
  def sig(z), do: 1.0 / (1.0 + :math.exp(-z))

  def lstm(x, h, c) do
    z = x + h
    f = sig(z); i = sig(z); o = sig(z); g = :math.tanh(z)
    c2 = f * c + i * g
    {o * :math.tanh(c2), c2}
  end

  def gru(x, h) do
    z = sig(x + h)
    r = sig(x + h)
    n = :math.tanh(x + r * h)
    (1.0 - z) * n + z * h
  end
end

for {x,h,c} <- [{0.2,-0.1,0.3},{1.0,0.2,-0.4},{-0.7,0.5,0.1}] do
  {lh,lc} = Oracle.lstm(x,h,c)
  gh = Oracle.gru(x,h)
  IO.puts(:io_lib.format("~.10f,~.10f,~.10f,~.10f,~.10f,~.10f", [x,h,c,lh,lc,gh]))
end
