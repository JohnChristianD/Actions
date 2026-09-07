defmodule Oracle do
  def sigmoid(z), do: 1.0 / (1.0 + :math.exp(-z))

  def lstm(x, h, c) do
    z = x + h
    f = sigmoid(z)
    i = sigmoid(z)
    o = sigmoid(z)
    g = :math.tanh(z)
    c2 = f * c + i * g
    {o * :math.tanh(c2), c2}
  end
end

for {x, h, c} <- [{0.2,-0.1,0.3},{1.0,0.2,-0.4},{-0.7,0.5,0.1}] do
  {lh, lc} = Oracle.lstm(x, h, c)
  IO.puts(:io_lib.format("~.12f,~.12f,~.12f,~.12f,~.12f", [x,h,c,lh,lc]))
end
