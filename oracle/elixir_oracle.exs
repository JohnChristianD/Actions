defmodule Oracle do
  def sigmoid(z), do: 1.0 / (1.0 + :math.exp(-z))

  def lstm_step(x, h, c) do
    f = sigmoid(0.7 * x + 0.4 * h)
    i = sigmoid(0.3 * x - 0.2 * h)
    o = sigmoid(-0.1 * x + 0.5 * h)
    g = :math.tanh(0.6 * x + 0.1 * h)
    c1 = f * c + i * g
    o * :math.tanh(c1)
  end

  def emit(x, h, c) do
    :io.format("~.12f,~.12f,~.12f,~.12f~n", [x, h, c, lstm_step(x, h, c)])
  end
end

IO.puts("x,h,c,output")
Oracle.emit(0.2, -0.1, 0.3)
Oracle.emit(1.0, 0.2, -0.4)
Oracle.emit(-0.7, 0.5, 0.1)
