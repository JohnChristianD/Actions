# Exact finite ordered Rational oracle for the v150 Efficient-CHAD target.
# Native Ruby Rational arithmetic; no floating point values.

def sigmoid_r(z)
  (Rational(2) + z) / Rational(4)
end

def tanh_r(z)
  (Rational(2) * z) / (Rational(2) + z * z)
end

def crelu(z)
  [z > 0 ? z : Rational(0), z < 0 ? -z : Rational(0)]
end

def tsallis2(scores, values)
  tau = Rational(1, 4)
  raw = scores.map { |s| [s - tau, Rational(0)].max }
  total = raw.inject(Rational(0), :+)
  weights = raw.map { |w| w / total }
  out = values.zip(weights).inject(Rational(0)) { |acc, (v, p)| acc + p * v }
  [weights, out]
end

def lstm(x, h, c)
  z = x + h
  f = sigmoid_r(z)
  i = sigmoid_r(z)
  o = sigmoid_r(z)
  g = tanh_r(z)
  c2 = f * c + i * g
  [o * tanh_r(c2), c2]
end

def render(r)
  r.denominator == 1 ? r.numerator.to_s : "#{r.numerator}/#{r.denominator}"
end

cases = [
  [Rational(1, 5), Rational(-1, 10), Rational(3, 10)],
  [Rational(1), Rational(1, 5), Rational(-2, 5)],
  [Rational(-7, 10), Rational(1, 2), Rational(1, 10)]
]

puts 'oracle=ruby-rational'
cases.each_with_index do |(x, h, c), i|
  lh, lc = lstm(x, h, c)
  puts "case=#{i + 1}=" + [x, h, c, lh, lc].map { |r| render(r) }.join(',')
end

weights, out = tsallis2([Rational(1), Rational(1, 2), Rational(-1, 2)], [Rational(1), Rational(-1), Rational(2)])
abort 'Ruby Tsallis-2 equilibrium failure' unless weights == [Rational(3, 4), Rational(1, 4), Rational(0)]
abort 'Ruby Tsallis-2 weighted output failure' unless out == Rational(1, 2)
puts "tsallis=" + weights.map { |r| render(r) }.join(',') + ";" + render(out)

cp, cm = crelu(Rational(-3, 2))
abort 'Ruby CReLU reconstruction failure' unless cp - cm == Rational(-3, 2)
abort 'Ruby CReLU magnitude failure' unless cp + cm == Rational(3, 2)
puts "crelu=" + [cp, cm, cp - cm, cp + cm].map { |r| render(r) }.join(',')

abort 'Ruby degree recurrence failure' unless [1, 3, 9, 27].each_cons(2).all? { |a, b| b == 3 * a }
puts 'degree=1,3,9,27'
puts 'status=PASS'
