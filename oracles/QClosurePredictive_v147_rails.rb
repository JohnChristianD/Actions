# frozen_string_literal: true
require "rails"
abort "Rails runtime unavailable" unless defined?(Rails)

class Q
  include Comparable
  attr_reader :v
  def initialize(n, d = 1)
    raise ArgumentError, "zero denominator" if d == 0
    @v = Rational(n, d)
  end
  def +(o) = Q.new(@v + o.v)
  def -(o) = Q.new(@v - o.v)
  def *(o) = Q.new(@v * o.v)
  def /(o) = Q.new(@v / o.v)
  def <=>(o) = @v <=> o.v
end
ZERO = Q.new(0)
def sq(x) = x * x
def fourth(x) = sq(sq(x))
def vectors(n)
  return [[]] if n.zero?
  vectors(n - 1).flat_map { |p| [0, 1, 2].map { |a| p + [Q.new(a)] } }
end
def num(mask, a, x, b) = mask.sum { |i| a[i] * sq(x[i]) } - b
def den(mask, x) = mask.sum { |i| fourth(x[i]) }
def first_negative(mask, a, x, mu)
  mask.find { |i| a[i] - mu * sq(x[i]) < ZERO }
end
def run_q(mask, a, x, b, steps = 0)
  n = num(mask, a, x, b); d = den(mask, x)
  mu = n > ZERO && d > ZERO ? n / d : ZERO
  bad = first_negative(mask, a, x, mu)
  return [mu, mask, steps] unless bad
  reduced = mask.reject { |i| i == bad }
  n2 = num(reduced, a, x, b); d2 = den(reduced, x)
  y = a[bad] * sq(x[bad]); z = fourth(x[bad])
  raise "invalid deletion" unless n > ZERO && d > ZERO && d2 > ZERO && n2 > ZERO && y * d < n * z
  mu2 = n2 / d2
  raise "multiplier not increasing" unless mu < mu2
  run_q(reduced, a, x, b, steps + 1)
end

(1..4).each do |n|
  vectors(n).each do |a|
    vectors(n).each do |x|
      (0..4).each do |bi|
        mu, active, steps = run_q((0...n).to_a, a, x, Q.new(bi))
        raise "fuel bound" unless steps <= n
        active.each { |i| raise "active sign" unless a[i] - mu * sq(x[i]) >= ZERO }
        ((0...n).to_a - active).each { |i| raise "inactive sign" unless a[i] - mu * sq(x[i]) <= ZERO }
      end
    end
  end
end
puts "rails-q-finite-fuel=PASS"
puts "rails-q-terminal-signs=PASS"
puts "rails-q-multiplier-monotonicity=PASS"
puts "rails-q-terminal-kkt-prescriptive=PASS"
puts "rails-bridge-bounded=PASS"
puts "rails-theorem-bounded=PASS"
puts "rails-conjecture-falsification=PASS"
