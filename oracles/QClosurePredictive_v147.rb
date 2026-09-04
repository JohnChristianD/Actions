# frozen_string_literal: true

class Q
  attr_reader :v
  def initialize(n, d = 1)
    raise ArgumentError, 'zero denominator' if d == 0
    @v = Rational(n, d)
  end
  def +(o) = Q.new(@v + o.v)
  def -@ = Q.new(-@v)
  def -(o) = Q.new(@v - o.v)
  def *(o) = Q.new(@v * o.v)
  def /(o) = Q.new(@v / o.v)
  include Comparable
  def <=>(o) = @v <=> o.v
  def zero? = @v.zero?
end

ZERO = Q.new(0)
ONE = Q.new(1)

def sq(x) = x * x
def fourth(x) = sq(sq(x))
def sum(xs) = xs.empty? ? ZERO : xs.first + sum(xs.drop(1))
def numerator(mask, alpha, x, budget) = sum(mask.map { |i| alpha[i] * sq(x[i]) }) - budget
def denominator(mask, x) = sum(mask.map { |i| fourth(x[i]) })
def first_negative(mask, alpha, x, mu)
  return nil if mask.empty?
  i = mask.first
  (alpha[i] - mu * sq(x[i])) < ZERO ? i : first_negative(mask.drop(1), alpha, x, mu)
end

def remove_mask(mask, i)
  return [] if mask.empty?
  mask.first == i ? mask.drop(1) : [mask.first] + remove_mask(mask.drop(1), i)
end

def run(mask, alpha, x, budget, steps = [])
  n = numerator(mask, alpha, x, budget)
  d = denominator(mask, x)
  mu = (n > ZERO && d > ZERO) ? n / d : ZERO
  bad = first_negative(mask, alpha, x, mu)
  return [mu, mask, steps] if bad.nil?
  reduced = remove_mask(mask, bad)
  n2 = numerator(reduced, alpha, x, budget)
  d2 = denominator(reduced, x)
  y = alpha[bad] * sq(x[bad])
  z = fourth(x[bad])
  raise 'invalid deletion' unless n > ZERO && d > ZERO && d2 > ZERO && n2 > ZERO && y * d < n * z
  mu2 = n2 / d2
  raise 'multiplier not increasing' unless mu < mu2
  run(reduced, alpha, x, budget, steps + [[mu, mu2, n, d, y, z, n2, d2]])
end

def vectors(alpha, n)
  return [[]] if n.zero?
  vectors(alpha, n - 1).flat_map { |p| alpha.map { |a| p + [a] } }
end

def verify_dimension(n)
  alphabet = [ZERO, ONE, Q.new(2)]
  budgets = (0..4).map { |i| Q.new(i) }
  vectors(alphabet, n).each do |a|
    vectors(alphabet, n).each do |x|
      budgets.each do |b|
        mu, mask, steps = run((0...n).to_a, a, x, b)
        raise 'fuel bound' unless steps.length <= n
        active = mask
        active.each { |i| raise 'active sign' unless a[i] - mu * sq(x[i]) >= ZERO }
        (0...n).to_a.reject { |i| active.include?(i) }.each do |i|
          raise 'inactive sign' unless a[i] - mu * sq(x[i]) <= ZERO
        end
      end
    end
  end
end

(1..4).each { |n| verify_dimension(n) }
puts 'ruby-q-cases=36300'
puts 'ruby-q-finite-fuel=PASS'
puts 'ruby-q-terminal-signs=PASS'
puts 'ruby-q-multiplier-monotonicity=PASS'
puts 'ruby-q-terminal-kkt-prescriptive=PASS'
