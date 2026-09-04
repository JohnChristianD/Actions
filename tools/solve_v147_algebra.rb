# frozen_string_literal: true
require 'json'
require 'open3'

ROOT = File.expand_path('..', __dir__)
manifest = JSON.parse(File.read(File.join(ROOT, 'tools', 'algebraic_obligations.json')))
bridges = manifest.fetch('bridges')
theorems = manifest.fetch('theorems')
conjectures = manifest.fetch('conjectures')
raise 'empty closure class' if [bridges, theorems, conjectures].any?(&:empty?)
(bridges + theorems + conjectures).each do |item|
  raise "missing id: #{item.inspect}" unless item['id']
end
puts "closure-bridges=#{bridges.length}"
puts "closure-theorems=#{theorems.length}"
puts "closure-conjectures=#{conjectures.length}"

run = lambda do |label, *cmd|
  stdout, stderr, status = Open3.capture3(*cmd)
  warn stderr unless stderr.empty?
  abort("#{label} failed") unless status.success?
  puts stdout unless stdout.empty?
end

run.call('ruby-oracle', 'ruby', File.join(ROOT, 'oracles', 'QClosurePredictive_v147.rb'))

swift = File.join(ROOT, 'oracles', 'QClosurePredictive_v147.swift')
swift_bin = File.join(ROOT, 'oracles', 'qclosure-swift')
run.call('swift-compile', 'swiftc', '-warnings-as-errors', '-O', swift, '-o', swift_bin)
run.call('swift-oracle', swift_bin)

run.call('haskell-oracle', 'runhaskell', File.join(ROOT, 'oracles', 'QClosurePredictive_v147.hs'))

run.call('rails-bundle', 'bundle', 'check')
run.call('rails-oracle', 'bundle', 'exec', 'ruby', File.join(ROOT, 'oracles', 'QClosurePredictive_v147_rails.rb'))

scala_src = File.join(ROOT, 'oracles', 'QClosurePredictive_v147_scala.scala')
scala_out = File.join(ROOT, 'oracles', 'scala-out')
Dir.mkdir(scala_out) unless Dir.exist?(scala_out)
run.call('scala-compile', 'scalac', '-deprecation', '-unchecked', '-d', scala_out, scala_src)
run.call('scala-oracle', 'scala', '-cp', scala_out, 'QClosurePredictiveV147')

run.call('rust-compile', 'rustc', '--edition=2021', '-C', 'opt-level=2', '-D', 'warnings', File.join(ROOT, 'oracles', 'QClosurePredictive_v147.rs'), '-o', File.join(ROOT, 'oracles', 'qclosure-rust'))
run.call('rust-oracle', File.join(ROOT, 'oracles', 'qclosure-rust'))

run.call('elixir-oracle', 'elixir', File.join(ROOT, 'oracles', 'q_closure_predictive_v147.exs'))
run.call('r-oracle', 'Rscript', File.join(ROOT, 'oracles', 'QClosurePredictive_v147.R'))
run.call('clojure-oracle', 'clojure', File.join(ROOT, 'oracles', 'QClosurePredictive_v147.clj'))
run.call('sympy-oracle', 'python3', File.join(ROOT, 'tools', 'sympy_solver_v147.py'))

puts 'closure-all-bridges=PASS'
puts 'closure-all-algebraic-theorems=PASS'
puts 'closure-all-algebraic-conjectures-bounded=PASS'
puts 'ten-way-algebraic-gate=PASS'
