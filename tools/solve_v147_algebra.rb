# frozen_string_literal: true
require 'json'
require 'open3'

ROOT = File.expand_path('..', __dir__)
manifest = JSON.parse(File.read(File.join(ROOT, 'tools', 'algebraic_obligations.json')))
%w[bridges theorems conjectures].each { |k| abort "empty #{k}" if manifest.fetch(k).empty? }
puts "closure-bridges=#{manifest.fetch('bridges').length}"
puts "closure-theorems=#{manifest.fetch('theorems').length}"
puts "closure-conjectures=#{manifest.fetch('conjectures').length}"

run = lambda do |label, *cmd|
  stdout, stderr, status = Open3.capture3(*cmd)
  warn stderr unless stderr.empty?
  abort("#{label} failed") unless status.success?
  puts stdout unless stdout.empty?
end

# Ruby is orchestration only; no Ruby/Rails mathematical oracle remains.
swift = File.join(ROOT, 'oracles', 'QClosurePredictive_v147.swift')
swift_bin = File.join(ROOT, 'oracles', 'qclosure-swift')
run.call('swift-compile', 'swiftc', '-warnings-as-errors', '-O', swift, '-o', swift_bin)
run.call('swift-oracle', swift_bin)
run.call('haskell-oracle', 'runhaskell', File.join(ROOT, 'oracles', 'QClosurePredictive_v147.hs'))

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

puts 'closure-all-bridges-bounded=PASS'
puts 'closure-all-algebraic-theorems-bounded=PASS'
puts 'closure-all-algebraic-conjectures-bounded-falsification=PASS'
puts 'independent-language-oracles=8'
