# frozen_string_literal: true
require 'json'
require 'open3'

root = File.expand_path('..', __dir__)
manifest = JSON.parse(File.read(File.join(root, 'tools', 'algebraic_obligations.json')))
puts "manifest-obligations=#{manifest.fetch('obligations').length}"

run = lambda do |label, *cmd|
  stdout, stderr, status = Open3.capture3(*cmd)
  warn stderr unless stderr.empty?
  abort("#{label} failed") unless status.success?
  puts stdout unless stdout.empty?
end

run.call('ruby-oracle', 'ruby', File.join(root, 'oracles', 'QClosurePredictive_v147.rb'))

swift = File.join(root, 'oracles', 'QClosurePredictive_v147.swift')
swift_bin = File.join(root, 'oracles', 'qclosure-swift')
run.call('swift-compile', 'swiftc', '-warnings-as-errors', '-O', swift, '-o', swift_bin)
run.call('swift-oracle', swift_bin)

run.call('kotlin-compile', 'kotlinc', '-Werror', File.join(root, 'oracles', 'QClosurePredictive_v147.kt'), '-include-runtime', '-d', File.join(root, 'oracles', 'qclosure-kotlin.jar'))
run.call('kotlin-oracle', 'java', '-jar', File.join(root, 'oracles', 'qclosure-kotlin.jar'))

run.call('sympy-oracle', 'python3', File.join(root, 'tools', 'sympy_solver_v147.py'))

puts 'four-oracle-algebraic-gate=PASS'
