path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

s.gsub!(/residualSquareNonzero_v140 : ∀ \{S\}\n/,
        "residualSquareNonzero_v140 : ∀ {S : SmoothAlgebra}\n")

s.gsub!(/  let hzero : alpha \+ Ring\.neg \(OrderedRing\.ring \(SmoothAlgebra\.orderedRing _\)\)\n        \(mu \* \(hx \* hx\)\) ≡ alpha =\n/m,
        "  let hzero =\n")

File.write(path, s)
abort 'residual carrier remained implicit' if s.match?(/residualSquareNonzero_v140 : ∀ \{S\}\n/)
abort 'residual hzero dependent annotation remained' if s.include?('let hzero : alpha +')
puts 'v151 residual normalization: PASS'
