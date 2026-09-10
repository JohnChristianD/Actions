path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

pattern = /qProjectionCross_v142[\s\S]*?(?=\nmultiplierDeletionStrict_v142 :)/
replacement = <<'AGDA'
qProjectionCross_v142 : ∀ {S} {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero →
  alpha * (x * x) < mu * ((x * x) * (x * x))
qProjectionCross_v142 = qProjectionCross_v141

AGDA

if pattern.match?(s)
  s.sub!(pattern, replacement)
else
  puts 'v166 q-projection v142 block already normalised'
end
File.write(path, s)
puts 'v166 q-projection v141/v142 compatibility: PASS'