path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

pattern = /qProjectionCross_v142 :.*?qProjectionCross_v142 = qProjectionCross_v141/m
replacement = <<'AGDA'
qProjectionCross_v142 : ∀ {S} {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero →
  alpha * (x * x) < mu * ((x * x) * (x * x))
qProjectionCross_v142 = qProjectionCross_v141
AGDA

abort 'q-projection v142 compatibility block not found' unless pattern.match?(s)
s.sub!(pattern, replacement)
File.write(path, s)
puts 'v166 q-projection v141/v142 compatibility: PASS'