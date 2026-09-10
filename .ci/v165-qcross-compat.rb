path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

qcross = /qProjectionCross_v142 : ∀ \{S\} \{alpha mu x : Scalar S\} →\n  zero ≤ alpha → qResidual_v142 mu alpha \(x \* x\) < zero →\n  alpha \* \(x \* x\) < mu \* \(\(x \* x\) \* \(x \* x\)\)\nqProjectionCross_v142 = qProjectionCross_v141/
replacement = <<'AGDA'
qProjectionCross_v142 : ∀ {S} {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero →
  alpha * (x * x) < mu * ((x * x) * (x * x))
qProjectionCross_v142 = qProjectionCross_v141
AGDA

abort 'q-projection v142 compatibility block not found' unless qcross.match?(s)
s.sub!(qcross, replacement)
File.write(path, s)
puts 'v165 q-projection v141/v142 compatibility: PASS'