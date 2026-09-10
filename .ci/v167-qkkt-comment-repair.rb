path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

pattern = /-- qProjectionFixedPoint_v147 : ∀ \{S n\}\n(  \(D : QProjectionDecisionAlgebra_v140 S\)[\s\S]*?  QRun_v142\.projection \(qRun_v142 D budget p x\) ≡ p\nqProjectionFixedPoint_v147 = qProjectionRetraction_v147)/
replacement = <<'AGDA'
qProjectionFixedPoint_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (p x : VecS S n) →
  (∀ i → zero ≤ indexV p i) →
  weightedExposure_v147 p x ≤ budget →
  QRun_v142.projection (qRun_v142 D budget p x) ≡ p
qProjectionFixedPoint_v147 = qProjectionRetraction_v147
AGDA

abort 'commented qProjectionFixedPoint declaration not found' unless pattern.match?(s)
s.sub!(pattern, replacement)
File.write(path, s)
puts 'v167 q-projection fixed-point declaration: PASS'