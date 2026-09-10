path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

exposure = /diagonalNewtonExposurePositive_v146 : ∀ \{S\} \(h : CoupledHyperParameters_v146 S\) →\n  zero < diagonalNewtonExposure_v146 h\ndiagonalNewtonExposurePositive_v146 h =[\s\S]*?(?=\ndiagonalNewtonRelativeBudget_v146 :)/
exposure_new = <<'AGDA'
diagonalNewtonExposurePositive_v146 : ∀ {S} (h : CoupledHyperParameters_v146 S) →
  zero < diagonalNewtonExposure_v146 h
diagonalNewtonExposurePositive_v146 h =
  transportLt_v142
    (sym (Ring.addComm
      (OrderedRing.ring (SmoothAlgebra.orderedRing _))
      (SmoothAlgebra.recip _ (traceProduct_v146 h))
      (Ring.one (OrderedRing.ring (SmoothAlgebra.orderedRing _)))))
    refl
    (OrderedRing.leLt
      (reciprocalNonnegative_v146
        (OrderedRing.mulPos
          (CoupledHyperParameters_v146.gammaPositive h)
          (CoupledHyperParameters_v146.lambdaPositive h)))
      (OrderedRing.addLtLeft
        (OrderedRing.zeroLtOne
          {orderedRing = SmoothAlgebra.orderedRing _})
        (SmoothAlgebra.recip _ (traceProduct_v146 h))))

AGDA

pareto = /[A-Za-z0-9_]+ : ∀ \{S\}[\s\S]*?paretoNewtonFrontierLaw_v146 h₂ hq₂[\s\S]*?in transportLt_v142 hleft hright hsub/
pareto_new = <<'AGDA'
diagonalNewtonParetoFrontierStep_v146 : ∀ {S}
  (h₁ h₂ : CoupledHyperParameters_v146 S) →
  CoupledHyperParameters_v146.q h₁ < CoupledHyperParameters_v146.q h₂ →
  one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (CoupledHyperParameters_v146.q h₂) <
  one + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (CoupledHyperParameters_v146.q h₁)
diagonalNewtonParetoFrontierStep_v146 h₁ h₂ hq =
  transportLt_v142
    (paretoNewtonFrontierLaw_v146 h₂ (CoupledHyperParameters_v146.q h₂))
    (paretoNewtonFrontierLaw_v146 h₁ (CoupledHyperParameters_v146.q h₁))
    (OrderedRing.addLtLeft
      (OrderedRing.negLt hq)
      (Ring.one (OrderedRing.ring (SmoothAlgebra.orderedRing _))))
AGDA

unless exposure.match?(s)
  abort 'exposure theorem block not found'
end
s.sub!(exposure, exposure_new)

unless pareto.match?(s)
  abort 'Pareto frontier proof block not found'
end
# Only replace the first local-let frontier proof containing these exact bindings.
s.sub!(pareto, pareto_new)
File.write(path, s)
puts 'v164 exposure/Pareto proof normalization: PASS'