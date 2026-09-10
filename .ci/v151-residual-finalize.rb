path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

old = /residualSquareNonzero_v140 : ∀ \{S\}\n[\s\S]*?------------------------------------------------------------------------\n-- The clean, reusable cross-multiplication theorem/
new = <<'AGDA'
residualSquareNonzero_v140 : ∀ {S : SmoothAlgebra}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero → x ≠ zero
residualSquareNonzero_v140 ha hr refl =
  let rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      hxx = Ring.zeroMulR rg zero
      hmul = cong (λ q → mu * q) hxx
      hnegMul = cong (Ring.neg rg) hmul
      hresidual =
        trans
          (cong (λ q → alpha + q) hnegMul)
          (Ring.addZeroR rg alpha)
  in ⊥-elim
      (OrderedRing.notLtFromLe ha
        (subst (λ q → q < zero) hresidual hr))

------------------------------------------------------------------------
-- The clean, reusable cross-multiplication theorem
AGDA

abort 'residual theorem block not found' unless old.match?(s)
s.sub!(old, new)
File.write(path, s)
abort 'residual theorem remained implicit' if s.match?(/residualSquareNonzero_v140 : ∀ \{S\}\n/)
abort 'residual theorem still uses proof witness as scalar' if s.include?('(mu * (hx * hx))')
puts 'v157 residual proof normalization: PASS'