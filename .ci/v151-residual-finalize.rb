path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

old = /residualSquareNonzero_v140 : ∀ \{S\}\n[\s\S]*?------------------------------------------------------------------------\n-- The clean, reusable cross-multiplication theorem/
new = <<'AGDA'
residualSquareNonzero_v140 : ∀ {S : SmoothAlgebra}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero → x ≠ zero
residualSquareNonzero_v140 ha hr hx =
  ⊥-elim
    (OrderedRing.notLtFromLe ha
      (subst (λ q → q < zero) hresidual hr))
  where
  rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
  hxx =
    trans
      (cong₂ (Ring._*_ rg) hx hx)
      (Ring.zeroMulR rg zero)
  hmul =
    trans
      (cong (λ q → mu * q) hxx)
      (Ring.zeroMulR rg mu)
  hnegZero =
    trans
      (sym (Ring.addZeroR rg (Ring.neg rg zero)))
      (Ring.addNegL rg zero)
  hresidual =
    trans
      (cong (λ q → alpha + q)
        (trans
          (cong (Ring.neg rg) hmul)
          hnegZero))
      (Ring.addZeroR rg alpha)

------------------------------------------------------------------------
-- The clean, reusable cross-multiplication theorem
AGDA

abort 'residual theorem block not found' unless old.match?(s)
s.sub!(old, new)
File.write(path, s)
abort 'residual theorem remained implicit' if s.match?(/residualSquareNonzero_v140 : ∀ \{S\}\n/)
abort 'residual theorem still uses proof witness as scalar' if s.include?('(mu * (hx * hx))')
puts 'v155 residual proof normalization: PASS'