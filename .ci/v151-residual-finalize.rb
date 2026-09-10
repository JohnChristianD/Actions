path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

old = /residualSquareNonzero_v140 : ∀ \{S\}\n.*?------------------------------------------------------------------------\n-- The clean, reusable cross-multiplication theorem/sm
new = <<'AGDA'
residualSquareNonzero_v140 : ∀ {S : SmoothAlgebra}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero → x ≠ zero
residualSquareNonzero_v140 ha hr hx =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      hxx : _ ≡ zero =
        trans
          (cong₂ (Ring._*_ Rg) hx hx)
          (Ring.zeroMulR Rg zero)
      hmul : _ ≡ zero =
        trans
          (cong (λ q → _ * q) hxx)
          (Ring.zeroMulR Rg mu)
      hnegZero : Ring.neg Rg zero ≡ zero =
        trans
          (sym (Ring.addZeroR Rg (Ring.neg Rg zero)))
          (Ring.addNegL Rg zero)
      hresidual : _ ≡ alpha =
        trans
          (cong (λ q → alpha + q)
            (trans
              (cong (Ring.neg Rg) hmul)
              hnegZero))
          (Ring.addZeroR Rg alpha)
  in ⊥-elim
      (OrderedRing.notLtFromLe ha
        (subst (λ q → q < zero) hresidual hr))

------------------------------------------------------------------------
-- The clean, reusable cross-multiplication theorem
AGDA

unless old.match?(s)
  abort 'residual theorem block not found'
end
s.sub!(old, new)
File.write(path, s)
abort 'residual theorem remained implicit' if s.match?(/residualSquareNonzero_v140 : ∀ \{S\}\n/)
abort 'residual theorem still uses proof witness as scalar' if s.include?('(mu * (hx * hx))')
puts 'v152 residual proof normalization: PASS'