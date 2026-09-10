path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

old_residual = /residualSquareNonzero_v140 : ∀ \{S\}\n[\s\S]*?------------------------------------------------------------------------\n-- The clean, reusable cross-multiplication theorem/
new_residual = <<'AGDA'
residualSquareNonzero_v140 : ∀ {S : SmoothAlgebra}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero → x ≠ zero
residualSquareNonzero_v140 ha hr refl =
  ⊥-elim
    (OrderedRing.notLtFromLe ha
      (subst (λ q → q < zero) hresidual hr))
  where
  rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
  hxx = Ring.zeroMulR rg zero
  hmul = cong (λ q → mu * q) hxx
  hnegMul = cong (Ring.neg rg) hmul
  hresidual = trans
    (cong (λ q → alpha + q) hnegMul)
    (Ring.addZeroR rg alpha)

------------------------------------------------------------------------
-- The clean, reusable cross-multiplication theorem
AGDA

old_cross = /orderedFieldCrossStrict_v142 : ∀ \{S\} \(a b d e : Scalar S\) →\n[\s\S]*?------------------------------------------------------------------------\n-- Strict deletion from a negative residual: yd < nz\./
new_cross = <<'AGDA'
orderedFieldLeftNorm_v142 : ∀ {S} (a d e : Scalar S) →
  zero < d →
  (d * e) * (a * SmoothAlgebra.recip _ d) ≡ a * e
orderedFieldLeftNorm_v142 a d e hd =
  trans
    (Ring.mulAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d e
      (a * SmoothAlgebra.recip _ d))
    (trans
      (cong (λ q → d * q)
        (Ring.mulComm (OrderedRing.ring (SmoothAlgebra.orderedRing _)) e
          (a * SmoothAlgebra.recip _ d)))
      (trans
        (sym (Ring.mulAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d
          (a * SmoothAlgebra.recip _ d) e))
        (cong (λ q → q * e) (cancelRecip_v142 a d hd))))

orderedFieldRightNorm_v142 : ∀ {S} (b d e : Scalar S) →
  zero < e →
  (d * e) * (b * SmoothAlgebra.recip _ e) ≡ b * d
orderedFieldRightNorm_v142 b d e he =
  trans
    (Ring.mulAssoc (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d e
      (b * SmoothAlgebra.recip _ e))
    (trans
      (cong (λ q → d * q) (cancelRecip_v142 b e he))
      (Ring.mulComm (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d b))

orderedFieldCrossStrict_v142 : ∀ {S} (a b d e : Scalar S) →
  zero < d → zero < e → a * e < b * d → a * SmoothAlgebra.recip _ d < b * SmoothAlgebra.recip _ e
orderedFieldCrossStrict_v142 a b d e hd he h =
  OrderedRing.mulLtPosCancelLeft
    (transportLt_v142
      (orderedFieldLeftNorm_v142 a d e hd)
      (orderedFieldRightNorm_v142 b d e he)
      h)
    (OrderedRing.mulPos hd he)

------------------------------------------------------------------------
-- Strict deletion from a negative residual: yd < nz.
AGDA

abort 'residual theorem block not found' unless old_residual.match?(s)
s.sub!(old_residual, new_residual)
abort 'cross strict theorem block not found' unless old_cross.match?(s)
s.sub!(old_cross, new_cross)
File.write(path, s)
abort 'residual theorem remained implicit' if s.match?(/residualSquareNonzero_v140 : ∀ \{S\}\n/)
abort 'residual theorem still uses proof witness as scalar' if s.include?('(mu * (hx * hx))')
puts 'v160 residual and reciprocal proofs flattened: PASS'