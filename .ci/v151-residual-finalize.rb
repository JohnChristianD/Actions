path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

old_residual = /residualSquareNonzero_v140 : ∀ \{S\}[\s\S]*?(?=------------------------------------------------------------------------\n-- The clean, reusable cross-multiplication theorem)/
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

AGDA

old_multiplier = /multiplierDeletionStrict_v142 : ∀ \{S\} \(n d y z : Scalar S\) →\n[\s\S]*?------------------------------------------------------------------------\n-- Fixed-mask q-projection transpose\./
new_multiplier = <<'AGDA'
multiplierLhsNorm_v142 : ∀ {S} (n d z : Scalar S) →
  n * (d + neg z) ≡ (n * d) + neg (n * z)
multiplierLhsNorm_v142 n d z =
  trans
    (Ring.distrib (OrderedRing.ring (SmoothAlgebra.orderedRing _)) n d (neg z))
    (cong₂ _+_ refl
      (sym (Ring.negScale (OrderedRing.ring (SmoothAlgebra.orderedRing _)) n z)))

multiplierRhsNorm_v142 : ∀ {S} (n d y : Scalar S) →
  (n + neg y) * d ≡ (n * d) + neg (y * d)
multiplierRhsNorm_v142 n d y =
  trans
    (Ring.distrib (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d n (neg y))
    (trans
      (cong₂ _+_
        (Ring.mulComm (OrderedRing.ring (SmoothAlgebra.orderedRing _)) d n)
        refl)
      (cong₂ _+_ refl
        (trans
          (Ring.mulComm (OrderedRing.ring (SmoothAlgebra.orderedRing _))
            (neg y) d)
          (sym (Ring.negScale (OrderedRing.ring (SmoothAlgebra.orderedRing _)) y d)))))

multiplierDeletionStrict_v142 : ∀ {S} (n d y z : Scalar S) →
  zero < d → zero < d + neg z → y * d < n * z →
  n * SmoothAlgebra.recip _ d < (n + neg y) * SmoothAlgebra.recip _ (d + neg z)
multiplierDeletionStrict_v142 n d y z hd he h =
  orderedFieldCrossStrict_v142 n (n + neg y) d (d + neg z) hd he
    (transportLt_v142
      (multiplierLhsNorm_v142 n d z)
      (multiplierRhsNorm_v142 n d y)
      (OrderedRing.addLtLeft (OrderedRing.negLt h) (n * d)))

------------------------------------------------------------------------
-- Fixed-mask q-projection transpose.
AGDA

abort 'residual theorem block not found' unless old_residual.match?(s)
s.sub!(old_residual, new_residual)
abort 'cross strict theorem block not found' unless old_cross.match?(s)
s.sub!(old_cross, new_cross)
abort 'multiplier theorem block not found' unless old_multiplier.match?(s)
s.sub!(old_multiplier, new_multiplier)
File.write(path, s)
abort 'residual theorem still uses proof witness as scalar' if s.include?('(mu * (hx * hx))')
puts 'v162 residual, reciprocal, and multiplier proofs flattened: PASS'