from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
marker = 'diagonalNewtonExposurePositive_v146 h ='
start = s.find(marker)
if start < 0:
    raise SystemExit('diagonal exposure theorem marker not found')
sep = s.find('\n------------------------------------------------------------------------', start)
if sep < 0:
    raise SystemExit('diagonal exposure theorem boundary not found')
replacement = '''diagonalNewtonExposurePositive_v146 h =
  let OR = SmoothAlgebra.orderedRing _
      Rg = OrderedRing.ring OR
      t = SmoothAlgebra.recip _ (traceProduct_v146 h)
      htrace = OrderedRing.mulPos
        (CoupledHyperParameters_v146.gammaPositive h)
        (CoupledHyperParameters_v146.lambdaPositive h)
      hrec = reciprocalNonnegative_v146 htrace
      hlt = OrderedRing.addLtLeft
        (OrderedRing.zeroLtOne {orderedRing = OR}) t
      hlt' = trans (Ring.addZeroR Rg t) hlt
      hsum = OrderedRing.leLt hrec hlt'
  in trans
       (sym (Ring.addComm Rg t (Ring.one Rg)))
       hsum
'''
s = s[:start] + replacement + s[sep:]

old = '''residualSquareNonzero_v140 : ∀ {S}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero → x ≠ zero
residualSquareNonzero_v140 ha hr hx =
  let hzero : alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing _))
        (mu * (hx * hx)) ≡ alpha =
      trans
        (cong (λ q → alpha + Ring.neg (OrderedRing.ring _) (mu * q))
          (cong₂ (Ring._*_ (OrderedRing.ring _)) hx hx))
        (Ring.addZeroR (OrderedRing.ring _) alpha)
  in ⊥-elim (OrderedRing.notLtFromLe ha (subst (λ q → zero ≤ q) hzero hr))
'''
new = '''residualSquareNonzero_v140 : ∀ {S}
  {alpha mu x : Scalar S} →
  zero ≤ alpha →
  alpha + Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S))
    (mu * (x * x)) < zero → x ≠ zero
residualSquareNonzero_v140 ha hr hxeq =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      hsquare : x * x ≡ Ring.zero Rg =
        cong₂ (Ring._*_ Rg) hxeq hxeq
      hzero : alpha + Ring.neg Rg (mu * (x * x)) ≡ alpha =
        trans
          (cong (λ q → alpha + Ring.neg Rg (mu * q)) hsquare)
          (Ring.addZeroR Rg alpha)
  in ⊥-elim (OrderedRing.notLtFromLe ha (subst (λ q → zero ≤ q) hzero hr))
'''
if old in s:
    s = s.replace(old, new, 1)
elif 'residualSquareNonzero_v140 ha hr hxeq =' not in s:
    raise SystemExit('residual square theorem is neither canonical nor already repaired')

old2 = '''vSub {S} = zipWithV minus
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  minus x y = Ring._+_ Rg x (Ring.neg Rg y)
'''
new2 = '''vSub {S} = zipWithV minus
  where
  Rg = OrderedRing.ring (SmoothAlgebra.orderedRing S)
  minus : Scalar S → Scalar S → Scalar S
  minus x y = Ring._+_ Rg x (Ring.neg Rg y)
'''
if old2 in s:
    s = s.replace(old2, new2, 1)
elif '  minus : Scalar S → Scalar S → Scalar S\n  minus x y =' not in s:
    raise SystemExit('vSub local minus helper is neither canonical nor already typed')

p.write_text(s)
print('diagonal exposure proof, residual-square contradiction, and vSub helper normalized exactly once')
