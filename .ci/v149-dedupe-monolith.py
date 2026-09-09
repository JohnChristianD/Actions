from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

marker_start = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"
marker_end = "------------------------------------------------------------------------\n-- Seven coupled parameter blocks and finite parameter indices\n"
if s.count(marker_start) != 1 or s.count(marker_end) != 1:
    raise SystemExit(f'unexpected monolith markers: start={s.count(marker_start)} end={s.count(marker_end)}')

needle = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n"
replacement = needle + "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n"
if s.count(needle) == 1:
    s = s.replace(needle, replacement, 1)

start = s.index(marker_start)
end = s.index(marker_end, start)
s = s[:start] + s[end:]

old_acc = """  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)
"""
new_acc = """  accumulateAt : Fin n → R → Cot → Fin n → R
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (accumulateAt i c s)
"""
if s.count(old_acc) == 1:
    s = s.replace(old_acc, new_acc, 1)

residual_marker = 'residualSquareNonzero_v140 '
rstart = s.find(residual_marker)
if rstart < 0: raise SystemExit('residual theorem marker not found')
rsep = s.find('\n------------------------------------------------------------------------', rstart)
residual = '''residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
  λ hx →
    let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
        hxx0 = trans
          (cong₂ (Ring._*_ Rg) hx hx)
          (Ring.zeroMulL Rg zero)
        hmu0 = trans
          (cong (λ q → mu * q) hxx0)
          (Ring.zeroMulR Rg mu)
        hneg0 = trans
          (cong (λ q → Ring.neg Rg q) hmu0)
          (trans
            (sym (Ring.addZeroR Rg (Ring.neg Rg zero)))
            (Ring.addNegL Rg zero))
        hzero = trans
          (cong (λ q → alpha + q) hneg0)
          (Ring.addZeroR Rg alpha)
        hlt = subst (λ q → q < zero) hzero hr
    in OrderedRing.notLtFromLe ha hlt
'''
s = s[:rstart] + residual + s[rsep:]

q_marker = 'qProjectionCross_v141 '
qstart = s.find(q_marker)
if qstart < 0: raise SystemExit('q projection theorem marker not found')
qsep = s.find('\n------------------------------------------------------------------------', qstart)
qcross = '''qProjectionCross_v141 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      hx = residualSquareNonzero_v140 ha hr
      hxx = OrderedRing.squarePositive hx
      hlt = OrderedRing.subLtZero hr
      hmul = OrderedRing.mulLtPosLeft hlt hxx
      hright =
        trans
          (Ring.mulComm Rg (x * x) (mu * (x * x)))
          (sym (Ring.mulAssoc Rg mu (x * x) (x * x)))
  in trans
       (trans
         (sym (Ring.mulComm Rg alpha (x * x)))
         hmul)
       hright
'''
s = s[:qstart] + qcross + s[qsep:]

cross_marker = 'orderedFieldCrossStrict_v142 '
cstart = s.find(cross_marker)
if cstart < 0: raise SystemExit('cross theorem marker not found')
csep = s.find('\n------------------------------------------------------------------------', cstart)
cross = '''orderedFieldCrossStrict_v142 a b d e hd he h =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      leftCancel = cancelRecip_v142 a d hd
      rightCancel = cancelRecip_v142 b e he
      leftNorm =
        trans
          (sym (Ring.mulAssoc Rg d e (a * SmoothAlgebra.recip _ d)))
          (trans
            (cong (λ q → e * q) leftCancel)
            (Ring.mulComm Rg e a))
      rightNorm =
        trans
          (sym (Ring.mulAssoc Rg e d (b * SmoothAlgebra.recip _ e)))
          (trans
            (cong (λ q → d * q) rightCancel)
            (Ring.mulComm Rg d b))
  in OrderedRing.mulLtPosCancelLeft (transportLt_v142 leftNorm rightNorm h)
       (OrderedRing.mulPos hd he)
'''
s = s[:cstart] + cross + s[csep:]

mult_marker = 'multiplierDeletionStrict_v142 '
mstart = s.find(mult_marker)
if mstart < 0: raise SystemExit('multiplier theorem marker not found')
msep = s.find('\n------------------------------------------------------------------------', mstart)
mult = '''multiplierDeletionStrict_v142 n d y z hd he h =
  let Rg = OrderedRing.ring (SmoothAlgebra.orderedRing _)
      hnz = OrderedRing.negLt h
      base = n * d
      negMul =
        trans
          (sym (Ring.negScale Rg d y))
          (cong (Ring.neg Rg) (Ring.mulComm Rg d y))
      lhs =
        trans
          (Ring.distrib Rg n d (neg z))
          (cong₂ _+_ refl (sym (Ring.negScale Rg n z)))
      rhs =
        trans
          (Ring.distrib Rg d n (neg y))
          (cong₂ _+_ (Ring.mulComm Rg d n) negMul)
      cross = OrderedRing.addLtLeft hnz base
      cross' = transportLt_v142 lhs rhs cross
  in orderedFieldCrossStrict_v142 n (n + neg y) d (d + neg z) hd he cross'
'''
s = s[:mstart] + mult + s[msep:]

old_terminal = 'qTerminalProjectionUnique_v147 t u ha hx hmu ='
if s.count(old_terminal) != 1: raise SystemExit('terminal uniqueness theorem count mismatch')
tstart = s.index(old_terminal)
tsep = s.find('\n------------------------------------------------------------------------', tstart)
terminal = '''qTerminalProjectionUnique_v147 t u refl refl refl =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (sym (QTerminalSolution_v147.stationarity u i)))
'''
s = s[:tstart] + terminal + s[tsep:]

checks = [
    'record SmoothAlgebra : Set₁ where',
    'sqrtDomain : R → Set',
    'sqrtSquareLaw :',
    'accumulateAt : Fin n → R → Cot → Fin n → R',
    'residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =',
    'qProjectionCross_v141 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =',
    'orderedFieldCrossStrict_v142 a b d e hd he h =',
    'multiplierDeletionStrict_v142 n d y z hd he h =',
    'qTerminalProjectionUnique_v147 t u refl refl refl =']
for needle in checks:
    if s.count(needle) != 1: raise SystemExit(f'missing/duplicate target: {needle}')

p.write_text(s)
print('monolith canonical algebra/parser/residual/q-cross/reciprocal-cross/multiplier/terminal normalization applied exactly once')
