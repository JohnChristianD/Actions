from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

marker_start = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"
marker_end = "------------------------------------------------------------------------\n-- Seven coupled parameter blocks and finite parameter indices\n"
if s.count(marker_start) != 1 or s.count(marker_end) != 1:
    raise SystemExit(f'unexpected monolith markers: start={s.count(marker_start)} end={s.count(marker_end)}')

needle = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n"
replacement = needle + "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n"
if s.count(needle) != 1:
    raise SystemExit(f'unexpected reciprocal law count: {s.count(needle)}')
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
if s.count(old_acc) > 1:
    raise SystemExit(f'non-unique accumulator parser target: {s.count(old_acc)}')
if s.count(old_acc) == 1:
    s = s.replace(old_acc, new_acc, 1)
else:
    old_at = """  accumulateAt : Fin n → R → Cot → Cot
  accumulateAt i c s j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j

  accumulate i c (state s) = state (accumulateAt i c s)
"""
    if s.count(old_at) == 1:
        s = s.replace(old_at, new_acc, 1)
    elif s.count(new_acc) != 1:
        raise SystemExit('robust accumulateAt parser form not found')

residual_marker = 'residualSquareNonzero_v140 '
rstart = s.find(residual_marker)
if rstart < 0:
    raise SystemExit('residual square theorem marker not found')
rsep = s.find('\n------------------------------------------------------------------------', rstart)
if rsep < 0:
    raise SystemExit('residual square theorem separator not found')
new_residual = '''residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
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
s = s[:rstart] + new_residual + s[rsep:]

q_marker = 'qProjectionCross_v141 '
qstart = s.find(q_marker)
if qstart < 0:
    raise SystemExit('q projection cross theorem marker not found')
qsep = s.find('\n------------------------------------------------------------------------', qstart)
if qsep < 0:
    raise SystemExit('q projection cross theorem separator not found')
new_q = '''qProjectionCross_v141 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =
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
s = s[:qstart] + new_q + s[qsep:]

cross_marker = 'orderedFieldCrossStrict_v142 '
cstart = s.find(cross_marker)
if cstart < 0:
    raise SystemExit('ordered field cross theorem marker not found')
csep = s.find('\n------------------------------------------------------------------------', cstart)
if csep < 0:
    raise SystemExit('ordered field cross theorem separator not found')
new_cross = '''orderedFieldCrossStrict_v142 a b d e hd he h =
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
s = s[:cstart] + new_cross + s[csep:]

old_terminal = 'qTerminalProjectionUnique_v147 t u ha hx hmu ='
if s.count(old_terminal) != 1:
    raise SystemExit(f'expected exactly one terminal uniqueness theorem: {s.count(old_terminal)}')
tstart = s.index(old_terminal)
tsep = s.find('\n------------------------------------------------------------------------', tstart)
if tsep < 0:
    raise SystemExit('terminal uniqueness separator not found')
replacement_terminal = '''qTerminalProjectionUnique_v147 t u refl refl refl =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (sym (QTerminalSolution_v147.stationarity u i)))
'''
s = s[:tstart] + replacement_terminal + s[tsep:]

for needle in [
    'record SmoothAlgebra : Set₁ where',
    'sqrtDomain : R → Set',
    'sqrtSquareLaw :',
    'accumulateAt : Fin n → R → Cot → Fin n → R',
    'residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =',
    'qProjectionCross_v141 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =',
    'orderedFieldCrossStrict_v142 a b d e hd he h =',
    'qTerminalProjectionUnique_v147 t u refl refl refl =']:
    if s.count(needle) != 1:
        raise SystemExit(f'missing/duplicate target: {needle}')

p.write_text(s)
print('monolith canonical algebra/parser/residual/q-cross/reciprocal-cross/terminal uniqueness normalization applied exactly once')
