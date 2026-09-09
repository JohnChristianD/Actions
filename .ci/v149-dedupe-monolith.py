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

old_terminal = 'qTerminalProjectionUnique_v147 t u ha hx hmu ='
if s.count(old_terminal) != 1:
    raise SystemExit(f'expected exactly one terminal uniqueness theorem: {s.count(old_terminal)}')
start = s.index(old_terminal)
sep = s.find('\n------------------------------------------------------------------------', start)
if sep < 0:
    raise SystemExit('expected separator after terminal uniqueness theorem')
replacement_terminal = '''qTerminalProjectionUnique_v147 t u refl refl refl =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (sym (QTerminalSolution_v147.stationarity u i)))
'''
s = s[:start] + replacement_terminal + s[sep:]

if s.count('record SmoothAlgebra : Set₁ where') != 1:
    raise SystemExit('expected exactly one SmoothAlgebra declaration after dedupe')
if s.count('sqrtDomain : R → Set') != 1 or s.count('sqrtSquareLaw :') != 1:
    raise SystemExit('expected exactly one domain-aware sqrt law after dedupe')
if s.count('accumulateAt : Fin n → R → Cot → Fin n → R') != 1:
    raise SystemExit('expected exactly one robust accumulateAt declaration')
if s.count('residualSquareNonzero_v140 {S} {alpha = alpha} {mu = mu} {x = x} ha hr =') != 1:
    raise SystemExit('residual square normalization missing')
if s.count('        hlt = subst (λ q → q < zero) hzero hr') != 1:
    raise SystemExit('residual hlt inference normalization missing')
if s.count('qTerminalProjectionUnique_v147 t u refl refl refl =') != 1:
    raise SystemExit('terminal uniqueness normalization missing')

p.write_text(s)
print('monolith canonical algebra/parser/residual/terminal uniqueness normalization applied exactly once')
