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
    new_at = """  accumulateAt : Fin n → R → Cot → Fin n → R
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (accumulateAt i c s)
"""
    if s.count(old_at) == 1:
        s = s.replace(old_at, new_at, 1)
    elif s.count(new_at) != 1:
        raise SystemExit('robust accumulateAt parser form not found')

if s.count('record SmoothAlgebra : Set₁ where') != 1:
    raise SystemExit('expected exactly one SmoothAlgebra declaration after dedupe')
if s.count('sqrtDomain : R → Set') != 1 or s.count('sqrtSquareLaw :') != 1:
    raise SystemExit('expected exactly one domain-aware sqrt law after dedupe')
if s.count('accumulateAt : Fin n → R → Cot → Fin n → R') != 1:
    raise SystemExit('expected exactly one robust accumulateAt declaration')

p.write_text(s)
print('monolith dedupe/domain/accumulateAt normalization applied exactly once')
