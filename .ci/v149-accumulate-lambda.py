from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
old = '''  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)
'''
new = '''  accumulateAt : Fin n → R → Cot → Fin n → R
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (accumulateAt i c s)
'''
if old not in s:
    if new in s:
        print('accumulate helper already present')
        raise SystemExit(0)
    raise SystemExit('accumulate lambda pattern absent')
if s.count(old) != 1:
    raise SystemExit(f'accumulate lambda pattern count={s.count(old)}; expected 1')
p.write_text(s.replace(old, new, 1))
print('accumulate-with lambda lifted to named helper exactly once')
