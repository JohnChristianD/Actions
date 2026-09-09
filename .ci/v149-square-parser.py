from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

old = '    squarePositive : ∀ {x} → x ≠ zero → zero < x * x\n'
new = '    squarePositive : ∀ {x} → x ≠ zero → zero < Ring._*_ ring x x\n'
if old in s:
    s = s.replace(old, new, 1)
elif new not in s:
    raise SystemExit('squarePositive parser target not found')

old_nn = '    squareNonnegative : ∀ x → zero ≤ x * x\n'
new_nn = '    squareNonnegative : ∀ x → zero ≤ Ring._*_ ring x x\n'
if old_nn in s:
    s = s.replace(old_nn, new_nn, 1)
elif new_nn not in s:
    raise SystemExit('squareNonnegative parser target not found')

if s.count(new) != 1 or s.count(new_nn) != 1:
    raise SystemExit('square parser normalization count mismatch')

p.write_text(s)
print('square parser boundaries normalized exactly once')
