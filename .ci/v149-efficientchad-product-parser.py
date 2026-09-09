from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
old = '  coeff (mul x y) ρ i = eval y ρ * coeff x ρ i + eval x ρ * coeff y ρ i\n'
new = '  coeff (mul x y) ρ i = (eval y ρ * coeff x ρ i) + (eval x ρ * coeff y ρ i)\n'
if old in s:
    s = s.replace(old, new, 1)
elif new not in s:
    raise SystemExit('unparenthesized EfficientCHAD product coefficient rule not found')
p.write_text(s)
print('EfficientCHAD product coefficient parser ambiguity normalized')
