from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
anchor = '¬ A = A → ⊥\n'
insert = '¬ A = A → ⊥\n\n_≠_ : {A : Set} → A → A → Set\nx ≠ y = ¬ (x ≡ y)\n'
if '_≠_ :' not in s:
    if anchor not in s:
        raise SystemExit('inequality anchor not found')
    s = s.replace(anchor, insert, 1)
p.write_text(s)
if '_≠_ :' not in s or 'x ≠ y = ¬ (x ≡ y)' not in s:
    raise SystemExit('inequality normalization failed')
print('inequality notation present')
