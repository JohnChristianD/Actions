from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
marker = '¬ A = A → ⊥\n'
helper = '''\n_≠_ : {A : Set} → A → A → Set\nx ≠ y = ¬ (x ≡ y)\n'''
if '_≠_ : {A : Set} → A → A → Set' not in s:
    if marker not in s:
        raise SystemExit('negation definition marker missing')
    s = s.replace(marker, marker + helper, 1)
p.write_text(s)
print('finite equality-negation operator is in scope')