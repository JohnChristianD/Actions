from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
old_import = 'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)'
new_import = 'open import Agda.Builtin.Nat using (Nat; suc; _+_) renaming (zero to natZero)'
if old_import in s:
    s = s.replace(old_import, new_import, 1)
# Only the finite Nat definitions before Ring need Nat.zero explicitly. After
# `open Ring`, unqualified `zero` is intentionally the scalar-ring field.
for old, new in [
    ('Vec A zero', 'Vec A natZero'),
    ('sumFin _ z zero _', 'sumFin _ z natZero _'),
]:
    if old in s:
        s = s.replace(old, new, 1)
if old_import in s:
    raise SystemExit('Nat import alias did not persist')
if 'open import Agda.Builtin.Nat using (Nat; suc; _+_) renaming (zero to natZero)' not in s:
    raise SystemExit('Nat zero import alias missing')
if s.count('Vec A natZero') != 1:
    raise SystemExit('Vec Nat.zero scope repair count mismatch')
if s.count('sumFin _ z natZero _') != 1:
    raise SystemExit('sumFin Nat.zero scope repair count mismatch')
p.write_text(s)
print('Nat zero is now natZero; scalar Ring.zero remains unqualified after Ring scope opens')