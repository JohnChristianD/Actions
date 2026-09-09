from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
old_import = 'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)'
new_import = 'open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to natZero)'
if old_import in s:
    s = s.replace(old_import, new_import, 1)
else:
    s = s.replace(
        'open import Agda.Builtin.Nat using (Nat; suc; _+_) renaming (zero to natZero)',
        new_import,
        1,
    )
for old, new in [
    ('Vec A zero', 'Vec A natZero'),
    ('sumFin _ z zero _', 'sumFin _ z natZero _'),
]:
    if old in s:
        s = s.replace(old, new, 1)
if old_import in s:
    raise SystemExit('Nat import alias did not persist')
if new_import not in s:
    raise SystemExit('Nat zero import alias missing')
if 'using (Nat; suc; _+_)' in s:
    raise SystemExit('Nat addition remains exported into scalar namespace')
p.write_text(s)
print('Nat namespace reduced to Nat/suc/natZero; scalar _+_ remains reserved for Ring')