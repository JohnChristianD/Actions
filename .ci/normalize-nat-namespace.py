from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = 'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)'
new = 'open import Agda.Builtin.Nat using (Nat; suc)'
if old not in text:
    raise SystemExit('Nat import shape not found')
text = text.replace(old, new, 1)
old_vec = '  [] : Vec A zero\n'
new_vec = '  [] : Vec A Nat.zero\n'
if old_vec not in text:
    raise SystemExit('Vec zero constructor line not found')
text = text.replace(old_vec, new_vec, 1)
old_sum = 'sumFin _ z zero _ = z\n'
new_sum = 'sumFin _ z Nat.zero _ = z\n'
if old_sum not in text:
    raise SystemExit('sumFin zero clause not found')
text = text.replace(old_sum, new_sum, 1)
path.write_text(text)
print('nat-namespace-normalized=True')
