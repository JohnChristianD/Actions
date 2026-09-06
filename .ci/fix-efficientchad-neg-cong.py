from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = '(sym (Ring.negScale Rg c (coeff x ρ i)))'
new = '(Ring.negScale Rg c (coeff x ρ i))'
if old in text:
    text = text.replace(old, new, 1)
path.write_text(text)
print(f'efficientchad-negScale-direction-fixed={old in text or new in text}')
