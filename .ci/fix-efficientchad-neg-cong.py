from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = 'cong Ring.neg Rg'
new = 'cong (Ring.neg Rg)'
if old in text:
    text = text.replace(old, new)
path.write_text(text)
print(f'efficientchad-neg-cong-parenthesized={old in text or "cong (Ring.neg Rg)" in text}')
