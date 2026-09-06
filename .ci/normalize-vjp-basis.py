from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = "  coeff (var j) _ i with finDecEq i j\n  ... | yes _ = one\n  ... | no _ = zero\n"
new = "  coeff (var j) _ i = basis j i\n"
if old in text:
    text = text.replace(old, new, 1)
path.write_text(text)
print('vjp-coeff-variable-as-basis=True')
