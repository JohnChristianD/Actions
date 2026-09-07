from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
text = text.replace('cong Ring.neg Rg', 'cong (Ring.neg Rg)')
text = text.replace('(sym (Ring.negScale Rg c (coeff x ρ i)))', '(Ring.negScale Rg c (coeff x ρ i))')
path.write_text(text)
print('efficientchad-neg-cong-parenthesized=True;negScale-direction-fixed=True')
