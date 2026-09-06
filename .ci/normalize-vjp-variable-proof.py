from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
old = "  vjpCoeff (var j) _ c i with finDecEq i j\n  ... | yes _ = sym (Ring.mulOneR Rg c)\n  ... | no _ = sym (Ring.zeroMulR Rg c)\n"
new = "  vjpCoeff (var j) _ c i = refl\n"
if old not in text:
    raise SystemExit('variable VJP proof block not found')
text = text.replace(old, new, 1)
path.write_text(text)
print('vjp-variable-proof-reflexive=True')
