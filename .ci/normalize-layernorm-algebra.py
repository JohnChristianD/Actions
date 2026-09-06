from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start = text.find('layerNormalise :')
end = text.find('\n\nrecurrentAffine :', start)
if start < 0 or end < 0:
    raise SystemExit('layerNormalise region not found')
region = text[start:end]
old = '  centered x = x + neg μ'
new = '  centered : Scalar S → Scalar S\n  centered x = Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) μ)'
region = region.replace(old, new, 1)
region = region.replace('(g * normalise x)', '(Ring._*_ Rg g (normalise x))')
region = region.replace('(x + b)', '(Ring._+_ Rg x b)')
text = text[:start] + region + text[end:]
path.write_text(text)
print('layernorm-centered-signature=True;layernorm-products-qualified=True')
