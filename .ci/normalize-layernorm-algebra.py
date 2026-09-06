from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start = text.find('layerNormalise :')
end = text.find('\n\nrecurrentAffine :', start)
if start < 0 or end < 0:
    raise SystemExit('layerNormalise region not found')
region = text[start:end]
region = region.replace(
    '  centered x = x + neg μ',
    '  centered : Scalar S → Scalar S\n  centered x = Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)) x (Ring.neg (OrderedRing.ring (SmoothAlgebra.orderedRing S)) μ)',
    1,
)
region = region.replace(
    '  normalise x = centered x * invStd',
    '  normalise : Scalar S → Scalar S\n  normalise x = Ring._*_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)) (centered x) invStd',
    1,
)
region = region.replace('(g * normalise x)', '(Ring._*_ Rg g (normalise x))', 1)
region = region.replace('(x + b)', '(Ring._+_ Rg x b)', 1)
text = text[:start] + region + text[end:]
path.write_text(text)
print('layernorm-centered-signature=True;layernorm-normalise-signature=True;layernorm-products-qualified=True')
