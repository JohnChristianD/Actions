from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start = text.find('module EfficientCHAD (S : SmoothAlgebra) (n : Nat) where')
end = text.find('\n------------------------------------------------------------------------', start + 10)
if start < 0 or end < 0:
    raise SystemExit('EfficientCHAD module region not found')
region = text[start:end]
replacements = {
    's j + c': 'Ring._+_ Rg (s j) c',
    'runState s i + b i': 'Ring._+_ Rg (runState s i) (b i)',
}
changed = 0
for old, new in replacements.items():
    n = region.count(old)
    if n:
        region = region.replace(old, new)
        changed += n
text = text[:start] + region + text[end:]
path.write_text(text)
print(f'accumulate-algebra-qualified={changed}')
