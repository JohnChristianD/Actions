from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
start = text.find('record OrderedRing : Set₁ where')
end = text.find('\nopen OrderedRing', start)
if start < 0 or end < 0:
    raise SystemExit('OrderedRing region not found')
region = text[start:end]
region = region.replace(
    'squarePositive : ∀ {x} → x ≠ zero → zero < (x * x)',
    'squarePositive : ∀ {x} → ¬ (x ≡ zero) → zero < (x * x)',
    1)
region = region.replace(
    'squarePositive : ∀ {x} → x ≠ zero → zero < x * x',
    'squarePositive : ∀ {x} → ¬ (x ≡ zero) → zero < (x * x)',
    1)
path.write_text(text[:start] + region + text[end:])
print('ordered-ring-inequality-normalized=True')
