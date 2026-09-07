from pathlib import Path

# Final workflow validation for the CompleteSafe OrderedRing surface.
# The preceding namespace normalizer performs the transformation; this step
# asserts that the kernel input no longer contains the known ambiguous forms.
p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

for forbidden in (
    'zero ≤ a * b',
    'a + c ≤ b + d',
    'c * a ≤ c * b',
    'a < b → c < d → a + c < b + d',
):
    if forbidden in s:
        raise SystemExit(f'final ordered-field qualification incomplete: {forbidden!r}')

print('final-ordered-ring-qualification=validated')
