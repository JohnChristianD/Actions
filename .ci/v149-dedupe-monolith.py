from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

# Keep algebraic zero unqualified; qualify Nat.zero where it denotes a
# vector/index size constructor. Do not globally rewrite algebraic zero.
s = s.replace(
    'open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)',
    'open import Agda.Builtin.Nat using (Nat; suc; _+_)',
    1,
)
for old, new in [
    ('Vec A zero', 'Vec A Nat.zero'),
    ('sumFin _ z zero _ = z', 'sumFin _ z Nat.zero _ = z'),
    ('tabulateV {zero} f = []', 'tabulateV {A = _} {n = Nat.zero} f = []'),
    ('tabulateVS {S} {zero} f = []', 'tabulateVS {S} {Nat.zero} f = []'),
    ('zeroVector {S} {zero} = []', 'zeroVector {S} {Nat.zero} = []'),
    ('zeroVecS {S} {zero} = []', 'zeroVecS {S} {Nat.zero} = []'),
    ('vZero_v140 {S} {zero} = []', 'vZero_v140 {S} {Nat.zero} = []'),
    ('maskAllFalse {zero} = []', 'maskAllFalse {Nat.zero} = []'),
    ('qRunFuel_v142 zero r = r', 'qRunFuel_v142 Nat.zero r = r'),
    ('shiftLV_v146 zero xs = xs', 'shiftLV_v146 Nat.zero xs = xs'),
    ('shiftRV_v146 zero xs = xs', 'shiftRV_v146 Nat.zero xs = xs'),
    ('qsaXorShiftDeterministic_v146 zero seed = []', 'qsaXorShiftDeterministic_v146 Nat.zero seed = []'),
]:
    if old in s:
        s = s.replace(old, new, 1)

canonical_header = '-- Canonical SmoothAlgebra boundary.'
header_pos = s.find(canonical_header)
if header_pos < 0:
    raise SystemExit('canonical SmoothAlgebra header not found')
legacy_pos = s.find('record SmoothAlgebra : Set₁ where')
if legacy_pos >= 0 and legacy_pos < header_pos:
    scalar_pos = s.find('\nScalar : SmoothAlgebra → Set\n', legacy_pos)
    if scalar_pos < 0 or scalar_pos > header_pos:
        raise SystemExit('legacy SmoothAlgebra block has no scalar boundary')
    s = s[:legacy_pos] + s[scalar_pos + 1:]
    header_pos = s.find(canonical_header)

marker_start = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"
marker_end = "------------------------------------------------------------------------\n-- Seven coupled parameter blocks and finite parameter indices\n"
if marker_start not in s or marker_end not in s:
    raise SystemExit('canonical SmoothAlgebra markers not found')
first = s.index(marker_start)
end_boundary = s.find(marker_end, first + len(marker_start))
if end_boundary < 0:
    raise SystemExit('canonical SmoothAlgebra closing boundary not found')
region = s[first:end_boundary]
record_token = 'record SmoothAlgebra : Set₁ where'
first_record = region.find(record_token)
if first_record < 0:
    raise SystemExit('canonical SmoothAlgebra record missing')
second_record = region.find(record_token, first_record + len(record_token))
while second_record >= 0:
    scalar_pos = region.find('\nScalar : SmoothAlgebra → Set\n', second_record)
    if scalar_pos < 0:
        raise SystemExit('duplicate SmoothAlgebra has no scalar boundary')
    region = region[:second_record] + region[scalar_pos + 1:]
    second_record = region.find(record_token, first_record + len(record_token))
s = s[:first] + region + s[end_boundary:]

old_max = "    sqrt recip max min : R → R\n"
new_max = "    sqrt recip : R → R\n    max min : R → R → R\n"
if old_max in s:
    s = s.replace(old_max, new_max, 1)
elif '    max min : R → R → R' not in s:
    raise SystemExit('SmoothAlgebra max/min signature not found')

needle = "    reciprocalLaw : ∀ {d} → zero < d → Ring._*_ (OrderedRing.ring orderedRing) d (recip d) ≡ one\n"
if needle in s and '    sqrtDomain : R → Set\n' not in s:
    s = s.replace(needle, needle + "    sqrtDomain : R → Set\n    sqrtSquareLaw : ∀ x → sqrtDomain x →\n      Ring._*_ (OrderedRing.ring orderedRing) (sqrt x) (sqrt x) ≡ x\n", 1)

old_acc = """  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (λ j with finDecEq j i
    ... | yes _ = s j + c
    ... | no _ = s j)
"""
new_acc = """  accumulateAt : Fin n → R → Cot → Fin n → R
  accumulateAt i c s j with finDecEq j i
  ... | yes _ = s j + c
  ... | no _ = s j

  accumulate : Fin n → R → EState → EState
  accumulate i c (state s) = state (accumulateAt i c s)
"""
if old_acc in s:
    s = s.replace(old_acc, new_acc, 1)

old_cvt = """insertCVT_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →
  CVTArchive_v142 S cells → Fin cells → Scalar S → CVTArchive_v142 S cells
insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j
  ... | no _ = CVTArchive_v142.cell a j
  ... | yes _ with CVTSlot_v142.occupied (CVTArchive_v142.cell a j)
  ...   | false = record { occupied = true ; fitness = f }
  ...   | true with QProjectionDecisionAlgebra_v140.ltDec D
        (CVTSlot_v142.fitness (CVTArchive_v142.cell a j)) f
  ...     | yes _ = record { occupied = true ; fitness = f }
  ...     | no _ = CVTArchive_v142.cell a j }
"""
new_cvt = """makeCVTSlot_v142 : ∀ {S} → Scalar S → CVTSlot_v142 S
makeCVTSlot_v142 f = record { occupied = true ; fitness = f }

insertCVTOccupied_v142 : ∀ {S} → QProjectionDecisionAlgebra_v140 S →
  CVTSlot_v142 S → Scalar S → CVTSlot_v142 S
insertCVTOccupied_v142 D slot f with QProjectionDecisionAlgebra_v140.ltDec D
  (CVTSlot_v142.fitness slot) f
... | yes _ = makeCVTSlot_v142 f
... | no _ = slot

insertCVTReplacement_v142 : ∀ {S} → QProjectionDecisionAlgebra_v140 S →
  CVTSlot_v142 S → Scalar S → CVTSlot_v142 S
insertCVTReplacement_v142 D slot f with CVTSlot_v142.occupied slot
... | false = makeCVTSlot_v142 f
... | true = insertCVTOccupied_v142 D slot f

insertCVTCell_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →
  CVTArchive_v142 S cells → Fin cells → Scalar S → Fin cells → CVTSlot_v142 S
insertCVTCell_v142 D a i f j with finDecEq i j
... | no _ = CVTArchive_v142.cell a j
... | yes _ = insertCVTReplacement_v142 D (CVTArchive_v142.cell a j) f

insertCVT_v142 : ∀ {S cells} → QProjectionDecisionAlgebra_v140 S →
  CVTArchive_v142 S cells → Fin cells → Scalar S → CVTArchive_v142 S cells
insertCVT_v142 D a i f = record
  { cell = insertCVTCell_v142 D a i f
  }
"""
if old_cvt in s:
    s = s.replace(old_cvt, new_cvt, 1)

header_marker = "-- Canonical SmoothAlgebra boundary.\n"
kmarker = "-- AUDITED-KKT-OBLIGATION"
# Audit the final normalized surface rather than trusting a single rewrite.
if s.count(header_marker) != 1:
    raise SystemExit('canonical marker count is not one')
if s.count(record_token) != 1:
    raise SystemExit('SmoothAlgebra record count is not one')
if s.count('sqrtDomain : R → Set') != 1:
    raise SystemExit('sqrt domain law missing or duplicated')
if s.count(kmarker) != 0:
    raise SystemExit('malformed audited KKT placeholder marker survived')
if 'λ j with finDecEq' in s:
    raise SystemExit('dependent lambda-with parser form survived')
p.write_text(s)
print('v149 monolith normalization complete: one SmoothAlgebra, canonical max/min arity, finite helper rewrites')
