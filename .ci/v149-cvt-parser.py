from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()

needle = 'insertCVT_v142 D a i f = record { cell = λ j with finDecEq i j'
if s.count(needle) == 0:
    if s.count('insertCVT_v142 D a i f = record { cell = insertCVTCell_v142 D a i }') == 1:
        print('CVT insertion already normalized')
        raise SystemExit(0)
    if s.count('insertCVT_v142 D a i f = record { cell = insertCVTCell_v142 D a i f }') == 1:
        print('CVT insertion already normalized')
        raise SystemExit(0)
    raise SystemExit('CVT insertion parser target not found')
if s.count(needle) != 1:
    raise SystemExit(f'non-unique CVT insertion parser target: {s.count(needle)}')

start = s.index(needle)
end = s.find('\n\nrecord AntitheticSample_v142 ', start)
if end < 0:
    raise SystemExit('CVT replacement boundary not found')

replacement = '''makeCVTSlot_v142 : ∀ {S} → Scalar S → CVTSlot_v142 S
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

insertCVT_v142 D a i f = record { cell = insertCVTCell_v142 D a i f }'''

s = s[:start] + replacement + s[end:]
p.write_text(s)
print('CVT insertion lambda normalized exactly once')
