from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
text = path.read_text()
marker = '------------------------------------------------------------------------\n-- Algebraic scalar model\n------------------------------------------------------------------------\n\n'
insert = marker + 'infix 4 _≤_ _<_\ninfixl 20 _+_\ninfixl 30 _*_\n\n'
if insert not in text:
    if marker not in text:
        raise SystemExit('algebraic scalar model marker not found')
    text = text.replace(marker, insert, 1)
path.write_text(text)
print('algebra-fixity-normalized=True')
