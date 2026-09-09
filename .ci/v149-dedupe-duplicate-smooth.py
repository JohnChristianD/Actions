from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
record = 'record SmoothAlgebra : Set₁ where'
marker = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"

# The canonical v149 boundary is authoritative. Any legacy SmoothAlgebra and
# its pre-canonical vector/matrix surface must be removed before checking the
# canonical definitions. Keep only the generic tabulateV helper from that old
# surface because the canonical matVec reuses it.
first_record = s.find(record)
canonical = s.find(marker)
if first_record >= 0 and canonical >= 0 and first_record < canonical:
    tab = s.find('tabulateV :', first_record, canonical)
    if tab < 0:
        raise SystemExit('legacy tabulateV helper not found before canonical boundary')
    legacy_mat = s.find('\nmatVec :', tab, canonical)
    if legacy_mat < 0:
        raise SystemExit('legacy matVec declaration not found after tabulateV')
    tabulate_block = s[tab:legacy_mat]
    s = s[:first_record] + tabulate_block + '\n\n' + s[canonical:]

# Remove any later duplicated canonical SmoothAlgebra surface. The first is
# the retained authoritative definition.
first = s.find(record)
second = s.find(record, first + len(record)) if first >= 0 else -1
if second >= 0:
    keep = s.find('vAddZeroL :', second)
    if keep < 0:
        raise SystemExit('vAddZeroL terminator not found after duplicate SmoothAlgebra')
    s = s[:second] + s[keep:]

if s.count(record) != 1:
    raise SystemExit(f'SmoothAlgebra definition count is {s.count(record)}, expected 1')
if s.count('matVec :') != 1:
    raise SystemExit(f'matVec definition count is {s.count("matVec :")}, expected 1')
if s.count('matMul :') != 1:
    raise SystemExit(f'matMul definition count is {s.count("matMul :")}, expected 1')
if s.count('tabulateV :') != 1:
    raise SystemExit(f'tabulateV helper count is {s.count("tabulateV :")}, expected 1')
p.write_text(s)
print('legacy smooth algebra removed; canonical algebra/vector/matrix definitions unique')