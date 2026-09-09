from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
record = 'record SmoothAlgebra : Set₁ where'
marker = "------------------------------------------------------------------------\n-- Canonical SmoothAlgebra boundary.\n"
first = s.find(record)
if first >= 0:
    # The pre-v149 algebra surface is obsolete. Remove that entire surface,
    # including its legacy vector/matrix implementations, but retain the
    # generic tabulateV helper because the canonical matVec uses it.
    legacy_start = first
    tab = s.find('tabulateV :', first)
    if tab < 0:
        raise SystemExit('generic tabulateV helper not found after legacy SmoothAlgebra')
    tab_end = s.find('\n------------------------------------------------------------------------', tab)
    if tab_end < 0:
        raise SystemExit('separator after legacy tabulateV not found')
    tabulate_block = s[tab:tab_end]
    canonical = s.find(marker, tab_end)
    if canonical < 0:
        raise SystemExit('canonical SmoothAlgebra marker not found after legacy algebra')
    s = s[:legacy_start] + tabulate_block + '\n\n' + s[canonical:]

# If more than one canonical record survived, retain the first canonical
# surface and delete later duplicate canonical surfaces through their local
# vector-algebra terminator.
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