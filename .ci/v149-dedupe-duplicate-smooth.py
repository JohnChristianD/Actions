from pathlib import Path
import re

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

# A generic zipWithV already exists near the primitive vector helpers. The
# canonical vAdd/vSub/vHadamard blocks previously redeclared the same helper
# locally, which clashes at top-level scope under Agda 2.8.0. Reuse the single
# generic helper instead.
local_zip = '''  zipWithV : ∀ {A B C n} → (A → B → C) → Vec A n → Vec B n → Vec C n
  zipWithV _ [] [] = []
  zipWithV f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithV f xs ys
'''
s = s.replace(local_zip, '')

# Once local helper declarations are removed, empty vAdd/vHadamard `where`
# blocks can remain in some source revisions. Eliminate only those blocks.
s = re.sub(
    r'(vAdd\s*\{S\}\s*=\s*zipWithV\s*\([^\n]+\))\n\s*where\n(?=\nvSub\s*:)',
    r'\1\n\n', s, count=1)
s = re.sub(
    r'(vHadamard\s*\{S\}\s*=\s*zipWithV\s*\([^\n]+\))\n\s*where\n(?=\nvSum\s*:)',
    r'\1\n\n', s, count=1)

# vSub keeps its carrier-local arithmetic helper. Ensure the helper itself has
# a type signature, which Agda requires after the generic zipWithV dedupe.
sub_anchor = 'vSub {S} = zipWithV sub\n  where\n'
if sub_anchor in s:
    pos = s.index(sub_anchor) + len(sub_anchor)
    rest = s[pos:]
    local_block = rest.split('\n------------------------------------------------------------------------', 1)[0]
    if '  sub : Scalar S → Scalar S → Scalar S\n' not in local_block:
        m = re.match(
            r'(\s*Rg\s*=\s*[^\n]+\n)\s*(sub\s+x\s+y\s*=\s*[^\n]+\n)',
            rest,
        )
        if not m:
            raise SystemExit('vSub local sub declaration shape not found')
        body = m.group(2).split('sub x y =', 1)[1].rstrip('\n')
        old = m.group(0)
        new = m.group(1) + '  sub : Scalar S → Scalar S → Scalar S\n  sub x y = ' + body + '\n'
        s = s[:pos] + rest.replace(old, new, 1)
else:
    raise SystemExit('vSub canonical declaration not found')

# The legacy LayerNorm surface defined layerNormVariance as the supplied
# epsilon. After that surface is removed, preserve the same finite-algebra
# semantic as one top-level helper matching the canonical (xs, epsilon) call.
variance_decl = '''layerNormVariance : ∀ {S d} → VecS S d → Scalar S → Scalar S
layerNormVariance _ eps = eps

'''
if 'layerNormVariance : ∀ {S d}' not in s:
    insertion = s.find('-- Domain-carrying recurrent LayerNorm boundary')
    if insertion < 0:
        insertion = s.find('record LayerNorm')
    if insertion < 0:
        raise SystemExit('LayerNorm boundary not found for variance helper insertion')
    s = s[:insertion] + variance_decl + s[insertion:]

if s.count(record) != 1:
    raise SystemExit(f'SmoothAlgebra definition count is {s.count(record)}, expected 1')
if s.count('matVec :') != 1:
    raise SystemExit(f'matVec definition count is {s.count("matVec :")}, expected 1')
if s.count('matMul :') != 1:
    raise SystemExit(f'matMul definition count is {s.count("matMul :")}, expected 1')
if s.count('tabulateV :') != 1:
    raise SystemExit(f'tabulateV helper count is {s.count("tabulateV :")}, expected 1')
if s.count('zipWithV :') != 1:
    raise SystemExit(f'zipWithV definition count is {s.count("zipWithV :")}, expected 1')
if s.count('layerNormVariance :') != 1:
    raise SystemExit(f'layerNormVariance definition count is {s.count("layerNormVariance :")}, expected 1')
if 'vAdd {S} = zipWithV (Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)))\n  where\n' in s:
    raise SystemExit('empty vAdd where block remains')
p.write_text(s)
print('canonical algebra helper scope normalized: one zipWithV, typed sub, preserved layerNormVariance')