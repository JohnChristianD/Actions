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

# Once local helper declarations are removed, an empty vAdd `where` remains
# in some source revisions. Eliminate only the known empty block.
s = re.sub(
    r'(vAdd\s*\{S\}\s*=\s*zipWithV\s*\([^\n]+\))\n\s*where\n(?=\nvSub\s*:)',
    r'\1\n\n',
    s,
    count=1,
)

# vSub keeps its carrier-local arithmetic helper. Ensure the helper itself has
# a type signature, which Agda requires after the generic zipWithV dedupe.
sub_pat = re.compile(
    r'(vSub\s*\{S\}\s*=\s*zipWithV\s+sub\s*\n\s*where\n)'
    r'(\s*Rg\s*=\s*OrderedRing\.ring\s+\(SmoothAlgebra\.orderedRing\s+S\)\s*\n)'
    r'(\s*sub\s+)(x\s+y\s*=\s*Ring\._\+_\s+Rg\s+x\s+\(Ring\.neg\s+Rg\s+y\))',
)
if sub_pat.search(s):
    s = sub_pat.sub(
        r'\1\2  sub : Scalar S → Scalar S → Scalar S\n  sub x y = Ring._+_ Rg x (Ring.neg Rg y)',
        s,
        count=1,
    )
elif '  sub : Scalar S → Scalar S → Scalar S\n  sub x y = Ring._+_ Rg x (Ring.neg Rg y)' not in s:
    # Fall back to the exact declaration line shape after earlier normalizers.
    line_pat = re.compile(
        r'(vSub\s*\{S\}\s*=\s*zipWithV\s+sub\s*\n\s*where\n)'
        r'(\s*Rg\s*=\s*[^\n]+\n)'
        r'\s*sub\s+x\s+y\s*=\s*([^\n]+)'
    )
    m = line_pat.search(s)
    if not m:
        raise SystemExit('vSub local sub declaration shape not found')
    s = s[:m.start()] + m.group(1) + m.group(2) + '  sub : Scalar S → Scalar S → Scalar S\n  sub x y = ' + m.group(3) + s[m.end():]

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
if 'vAdd {S} = zipWithV (Ring._+_ (OrderedRing.ring (SmoothAlgebra.orderedRing S)))\n  where\n' in s:
    raise SystemExit('empty vAdd where block remains')
p.write_text(s)
print('canonical vector helper scope normalized: one global zipWithV, typed sub, no empty vAdd where')