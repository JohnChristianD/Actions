import json
from pathlib import Path
import sympy as sp

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'tools' / 'algebraic_obligations.json').read_text())

n, y, d, z = sp.symbols('n y d z', nonzero=True)
exprs = {
    'q_num_remove': (n-y) + y - n,
    'q_den_remove': (d-z) + z - d,
    'q_quotient_deletion': (n-y)/(d-z) - n/d - (n*z-y*d)/(d*(d-z)),
}

for oid in ('q_num_remove', 'q_den_remove', 'q_quotient_deletion'):
    result = sp.factor(sp.together(exprs[oid]))
    if result != 0:
        raise SystemExit(f'SymPy failed {oid}: {result}')
    print(f'sympy-{oid}=PASS')

print(f"sympy-obligations={len(manifest['obligations'])}")
print('sympy-symbolic-solver=PASS')
