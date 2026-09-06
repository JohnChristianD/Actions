from pathlib import Path
import re
import sys

TARGET = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')

REQUIRED = {
    'finite-algebra': [
        'Ring', 'OrderedRing', 'SmoothAlgebra',
        'vAdd', 'vSub', 'vScale', 'vHadamard', 'vDot',
        'matVec', 'matMul',
    ],
    'q-projection': [
        'vectorExt_v147',
        'qResidualZero_v147',
        'qCandidateNonnegative_v147',
        'qRunProjectionFormFuel_v147',
        'qRunProjectionForm_v147',
        'qRunProjectionNonnegative_v147',
        'qMuZeroFromNumLe_v147',
        'qFirstNegativeNoneNonnegative_v147',
        'qRunStopsWhenNoNegative_v147',
    ],
    'q-terminal': [
        'qProjectionRetraction_v147',
        'qProjectionFixedPoint_v147',
        'qRunTerminalKKT_v147',
        'cancelPositiveRight_v147',
        'qTerminalMultiplierUnique_v147',
        'QTerminalSolution_v147',
        'qTerminalProjectionUnique_v147',
        'qTerminalConfluence_v147',
        'CompleteAlgebraicClosure_v146',
    ],
}

text = TARGET.read_text()
errors = []

if '{-# OPTIONS --safe #-}' not in text:
    errors.append('missing top-level --safe option')

for forbidden in ('--unsafe', 'primTrustMe', '{!!', '?_'):
    if forbidden in text:
        errors.append(f'forbidden unsafe/incomplete marker present: {forbidden!r}')

for family, names in REQUIRED.items():
    missing = [name for name in names if not re.search(rf'(?<![A-Za-z0-9_]){re.escape(name)}(?![A-Za-z0-9_])', text)]
    if missing:
        errors.append(f'{family}: missing {", ".join(missing)}')
    else:
        print(f'safe-surface={family}:ok:{len(names)}')

print(f'safe-surface-source-bytes={len(text.encode("utf-8"))}')
if errors:
    for error in errors:
        print(f'ERROR: {error}', file=sys.stderr)
    sys.exit(1)

print('safe-surface-audit=ok')
