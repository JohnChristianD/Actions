from pathlib import Path

path = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
lines = path.read_text().splitlines(keepends=True)
out = []
i = 0
q = False
acc = False
while i < len(lines):
    line = lines[i]
    stripped = line.strip()
    if stripped == 'initialForm : QRun_v142.projection' and i + 1 < len(lines):
        nxt = lines[i + 1].strip()
        if nxt.startswith('(initialQRun_v142 D budget p x)') and nxt.endswith('≡ p ='):
            indent = line[:len(line) - len(line.lstrip())]
            out.append(f'{indent}initialForm =\n')
            i += 2
            q = True
            continue
    if 'accumulate i c (state s) = state (λ j with finDecEq j i' in line:
        indent = line[:len(line) - len(line.lstrip())]
        out.extend([
            f'{indent}accumulateAt : Fin n → R → Cot → Fin n → R\n',
            f'{indent}accumulateAt i c s j with finDecEq j i\n',
            f'{indent}... | yes _ = s j + c\n',
            f'{indent}... | no _ = s j\n',
            '\n',
            f'{indent}accumulate i c (state s) = state (λ j → accumulateAt i c s j)\n',
        ])
        i += 1
        while i < len(lines) and ('... | yes _ = s j + c' in lines[i] or '... | no _ = s j' in lines[i]):
            i += 1
        acc = True
        continue
    out.append(line)
    i += 1

text = ''.join(out)

# Canonical repair removes the old pre-retraction KKT placeholder. Recreate
# the intended fixed-point theorem only after qProjectionRetraction_v147 has
# been defined, avoiding a forward dependency.
fixed = False
if 'qProjectionFixedPoint_v147 :' not in text:
    anchor = '\nqRunTerminalKKT_v147 :'
    pos = text.find(anchor)
    if pos >= 0:
        replacement = '''
qProjectionFixedPoint_v147 : ∀ {S n}
  (D : QProjectionDecisionAlgebra_v140 S)
  (budget : Scalar S)
  (p x : VecS S n) →
  (∀ i → zero ≤ indexV p i) →
  weightedExposure_v147 p x ≤ budget →
  QRun_v142.projection (qRun_v142 D budget p x) ≡ p
qProjectionFixedPoint_v147 = qProjectionRetraction_v147
'''
        text = text[:pos] + replacement + text[pos:]
        fixed = True
else:
    fixed = True

marker = 'qTerminalProjectionUnique_v147 t u ha hx hmu ='
start = text.find(marker)
terminal = False
if start >= 0:
    sep = text.find('\n------------------------------------------------------------------------', start)
    if sep >= 0:
        replacement = '''qTerminalProjectionUnique_v147 t u ha hx hmu =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (trans
        (cong
          (λ a → SmoothAlgebra.max _ zero
            (qResidual_v142
              (QTerminalSolution_v147.multiplier t)
              (indexV a i)
              (indexV (QTerminalSolution_v147.x t) i *
               (indexV (QTerminalSolution_v147.x t) i))))
          (cong (λ v → indexV v i) ha))
        (trans
          (cong
            (λ m → SmoothAlgebra.max _ zero
              (qResidual_v142 m
                (indexV (QTerminalSolution_v147.alpha u) i)
                (indexV (QTerminalSolution_v147.x t) i *
                 (indexV (QTerminalSolution_v147.x t) i))))
            hmu)
          (trans
            (cong
              (λ v → SmoothAlgebra.max _ zero
                (qResidual_v142
                  (QTerminalSolution_v147.multiplier u)
                  (indexV (QTerminalSolution_v147.alpha u) i)
                  (indexV v i * indexV v i)))
              hx)
            (sym (QTerminalSolution_v147.stationarity u i))))))

qTerminalConfluence_v147 : ∀ {S n}
  (t u : QTerminalSolution_v147 S n) →
  QTerminalSolution_v147.alpha t ≡ QTerminalSolution_v147.alpha u →
  QTerminalSolution_v147.x t ≡ QTerminalSolution_v147.x u →
  QTerminalSolution_v147.multiplier t ≡ QTerminalSolution_v147.multiplier u →
  QTerminalSolution_v147.projection t ≡ QTerminalSolution_v147.projection u
qTerminalConfluence_v147 = qTerminalProjectionUnique_v147
'''
        text = text[:start] + replacement + text[sep:]
        terminal = True

if not q:
    raise SystemExit('q-retraction multiline declaration not found')
if not terminal:
    raise SystemExit('q-terminal uniqueness declaration not found')
if not fixed:
    raise SystemExit('q fixed-point declaration could not be placed after retraction')

path.write_text(text)
print(f'q-retraction-normalized={q}; accumulate-normalized={acc}; fixed-point-normalized={fixed}; terminal-uniqueness-normalized={terminal}; confluence-restored=True')
