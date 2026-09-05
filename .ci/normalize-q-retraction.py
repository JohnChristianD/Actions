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
marker = 'qTerminalProjectionUnique_v147 t u ha hx hmu ='
start = text.find(marker)
terminal = False
if start >= 0:
    sep = text.find('\n------------------------------------------------------------------------', start)
    if sep >= 0:
        replacement = '''qTerminalProjectionUnique_v147 t u refl refl refl =
  vectorExt_v147 (λ i →
    trans
      (QTerminalSolution_v147.stationarity t i)
      (sym (QTerminalSolution_v147.stationarity u i)))
'''
        text = text[:start] + replacement + text[sep:]
        terminal = True

if not q:
    raise SystemExit('q-retraction multiline declaration not found')
if not terminal:
    raise SystemExit('q-terminal uniqueness declaration not found')

path.write_text(text)
print(f'q-retraction-normalized={q}; accumulate-normalized={acc}; terminal-uniqueness-normalized={terminal}')
