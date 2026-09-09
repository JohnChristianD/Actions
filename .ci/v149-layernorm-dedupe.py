from pathlib import Path

p = Path('Exotic/ERL/FullCoupled/CompleteSafe_v147.agda')
s = p.read_text()
record = 'record LayerNorm (S : SmoothAlgebra) (d : Nat) : Set where\n'
positions = []
start = 0
while True:
    i = s.find(record, start)
    if i < 0:
        break
    positions.append(i)
    start = i + len(record)

if len(positions) == 1:
    print('layerNorm-dedupe=already-single')
    raise SystemExit(0)
if len(positions) < 1:
    raise SystemExit('no top-level LayerNorm record found')

# Keep the first domain-carrying definition. Remove later duplicate record
# blocks without touching subsequent independent recurrent structures.
second = positions[1]
end = s.find('\nrecord RecurrentAffine (S : SmoothAlgebra) (input hidden : Nat) : Set where', second)
if end < 0:
    raise SystemExit('duplicate LayerNorm terminator at RecurrentAffine not found')
# Include the section separator immediately preceding RecurrentAffine only via
# replacing the duplicate block itself.
s = s[:second] + s[end + 1:]

positions_after = []
start = 0
while True:
    i = s.find(record, start)
    if i < 0:
        break
    positions_after.append(i)
    start = i + len(record)
if len(positions_after) != 1:
    raise SystemExit(f'LayerNorm record count after dedupe is {len(positions_after)}, expected 1')

p.write_text(s)
print('layerNorm-dedupe=one-authoritative-record')
