import csv
import sympy as sp

x, h, c = sp.symbols('x h c')
sig = lambda z: 1 / (1 + sp.exp(-z))

i = sig(x + h)
f = sig(x + h)
o = sig(x + h)
g = sp.tanh(x + h)
c2 = sp.simplify(f * c + i * g)
h2 = sp.simplify(o * sp.tanh(c2))

with open('oracle/cases.csv', newline='') as fh:
    for row in csv.DictReader(fh):
        xv = float(row['x'])
        hv = float(row['h'])
        cv = float(row['c'])
        lv = float(h2.evalf(40, subs={x:xv, h:hv, c:cv}))
        lc = float(c2.evalf(40, subs={x:xv, h:hv, c:cv}))
        print(f'{xv:.12f},{hv:.12f},{cv:.12f},{lv:.12f},{lc:.12f}')
