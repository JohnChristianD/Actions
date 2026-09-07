"""Finite algebraic conjecture enumerator.

This is a theorem-candidate generator, not a proof oracle. It deliberately
emits only small, syntax-directed identities that an Agda kernel proof must
still certify before they become theorems.
"""

from itertools import product

DEPTH = 3
ATOMS = ("id", "affine", "layerNorm", "lstmStep", "gruStep")


def compose(a: str, b: str) -> str:
    return f"({b}∘{a})"


def expressions(depth: int) -> tuple[str, ...]:
    levels = {0: ATOMS}
    seen = set(ATOMS)
    for d in range(1, depth + 1):
        current = set(levels[d - 1])
        for x, y in product(levels[d - 1], repeat=2):
            current.add(compose(x, y))
        levels[d] = tuple(sorted(current))
        seen.update(current)
    return tuple(sorted(seen))


def normalize(e: str) -> str:
    changed = True
    while changed:
        changed = False
        for old, new in (
            ("(id∘X)", "X"),
            ("(X∘id)", "X"),
            ("((X∘Y)∘Z)", "(X∘(Y∘Z))"),
        ):
            if old in e:
                e = e.replace(old, new)
                changed = True
    return e


def candidates() -> tuple[str, ...]:
    es = expressions(DEPTH)
    out = {
        "compose(id,f)=f",
        "compose(f,id)=f",
        "compose(compose(f,g),h)=compose(f,compose(g,h))",
        "iterate(0,f)=id",
        "iterate(suc(k),f)=compose(f,iterate(k,f))",
        "reverse(compose(f,g))=compose(reverse(g),reverse(f))",
    }
    # Generate finite architecture-specific shape conjectures.
    for x in es:
        nx = normalize(x.replace("affine", "X").replace("layerNorm", "Y"))
        if nx == x.replace("affine", "X").replace("layerNorm", "Y"):
            continue
        out.add(f"normalize({x})={nx}")
    return tuple(sorted(out))


for line in candidates():
    print(line)
