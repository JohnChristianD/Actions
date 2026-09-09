from fractions import Fraction as Q


def crelu(x):
    return max(Q(0), x), max(Q(0), -x)


def sparsemax(xs):
    u = sorted(xs, reverse=True)
    tau = Q(0)
    for k in range(1, len(xs) + 1):
        candidate = (sum(u[:k]) - Q(1)) / Q(k)
        if k == len(xs) or u[k] <= candidate:
            tau = candidate
            break
    return [max(Q(0), x - tau) for x in xs], tau


def row_l1(row):
    return sum((abs(x) for x in row), Q(0))


def weight_l1(matrix):
    return sum((row_l1(row) for row in matrix), Q(0))


def path1(w1, w2):
    return sum(
        (abs(w2[o][h]) * row_l1(w1[h])
         for o in range(len(w2))
         for h in range(len(w1))),
        Q(0),
    )


def fmt(q):
    q = Q(q)
    return f"{q.numerator}/{q.denominator}"


def main():
    x = Q(-7, 3)
    pos, neg = crelu(x)
    assert pos - neg == x
    assert pos + neg == abs(x)

    scores = [Q(5, 4), Q(3, 4), Q(1, 2)]
    weights, tau = sparsemax(scores)
    assert weights == [Q(3, 4), Q(1, 4), Q(0)]
    assert sum(weights, Q(0)) == Q(1)
    assert all(w >= 0 for w in weights)
    for s, w in zip(scores, weights):
        if w == 0:
            assert s <= tau
        else:
            assert w == s - tau

    w1 = [[Q(1, 2), Q(-1, 3)], [Q(1, 4), Q(1, 5)]]
    w2 = [[Q(2, 3), Q(-3, 4)]]
    l1 = weight_l1(w1)
    p1 = path1(w1, w2)
    assert l1 == Q(77, 60)
    assert p1 == Q(77, 72)

    degrees = [Q(1)]
    for _ in range(4):
        degrees.append(degrees[-1] * 3)
    assert [int(d) for d in degrees] == [1, 3, 9, 27, 81]

    lines = [
        "oracle=python-fraction",
        f"crelu.reconstruct={fmt(pos - neg)}",
        f"crelu.abs={fmt(pos + neg)}",
        f"tsallis.tau={fmt(tau)}",
        "tsallis.weights=" + ",".join(fmt(w) for w in weights),
        f"weight_l1={fmt(l1)}",
        f"path1={fmt(p1)}",
        "degree_sequence=1,3,9,27,81",
        "status=PASS",
    ]
    print("\n".join(lines))


if __name__ == "__main__":
    main()
