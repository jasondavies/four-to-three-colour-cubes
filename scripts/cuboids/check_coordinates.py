#!/usr/bin/env python3
"""Independent coordinate and arithmetic audit of the cuboid paper.

No repository modules, generated tables, Lean artifacts or third-party packages
are imported. These finite checks audit the proof's interfaces; they are not an
exhaustive inventory proof or a substitute for the symbolic argument.
"""

from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
import json


def cross(x, y):
    return (
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    )


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def cyclic(q):
    return min(q, q[1:] + q[:1], q[2:] + q[:2])


def corners(t):
    out = Counter()
    for bits in product((0, 1), repeat=3):
        faces = [2 * j + bits[j] for j in range(3)]
        if sum(bits) % 2:
            faces[1], faces[2] = faces[2], faces[1]
        out[cyclic(tuple(t[f] for f in faces))] += 1
    return out


def edges(t):
    return {
        tuple(sorted((t[f], t[g])))
        for f, g in combinations(range(6), 2)
        if f // 2 != g // 2
    }


def check_geometry():
    vectors = ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1))
    rotations = []
    for x in vectors:
        for y in vectors:
            if dot(x, y):
                continue
            z = cross(x, y)
            rotations.append(tuple(
                vectors.index(tuple(v[0] * x[j] + v[1] * y[j] + v[2] * z[j] for j in range(3)))
                for v in vectors
            ))
    assert len(set(rotations)) == 24

    def canonical(t):
        return min(tuple(t[j] for j in r) for r in rotations)

    sources = sorted({canonical(t) for t in product(range(4), repeat=6) if len(set(t)) == 4})
    assert len(sources) == 68
    support = {t: set(corners(t)) for t in sources}
    edge_support = {t: edges(t) for t in sources}
    minimal = [t for t in sources if not any(support[u] < support[t] for u in sources)]
    assert len(minimal) == 38
    for t in sources:
        replacements = [u for u in minimal if support[u] <= support[t]]
        assert replacements
        assert all(edge_support[u] <= edge_support[t] for u in replacements)
    ordinary = [t for t in minimal if any(len(set(k)) < 3 for k in support[t])]
    checkers = [t for t in minimal if all(len(set(k)) == 3 for k in support[t])]
    assert len(ordinary) == 32 and len(checkers) == 6
    signatures = Counter(frozenset(k for k in support[t] if len(set(k)) == 3) for t in ordinary)
    assert sorted(signatures.values()) == [16, 16]
    pairs = set(combinations(range(4), 2))
    for t in ordinary:
        assert pairs <= edge_support[t]
    for t in checkers:
        missing = pairs - edge_support[t]
        assert len(missing) == 1
        pair = next(iter(missing))
        assert {frozenset(k) for k in support[t]} == {
            frozenset(k) for k in combinations(range(4), 3) if not set(pair) <= set(k)
        }

    demand_checks = shape_count = 0
    for shape in combinations_with_replacement(range(2, 10), 3):
        # Exposed faces are obtained by visiting actual unit-cube positions.
        frame = Counter()
        face_only = 0
        for p in product(*(range(n) for n in shape)):
            fs = tuple(
                2 * j + side
                for j in range(3) for side in (0, 1)
                if p[j] == (shape[j] - 1 if side == 0 else 0)
            )
            if len(fs) >= 2:
                frame[fs] += 1
            else:
                face_only += 1
        a, b, c = shape
        m, t, q = a - 2, b - 2, c - 2
        assert sum(frame.values()) == 4 * (a + b + c) - 16
        assert sum(frame.values()) + face_only == a * b * c
        shape_count += 1
        for u, v, w in permutations(range(4), 3):
            for name, target, expected in (
                ("Q", (v, w, u, u, u, u), Counter({
                    (u, u): 4 * m,
                    tuple(sorted((u, v))): 2 * t + 2 * q,
                    tuple(sorted((u, w))): 2 * t + 2 * q,
                })),
                ("H", (v, w, u, u, u, v), Counter({
                    (u, u): 2 * m,
                    (v, v): t,
                    tuple(sorted((u, v))): 2 * m + t + 2 * q,
                    tuple(sorted((u, w))): t + 2 * q,
                    tuple(sorted((v, w))): t,
                })),
            ):
                actual = Counter()
                for fs, n in frame.items():
                    if len(fs) == 2:
                        actual[tuple(sorted(target[f] for f in fs))] += n
                assert +actual == +expected, (shape, target, actual, expected)
                if name == "H":
                    expected_corners = Counter({
                        cyclic((u, u, v)): 2, cyclic((u, u, w)): 2,
                        cyclic((u, v, v)): 2, cyclic((u, v, w)): 1,
                        cyclic((u, w, v)): 1,
                    })
                    assert corners(target) == expected_corners
                demand_checks += 1
    return {
        "proper_rotations": 24,
        "source_varieties": 68,
        "minimal_varieties": 38,
        "ordinary_classes": [16, 16],
        "coordinate_shapes": shape_count,
        "Q_H_coordinate_demand_checks": demand_checks,
    }


def check_arithmetic():
    shape_count = 0
    for a in range(2, 31):
        for b in range(a, 51):
            for c in range(b, 101):
                L = 4 * (a + b + c) - 16
                K = (24 * c - 1) // 5
                # This is the weaker assumption in the weighted lemma itself,
                # rather than the stronger assumption N >= 16*a - 3.
                N = max(29, L, K)
                sa, sb, sc = N - 4 * a, N - 4 * b, N - 4 * c
                assert sc >= 5 and N <= 6 * sc + 5
                assert sb >= max(7, 2 * b - 1)
                assert sa >= 4 * b - 1
                assert sc >= (4 * b - 1) // 3
                F = max(16 * a - 3, L, K)
                G = max(a * b * c, 16 * a - 3, K)
                assert (F == L) == (b + c >= 3 * a + 4 and c <= 5 * (a + b) - 19)
                assert (G == a * b * c) == (b >= 3 and (b >= 4 or c >= 5))
                assert a * b * c >= L
                assert F >= 4 * a + 2 * b + 2 * c - 5
                shape_count += 1

    states = exceptional = 0
    for a in range(2, 5):
        h = 4 * a - 1
        for b in range(a, (3 * a + 4) // 2 + 1):
            for c in range(b, 3 * a + 5 - b):
                N = max(16 * a - 3, 4 * (a + b + c) - 16, (24 * c - 1) // 5)
                if N > 16 * a + 2:
                    continue
                for counts in product(range(h + 1), repeat=4):
                    T = sum(counts)
                    if T < 16 * a - 14:
                        continue
                    for M in range(1, 7):
                        A = N - M
                        P = A - T
                        if P < 0 or T + 2 * P > 4 * h:
                            continue
                        states += 1
                        assert max(counts) >= 2 * a
                        assert A > 2 * a + b
                        if sum(t < b for t in counts) >= 2:
                            exceptional += 1
                            assert a == 2 and b <= 4 and M >= 5
                            assert sum(t >= 4 for t in counts) >= 2
    return {
        "arithmetic_shapes": shape_count,
        "reservation_split_numerical_states": states,
        "reservation_split_exceptional_states": exceptional,
    }


if __name__ == "__main__":
    print(json.dumps({
        "status": "passed",
        "scope": "Finite independent geometry/arithmetic checks, not an exhaustive inventory theorem.",
        "geometry": check_geometry(),
        "arithmetic": check_arithmetic(),
    }, indent=2))
