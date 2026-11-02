#!/usr/bin/env python3
"""Independent geometric audit of the 29-cube theorem and its lower witness.

Uses physical quarter-turns, not the search program's rotation/corner helpers.
No CP-SAT dependency. This is a finite audit, not a formal proof certificate
for CP-SAT optimality; the upper bound has a separate written proof.
"""
from collections import Counter
import itertools
import json
from pathlib import Path
import random
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rotations():
    group = {tuple(range(6))}
    todo = list(group)
    while todo:
        p = todo.pop()
        for g in ((0, 1, 5, 4, 2, 3), (3, 2, 0, 1, 4, 5)):
            q = tuple(p[i] for i in g)
            if q not in group:
                group.add(q)
                todo.append(q)
    require(len(group) == 24, 'Quarter turns did not generate 24 rotations')
    return sorted(group)


ROT = rotations()
SLOTS = list(itertools.product((0, 1), repeat=3))
FACES = [tuple(2 * a + s[a] for a in range(3)) for s in SLOTS]


def canonical(c):
    return min(tuple(c[i] for i in r) for r in ROT)


def corner_types(c):
    result = []
    for signs, faces in zip(SLOTS, FACES):
        k = tuple(c[f] for f in faces)
        if sum(signs) % 2:
            k = (k[0], k[2], k[1])
        result.append(min(k, k[1:] + k[:1], k[2:] + k[:2]))
    return result


def printed_table_rows(manuscript, label):
    """Read the simple tabular format used by the two geometric tables."""
    tables = [table for table in re.findall(
        r'\\begin\{table\}.*?\\end\{table\}', manuscript, re.S)
        if rf'\label{{{label}}}' in table]
    require(len(tables) == 1, f'Expected one printed table labelled {label}')
    tabular = re.search(
        r'\\begin\{tabular\}\{[^}]*\}(.*?)\\end\{tabular\}', tables[0], re.S)
    require(tabular is not None, f'Missing tabular in {label}')
    body = re.sub(r'\\(?:toprule|midrule|bottomrule)\b', '', tabular.group(1))
    rows = [row.strip() for row in body.split(r'\\') if row.strip()]
    require(len(rows) > 1, f'Missing printed rows in {label}')
    return [[cell.strip() for cell in row.split('&')] for row in rows[1:]]


def check_printed_tables(manuscript, reduction_table):
    """Compare printed entries with the independently checked geometry."""
    retained_types = {'001123': 'checkerboard $C$', '010203': 'triple-corner $T$',
                      '010213': 'pair type $P$', '010223': 'pair type $P$'}
    expected = [[f'${word}$', str(size), retained_types[word] if retained else '---',
                 '---' if retained else '$001123$']
                for word, size, retained in reduction_table]
    rows = printed_table_rows(manuscript, 'tab:reduction')
    require(sorted(rows) == sorted(expected), 'Printed reduction table disagrees with geometry')

    rows = printed_table_rows(manuscript, 'tab:corners')
    expected_words = {word for word, _, retained in reduction_table if retained}
    require(len(rows) == len(expected_words), 'Wrong number of printed corner-table rows')
    seen = set()
    for row in rows:
        require(len(row) == 2, 'Malformed printed corner-table row')
        word = re.fullmatch(r'\$([0-3]{6})\$', row[0])
        entries = re.fullmatch(r'\$\\\{([0-3,\s]+)\\\}\$', row[1])
        require(word is not None and entries is not None, 'Malformed printed corner-table entry')
        word = word.group(1)
        require(word in expected_words and word not in seen,
                f'Unexpected or duplicate printed representative: {word}')
        seen.add(word)
        triples = [entry.strip() for entry in entries.group(1).split(',')]
        require(all(re.fullmatch(r'[0-3]{3}', triple) for triple in triples),
                f'Malformed printed corner type for {word}')
        require(len(triples) == len(set(triples)), f'Duplicate printed corner type for {word}')
        actual = {''.join(map(str, k)) for k in corner_types(tuple(map(int, word)))}
        require(set(triples) == actual, f'Printed corner types disagree with geometry for {word}')
    return len(rows)


def fits(cubes, targets):
    oriented = [[{tuple(c[r[f]] for f in faces) for r in ROT}
                 for faces in FACES] for c in cubes]
    return [[[i for i in range(len(cubes))
              if tuple(t[f] for f in faces) in oriented[i][s]]
             for s, faces in enumerate(FACES)] for t in targets]


def restricted_target_families(targets):
    """Check the Q, R and D families used in the restricted-target corollary."""
    cyclic = lambda k: min(k, k[1:] + k[:1], k[2:] + k[:2])
    families = {name: set() for name in ('Q', 'R', 'D')}
    for a, b, c in itertools.permutations(range(4), 3):
        q = (a, a, a, a, b, c)
        r = (b, a, c, a, a, a)
        d = (a, a, b, b, c, c)
        require(Counter(corner_types(q)) == Counter({cyclic((a,a,b)): 4,
                                                    cyclic((a,a,c)): 4}), 'Q corner multiset')
        require(Counter(corner_types(r)) == Counter({(a,a,a): 2,
                    cyclic((a,a,b)): 2, cyclic((a,a,c)): 2,
                    cyclic((a,b,c)): 1, cyclic((a,c,b)): 1}), 'R corner multiset')
        require(Counter(corner_types(d)) == Counter({cyclic((a,b,c)): 4,
                                                    cyclic((a,c,b)): 4}), 'D corner multiset')
        for name, cube in (('Q', q), ('R', r), ('D', d)):
            families[name].add(canonical(cube))
    require({name: len(ts) for name, ts in families.items()} == {'Q':12, 'R':12, 'D':4},
            'Wrong restricted target family sizes')
    require(len(set.union(*families.values())) == 28, 'Target families overlap')
    # Classify all 120 targets by face multiplicities and opposite-face geometry.
    classified = {name: set() for name in families}
    for t in targets:
        counts = Counter(t)
        if sorted(counts.values()) == [1, 1, 4]:
            a = counts.most_common(1)[0][0]
            f, g = [f for f in range(6) if t[f] != a]
            classified['Q' if f // 2 == g // 2 else 'R'].add(t)
        elif all(t[2*j] == t[2*j+1] for j in range(3)):
            classified['D'].add(t)
    require(families == classified, 'Constructed families disagree with target geometry')
    return families


def match(slots, counts):
    copies = [i for i, n in enumerate(counts) for _ in range(n)]
    adj = [[j for j, i in enumerate(copies) if i in possible] for possible in slots]
    owner = [-1] * len(copies)

    def augment(s, seen):
        for j in adj[s]:
            if j in seen:
                continue
            seen.add(j)
            if owner[j] < 0 or augment(owner[j], seen):
                owner[j] = s
                return True
        return False
    return all(augment(s, set()) for s in range(len(slots)))


def main():
    cubes = sorted({canonical(c) for c in itertools.product(range(4), repeat=6)
                    if len(set(c)) == 4})
    targets = sorted({canonical(c) for c in itertools.product(range(4), repeat=6)
                      if len(set(c)) == 3})
    require((len(cubes), len(targets)) == (68, 120), 'Wrong geometric variety counts')
    slots = fits(cubes, targets)
    cs = [set(corner_types(c)) for c in cubes]
    for t, ss in zip(targets, slots):
        for k, possible in zip(corner_types(t), ss):
            require(possible == [i for i, c in enumerate(cs) if k in c],
                    'Cyclic corners disagree with physical orientations')
    minimal = [i for i, c in enumerate(cs) if not any(d < c for d in cs)]
    require(len(minimal) == 38, 'Wrong minimal source count')
    require(all(any(cs[j] <= c for j in minimal) for c in cs),
            'Minimal replacement failed')
    reduction_table = [('000123',12,False), ('001123',6,True),
                       ('001213',12,False), ('010123',6,False),
                       ('010203',8,True), ('010213',12,True),
                       ('010223',12,True)]
    covered = set()
    arrangements = Counter()
    for word, size, retained in reduction_table:
        c = tuple(map(int, word))
        multiplicities = Counter(c)
        opposite = {c[2*j] for j in range(3) if c[2*j] == c[2*j+1]}
        if max(multiplicities.values()) == 3:
            arrangements['triple_opposite' if opposite else 'triple_corner'] += 1
        else:
            arrangements[{0: 'two_adjacent_pairs', 1: 'one_opposite_pair',
                          2: 'two_opposite_pairs'}[len(opposite)]] += 1
        orbit = {canonical(tuple(p[a] for a in c))
                 for p in itertools.permutations(range(4))}
        require(len(orbit) == size and not (orbit & covered), 'Reduction table orbit')
        covered |= orbit
        require((cubes.index(c) in minimal) == retained, 'Reduction table type')
        if not retained:
            require(set(corner_types((0,0,1,1,2,3))) <= set(corner_types(c)),
                    'Printed replacement does not preserve corner containment')
    require(covered == set(cubes), 'Reduction table is incomplete')
    require(arrangements == {'triple_corner':1, 'triple_opposite':1,
                            'two_opposite_pairs':1, 'one_opposite_pair':1,
                            'two_adjacent_pairs':3}, 'Wrong source arrangement cases')
    manuscript = (Path(__file__).resolve().parents[1] /
                  'paper/four-to-three-colour-cubes.tex').read_text()
    printed_corner_rows = check_printed_tables(manuscript, reduction_table)
    plus = {(0, 1, 2), (0, 3, 1), (0, 2, 3), (1, 3, 2)}
    minus = {min((a,c,b), (c,b,a), (b,a,c)) for a,b,c in plus}
    categories = Counter()
    for i in minimal:
        c = cubes[i]
        triple = {k for k in cs[i] if len(set(k)) == 3}
        same_edges = {a for a in range(4) if any(k.count(a) >= 2 for k in cs[i])}
        if not same_edges:
            categories['C'] += 1
            require(all(c[2*j] == c[2*j+1] for j in range(3)
                        if Counter(c)[c[2*j]] == 2), 'Checkerboard opposite pairs')
            triples = {tuple(sorted(k)) for k in triple}
            require(len(triples) == 2 and len(triple) == 4,
                    'Checkerboard triple/orientation counts')
            repeated = {a for a, n in Counter(c).items() if n == 2}
            require(triples == {tuple(sorted(repeated | {a})) for a in range(4)
                                if a not in repeated}, 'Checkerboard supports wrong triples')
            continue
        require(triple in (plus, minus), 'Ordinary cube has wrong orientation class')
        categories['plus' if triple == plus else 'minus'] += 1
        if max(Counter(c).values()) == 3:
            categories['T'] += 1
            require(len(same_edges) == 1, 'T cube has wrong buckets')
            a = next(iter(same_edges))
            require((a,a,a) in cs[i], 'T cube lacks monochrome corner')
            require(all(min((a,a,b),(a,b,a),(b,a,a)) in cs[i]
                        for b in range(4) if b != a), 'T cube lacks aab')
        else:
            categories['P'] += 1
            require(len(same_edges) == 2, 'P cube has wrong buckets')
            for a in same_edges:
                require(sum(min((a,a,b),(a,b,a),(b,a,a)) in cs[i]
                            for b in range(4) if b != a) == 2,
                        'P cube must have two third colours per bucket')
    require(categories == {'T':8, 'P':24, 'C':6, 'plus':16, 'minus':16},
            'Wrong structural class counts')

    # Every target with a trichrome corner requires both orientations.
    # A target without one has four a faces and two opposite minority faces.
    no_trichrome = 0
    for t in targets:
        ct = Counter(corner_types(t))
        for k, n in ct.items():
            if len(set(k)) == 3:
                a,b,c = k
                require(ct[min((a,c,b),(c,b,a),(b,a,c))] == n,
                        'Three-colour target chirality imbalance')
        if not any(len(set(k)) == 3 for k in ct):
            no_trichrome += 1
            a = Counter(t).most_common(1)[0][0]
            minority = [f for f in range(6) if t[f] != a]
            require(len(minority) == 2 and minority[0] // 2 == minority[1] // 2,
                    'Wrong form of target without trichrome corners')
    require(no_trichrome == 12, 'Wrong number of no-trichrome targets')
    families = restricted_target_families(targets)
    restricted_targets = set.union(*families.values())
    restricted_slots = [ss for t, ss in zip(targets, slots) if t in restricted_targets]

    path = (Path(__file__).resolve().parents[1] / 'data/lower-obstruction.json')
    data = json.loads(path.read_text())
    counts = [0] * len(cubes)
    for e in data['collection']:
        counts[cubes.index(tuple(e['faces']))] += e['count']
    require(sum(counts) == 28, 'Lower witness has wrong size')
    require(all(not match(ss, counts) for ss in slots), '28-cube witness has a solution')
    orbit = set()
    for perm in itertools.permutations(range(4)):
        x = [0] * len(cubes)
        for c, n in zip(cubes, counts):
            if n:
                x[cubes.index(canonical(tuple(perm[a] for a in c)))] += n
        orbit.add(tuple(x))
    require(len(orbit) == 2, 'Expected two labelled lower obstructions')
    for x in orbit:
        require(all(not match(ss, x) for ss in slots), 'Colour-orbit example has a solution')
    certificates = {tuple(e['target']): e for e in data['hall_certificates']}
    require(set(certificates) == set(targets), 'Certificate target list is incomplete')
    for t, ss in zip(targets, slots):
        cert = certificates[t]
        s = cert['slot_mask']
        neighbours = set().union(*(set(ss[j]) for j in range(8) if s >> j & 1))
        actual = sum(counts[i] for i in neighbours)
        require(0 < s < 256 and actual < s.bit_count(), 'Invalid Hall deficiency')
        require(actual == cert['neighbours'] and s.bit_count() == cert['demand'],
                'Hall certificate counts disagree')

    # A small independent sanity check of the upper bound, including all
    # one-cube extensions of the tight example. The proof covers all multisets.
    for i in range(len(cubes)):
        counts[i] += 1
        require(any(match(ss, counts) for ss in restricted_slots),
                'One-cube extension has no Q, R or D solution')
        counts[i] -= 1
    rng = random.Random(29)
    for _ in range(1000):
        support = rng.sample(range(68), rng.randint(1, 15))
        x = [0] * 68
        for _ in range(29):
            x[rng.choice(support)] += 1
        require(any(match(ss, x) for ss in restricted_slots),
                'Random 29-cube inventory has no Q, R or D solution')
        x[next(i for i, n in enumerate(x) if n)] -= 1
        if not any(match(ss, x) for ss in restricted_slots):
            require(not any(match(ss, x) for ss in slots),
                    'Solvable 28-cube inventory has no Q, R or D solution')
    result = dict(varieties=68, targets=120, minimal_varieties=38,
                  printed_reduction_rows_checked=len(reduction_table),
                  printed_corner_rows_checked=printed_corner_rows,
                  source_arrangement_orbits=dict(arrangements),
                  restricted_target_varieties={name: len(ts) for name, ts in families.items()},
                  classes=dict(categories), lower_bound_size=28,
                  exhibited_labelled_lower_obstructions=2,
                  lower_bound_targets_checked=120, one_cube_extensions_checked=68,
                  random_29_cube_collections_checked=1000,
                  random_28_cube_collections_checked=1000,
                  status='all checks passed',
                  scope='Independent finite geometric audit; upper bound proved in the note')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
