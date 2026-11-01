#!/usr/bin/env python3
"""Hall-obstruction optimisation for coloured-cube corner solutions.

Python generates the finite geometry and model; OR-Tools' compiled CP-SAT
backend does the search, with multiple workers. Repeated varieties are allowed.
Faces are +x,-x,+y,-y,+z,-z. Interior faces are unrestricted.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import time

from ortools.sat.python import cp_model
from cube_geometry import canonical, corners


def varieties(palette, used):
    return sorted({canonical(c) for c in itertools.product(range(palette), repeat=6)
                   if len(set(c)) == used})


def obstructions(cubes, target):
    """All maximal Hall-deficiency alternatives, with a representative slot mask.

    A collection x fails iff, for some nonempty set S of target slots,
    sum(x[c] for c adjacent to S) <= |S|-1. For a fixed neighbourhood keep
    the largest |S|. A smaller neighbourhood with at least that RHS subsumes
    an alternative, so the latter may also be discarded.
    """
    available = [set(corners(c)) for c in cubes]
    neighbourhoods = [sum(1 << i for i, cs in enumerate(available) if k in cs)
                      for k in corners(target)]
    masks = [0] * 256
    best = {}
    for s in range(1, 256):
        low = s & -s
        masks[s] = masks[s ^ low] | neighbourhoods[low.bit_length() - 1]
        rhs = s.bit_count() - 1
        if masks[s] not in best or best[masks[s]][0] < rhs:
            best[masks[s]] = (rhs, s)
    result = []
    for n, (rhs, s) in best.items():
        if any(m != n and m & n == m and r >= rhs
               for m, (r, _) in best.items()):
            continue
        result.append((n, rhs, s))
    return result


def solve(palette, target_colours, seconds, workers, output, seed=1,
          minimal=False, size=None, hint=None, exclude_colour_orbit=None):
    started = time.monotonic()
    cubes = varieties(palette, palette)
    if minimal:
        sets = [set(corners(c)) for c in cubes]
        cubes = [c for c, cs in zip(cubes, sets) if not any(ds < cs for ds in sets)]
    targets = varieties(palette, target_colours)
    # This is also checked when target_colours differs from the source palette:
    # eight copies of any variety must build at least one permitted target.
    target_sets = [set(corners(t)) for t in targets]
    if not all(any(ts <= set(corners(c)) for ts in target_sets) for c in cubes):
        raise ValueError('Eight-copy bound does not hold for this target family')
    model = cp_model.CpModel()
    counts = [model.new_int_var(0, 7, f'x{i}') for i in range(len(cubes))]
    if minimal and palette == 4 and target_colours == 3:
        # Every cube in a monochrome-edge bucket has at least two of the
        # three possible corners aab. Eight such cubes can match four aab
        # and four aac slots for some b != c: there are at least 16 corner
        # incidences, hence two types each supported by at least four cubes.
        # Each cube supports their union. Hall's theorem completes the match.
        for a in range(4):
            bucket = []
            for i, c in enumerate(cubes):
                cc = set(corners(c))
                third = {b for b in range(4) if b != a and
                         min((a,a,b),(a,b,a),(b,a,a)) in cc}
                if third:
                    if len(third) < 2:
                        raise ValueError('Bucket lemma hypothesis failed')
                    bucket.append(counts[i])
            model.add(sum(bucket) <= 7)
    alternatives = [obstructions(cubes, t) for t in targets]
    for t, options in enumerate(alternatives):
        selectors = []
        for j, (n, rhs, _) in enumerate(options):
            b = model.new_bool_var(f'h{t}_{j}')
            model.add(sum(counts[i] for i in range(len(cubes)) if n >> i & 1)
                      <= rhs).only_enforce_if(b)
            selectors.append(b)
        model.add_bool_or(selectors)
    if size is None:
        model.maximize(sum(counts))
    else:
        model.add(sum(counts) == size)
    if hint:
        data = json.loads(Path(hint).read_text())
        hint_counts = {tuple(e['faces']): e['count'] for e in data['collection']}
        for c, x in zip(cubes, counts):
            model.add_hint(x, hint_counts.get(c, 0))
    excluded = set()
    if exclude_colour_orbit:
        data = json.loads(Path(exclude_colour_orbit).read_text())
        index = {c: i for i, c in enumerate(cubes)}
        for perm in itertools.permutations(range(palette)):
            vector = [0] * len(cubes)
            for e in data['collection']:
                c = canonical(tuple(perm[a] for a in e['faces']))
                vector[index[c]] += e['count']
            excluded.add(tuple(vector))
        model.add_forbidden_assignments(counts, sorted(excluded))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = seed
    print(json.dumps({'cubes': len(cubes), 'targets': len(targets),
                      'hall_alternatives': sum(map(len, alternatives)),
                      'setup_seconds': time.monotonic() - started}), flush=True)
    status = solver.solve(model)
    result = dict(palette=palette, target_colours=target_colours,
                  status=solver.status_name(status), source_varieties=len(cubes),
                  target_varieties=len(targets), seed=seed, workers=workers,
                  minimal_sources=minimal, requested_size=size,
                  excluded_collections=len(excluded),
                  limit_seconds=seconds, search_seconds=solver.wall_time,
                  upper_bound=solver.best_objective_bound if size is None else None,
                  branches=solver.num_branches, conflicts=solver.num_conflicts,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        x = [solver.value(c) for c in counts]
        certificates = []
        for t, options in zip(targets, alternatives):
            for n, rhs, s in options:
                neighbours = sum(x[i] for i in range(len(cubes)) if n >> i & 1)
                if neighbours <= rhs:
                    certificates.append(dict(target=t, slot_mask=s,
                                             demand=s.bit_count(), neighbours=neighbours))
                    break
            else:
                raise ValueError('Reported solution lacks a Hall certificate')
        result.update(size=sum(x), collection=[dict(faces=c, count=k)
                                              for c, k in zip(cubes, x) if k],
                      hall_certificates=certificates)
    Path(output).parent.mkdir(parents=True, exist_ok=True)
    Path(output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('hall_certificates', 'collection')}), flush=True)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--palette', type=int, choices=range(2, 7), required=True)
    parser.add_argument('--target-colours', type=int)
    parser.add_argument('--seconds', type=float, default=60)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--minimal', action='store_true')
    parser.add_argument('--size', type=int)
    parser.add_argument('--hint')
    parser.add_argument('--exclude-colour-orbit')
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    solve(args.palette, args.target_colours or args.palette, args.seconds,
          args.workers, args.output, args.seed, args.minimal, args.size, args.hint,
          args.exclude_colour_orbit)
