# Three-colour solutions from four-colour cubes

- [Paper (PDF)](paper/four-to-three-colour-cubes.pdf) and [LaTeX](paper/four-to-three-colour-cubes.tex).
- [Main Lean results](ThreeColour/FrameResults.lean), [physical model](ThreeColour/FramePhysical.lean), and [formalisation guide](ThreeColour/README.md).
- [Independent theorem statements](Challenge.lean) and [completed proof entry point](Solution.lean).
- [Provenance, scope and AI disclosure](formalization.yaml).

**For every $n\ge4$, any $n^3$ cubes, each painted with all four colours of a
fixed palette, build an $n\times n\times n$ cube with solid faces in exactly
three colours. For $n=2$ and $n=3$ the sharp numbers are 29 and 45.**

Both follow from a frame theorem. A frame is the $12n-16$ corner and edge
pieces of an $n\times n\times n$ cube. For every $n\ge2$, any $16n-3$
four-colour cubes contain a three-colour frame. For a fixed palette, exactly
two collections of $16n-4$ cubes fail: $4n-1$ copies of each of four
varieties in one orientation class, and the mirror image of that collection.
The remaining pieces of a complete cube are easy, since every cube shows
every colour, so the complete-cube threshold is $\max\{n^3,16n-3\}$.

The exterior faces must be monochromatic and use exactly three colours;
internal faces need not match. Collections may repeat varieties, and only
proper rotations are allowed.

| Side length | Frame pieces | Frame threshold | Complete-cube threshold |
| --- | --- | --- | --- |
| 2 | 8 | 29 | 29 |
| 3 | 20 | 45 | 45 |
| 4 | 32 | 61 | 64 |
| 5 | 44 | 77 | 125 |

The case $n=2$ answers the threshold question in Problem 2 of
[Berkove, Eickemeyer and Schulman, *The 4-Color Cubes Puzzle* (2018)](https://math.colgate.edu/~integers/s68/s68.pdf).
The figure shows this first case; the general obstruction replaces seven
copies of each variety by $4n-1$ copies.

![Why the exceptional 28 cubes fail: missing corner orientations, or eight required cubes with only seven available](paper/obstruction-figure.svg)

*Marked vertices are monochromatic corners. In panel B, opposite faces of
the target have equal colours, so its hidden bottom face has colour 2.
In panel C, $a,b,c$ are distinct colours.*

## Proof idea

The proof reduces the 68 varieties to 38 by replacing cubes with varieties
whose corner types are contained in theirs. This preserves unsolvability.
The retained types are triple-corner ($T$), pair-type ($P$), and checkerboard ($C$).
A cube belongs to colour bucket $a$ if it has at least two of the three
corner types $aab$, with $b\ne a$. The examples show one cube of each type;
colour permutations give the other bucket memberships.

![A T cube links to one colour bucket, a P cube to two, and a checkerboard to none](paper/bucket-figure.svg)

Corner containment also preserves edges, so the reduction works for frames.
Every ordinary cube ($T$ or $P$) has all six two-colour edge types, and a
checkerboard lacks only one. The ordinary varieties form two orientation
classes, each with one trichromatic orientation on every triple of colours.
For a failing reduced collection of $16n-4$ cubes, call the larger class the
majority and all other cubes the minority. The argument has four steps:

1. **At most six minority cubes.** Targets with three monochromatic opposite
   face pairs ($D$) need both orientations of one colour triple. Hall's theorem
   extends any $D$ corner solution to a frame, using the edge facts above, so
   counting $D$ corner solutions leaves at most six minority cubes.
2. **Bucket capacity $4n-1$.** A majority bucket with $4n$ cubes builds a frame
   with four faces of one colour and two opposite faces of others ($Q$).
   Counting memberships by cube type and by bucket, which is
   [BES's equation (1)](https://math.colgate.edu/~integers/s68/s68.pdf), gives
   $$n_T+2n_P\le 4(4n-1),$$
   where $n_T,n_P$ count majority $T$ and $P$ cubes, including repeats.
3. **No minority cubes.** If one remains, the target with face tuple
   $(a,b,a,b,a,c)$ can be built from $3n-2$ cubes of one $T$ variety, $n$ of
   another, the minority cube and ordinary cubes for the edges: a contradiction.
   For $n=2$, the original corner argument with targets of type $R$ (four faces
   of one colour, two adjacent faces of others) does this step.
4. **Equal multiplicities.** All cubes are now majority cubes, the bucket count
   excludes $P$ cubes, and each $T$ variety occurs exactly $4n-1$ times.

## Repository layout

- `paper/`: manuscript source and PDF.
- `ThreeColour/`: Lean proofs, generated geometry and formalisation guide.
- `scripts/`: geometry generation, validation, comparator and optional search.
- `data/lower-obstruction.json`: the 28-cube witness and its 120 Hall certificates.
- Root Lean files and configuration: build entry points, independent challenge,
  comparator configuration and formalisation metadata.

## Lean dependency

The project uses Lean and mathlib **v4.35.0** and pins
release [v1.0.0 of colour-cubes-core](https://github.com/jasondavies/colour-cubes-core/tree/v1.0.0) for the physical model, proper rotations and
corner geometry. Lake fetches this shared library automatically.

## Reproduce

Install [elan](https://github.com/leanprover/elan), Python 3.11 or later and
Ruby, then run:

```sh
lake exe cache get
make check
make paper  # requires latexmk and a LaTeX installation
```

`make check` audits proof sources, validates metadata and dependency pins,
regenerates geometry and figures, runs the separate corner and frame Python checkers, and builds
all Lean targets, including the axiom guards.
[CI](.github/workflows/ci.yml) runs these checks on pushes and pull requests.

The public Lean results include:

| Theorem | Claim |
| --- | --- |
| `frame_threshold_n` | For every $n\ge2$, the least frame guarantee is $16n-3$. |
| `family_frame_classification` | Exactly the two scaled obstructions fail at size $16n-4$, for arbitrary oriented input cubes. |
| `full_threshold_n` | The least complete-cube guarantee is $\max\{n^3,16n-3\}$. |
| `full_cube_of_four_le` | Any $n^3$ source cubes suffice for $n\ge4$. |
| `family_restricted_threshold29` / `family_restricted_of_solvable28` | At $n=2$, every 29-cube family and every solvable 28-cube family builds a $Q$, $R$, or $D$ target. |

See [Challenge.lean](Challenge.lean) for all 35 statements, including
catalogue coverage, uniqueness, geometry and the restricted-target counts.

`Family.lean` and `FrameFamily.lean` work with arbitrary indexed face colourings;
solutions select distinct copies and proper rotations. Transport lemmas connect these
families to inventories of the 68 canonical varieties. A
[corner–rotation theorem](https://github.com/jasondavies/colour-cubes-core/blob/v1.0.0/ColourCubes/Corners.lean), valid for any
palette, equates cyclic corner matching with matching the three exposed faces
by a proper rotation. The proof does not enumerate all collections.

## Kernel replay

```sh
make comparator
```

This checks the statements and referenced definitions in `Challenge.lean`
against the proof library, then replays the proofs through Lean, NanoDa and
con-ron. The challenge copies model definitions and tables; it does not
constitute an independently devised model. Replay requires `bwrap`, can take
tens of minutes, and is separate from `make check`.

The [Comparator workflow](.github/workflows/comparator.yml) runs only on manual
request. See the [formalisation guide](ThreeColour/README.md#verification-and-maintenance)
for resource settings, release checks and the Palomar preflight.

## Computation and review

The [separate checker](scripts/check_three_colour_threshold.py) uses Python's
standard library and generates rotations from quarter-turns. It checks the
68-to-38 corner reduction, the printed entries in both geometric tables,
both exhibited lower obstructions, all 120 targets,
68 one-cube extensions of the first obstruction and 1,000 sampled 29-cube
collections. The extension and sample checks use only the 28 targets of
types $Q,R,D$ in the paper's restricted-target corollary. It also checks this
restriction on 1,000 sampled 28-cube collections. These finite samples do not
prove the general statements, which are established by the paper and the
Lean proofs in [RestrictedFamily.lean](ThreeColour/RestrictedFamily.lean).

A second checker, [check_frames.py](scripts/check_frames.py), covers frames.
It checks the edge facts used in the proof, that the reduction preserves edges,
and the corners and edges of every $(a,b,a,b,a,c)$ target. For $n=2,\dots,6$
it matches against all 120 targets to confirm that both obstructions fail and
that all 136 one-cube extensions succeed. These are again finite checks; the
general statements are proved in [FrameResults.lean](ThreeColour/FrameResults.lean).

The optional search, for the case $n=2$, uses OR-Tools CP-SAT:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
python3 scripts/cube_frame_search.py --palette 4 --target-colours 3 \
  --minimal --seconds 60 --workers 8 \
  --hint data/lower-obstruction.json --output /tmp/four-to-three-search.json
```

That command searches for the largest obstruction. To test size 29 and
exclude the known 28-cube obstructions among the 38 reduced varieties, run:

```sh
python3 scripts/cube_frame_search.py --palette 4 --target-colours 3 \
  --minimal --size 29 --seconds 60 --workers 8 \
  --output /tmp/four-to-three-size29.json
python3 scripts/cube_frame_search.py --palette 4 --target-colours 3 \
  --minimal --size 28 --exclude-colour-orbit data/lower-obstruction.json \
  --seconds 60 --workers 8 --output /tmp/four-to-three-exclude-extrema.json
```

Both should report `INFEASIBLE`. The checked-in fixture contains the 28-cube
witness and Hall certificates for every target; the geometric checker validates
them on each run. The Lean proof does not depend on the solver.

See [formalization.yaml](formalization.yaml) for AI contributions, review scope
and the outstanding literature check, and the paper for the author's disclosure.

Code and manuscript are distributed under the [Apache-2.0 licence](LICENSE).
