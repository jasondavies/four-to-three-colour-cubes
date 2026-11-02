# Three-colour solutions from four-colour cubes

- [Paper (PDF)](paper/four-to-three-colour-cubes.pdf) and [LaTeX](paper/four-to-three-colour-cubes.tex).
- [Main Lean results](ThreeColour/Family.lean), [physical model](ThreeColour/PhysicalDefs.lean), and [formalisation guide](ThreeColour/README.md).
- [Independent theorem statements](Challenge.lean) and [completed proof entry point](Solution.lean).
- [Provenance, scope and AI disclosure](formalization.yaml).

**Every collection of 29 four-colour cubes contains eight that build an
exactly-three-colour target. For a fixed palette, exactly two collections of
28 cubes fail.** Each consists of seven copies of each of four varieties; the two
collections are mirror images.

Each source cube uses all four colours. A target is a 2×2×2 cube with
monochromatic exterior faces using exactly three colours; internal faces
need not match. Colourings related by a proper rotation are the same
*variety*; reflecting a cube is not an allowed move. Collections may repeat varieties.
A trichromatic corner has three different face colours.

This answers the threshold question in Problem 2 of
[Berkove, Eickemeyer and Schulman, *The 4-Color Cubes Puzzle* (2018)](https://math.colgate.edu/~integers/s68/s68.pdf).

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

Eight cubes in any bucket can build a three-colour target, so an unsolvable
collection has at most seven in each bucket. Let $n_T,n_P$ count the $T$ and
$P$ cubes, including repeats. Counting memberships by cube type and by bucket gives

$$n_T+2n_P\le 4\cdot7=28.$$

The ordinary varieties ($T$ and $P$) form two orientation classes, each sharing
one trichromatic orientation on every triple of colours. For a failing reduced
collection of 28 cubes, call the larger class the majority and all other cubes
the minority. The remaining argument has three steps:

1. Targets with three monochromatic opposite face pairs ($D$) force the
   minority to contain at most six cubes, leaving at least 22 in the majority.
2. If any minority cubes occur, targets with four faces of one colour and two
   differently coloured adjacent faces ($R$) force $2t_a+p_a\le10$ in each
   bucket, where $t_a,p_a$ count majority $T,P$ cubes. Summing bounds the
   majority by 20, a contradiction.
3. All cubes therefore belong to one ordinary class. The bucket count then
   excludes $P$ cubes and forces seven $T$ cubes of each repeated colour.

The bucket double-count is [BES's equation (1)](https://math.colgate.edu/~integers/s68/s68.pdf).

## Repository layout

- `paper/`: manuscript source and PDF.
- `ThreeColour/`: Lean proofs, generated geometry and formalisation guide.
- `scripts/`: geometry generation, validation, comparator and optional search.
- `data/lower-obstruction.json`: the 28-cube witness and its 120 Hall certificates.
- Root Lean files and configuration: build entry points, independent challenge,
  comparator configuration and formalisation metadata.

## Lean dependency

The project uses Lean and mathlib **v4.35.0** and pins
[colour-cubes-core](https://github.com/jasondavies/colour-cubes-core/tree/3164adbd2ee16d2721caadc1db67c1498e5d67e0) for the physical model, proper rotations and
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
regenerates geometry and figures, runs the separate Python checker, and builds
all Lean targets, including the axiom guards.
[CI](.github/workflows/ci.yml) runs these checks on pushes and pull requests.

The public Lean results include:

| Theorem | Claim |
| --- | --- |
| `family_threshold29` | Every arbitrary indexed family of 29 four-colour cubes has a three-colour solution. |
| `family_sharp_threshold29` | Upper bound without source or target catalogues and explicit size-28 counterexample. |
| `family_least_guaranteed_size` | Least-size theorem without source or target catalogues. |
| `family_classify28_geometric` | Classification for arbitrary indexed cubes by proper-rotation equivalence to the source representatives. |
| `family_restricted_threshold29` / `family_restricted_of_solvable28` | Every 29-cube family and every solvable 28-cube family builds a target of type $Q$, $R$, or $D$. |

See [Challenge.lean](Challenge.lean) for all 25 checked statements, including
catalogue coverage, uniqueness, geometry and the restricted-target counts.

`Family.lean` works with arbitrary indexed face colourings; a solution selects
eight distinct copies and proper rotations. Transport lemmas connect these
families to inventories of the 68 canonical varieties. A
[corner–rotation theorem](https://github.com/jasondavies/colour-cubes-core/tree/3164adbd2ee16d2721caadc1db67c1498e5d67e0/ColourCubes/Corners.lean), valid for any
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

The optional search uses OR-Tools CP-SAT:

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
