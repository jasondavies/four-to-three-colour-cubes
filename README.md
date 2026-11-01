# A sharp threshold for three-colour targets from four-colour cubes

- [Paper (PDF)](paper/macmahon-four-to-three.pdf) and [LaTeX](paper/macmahon-four-to-three.tex).
- [Main Lean results](ThreeColour/Family.lean), [physical model](ThreeColour/PhysicalDefs.lean), and [formalisation guide](ThreeColour/README.md).
- [Independent theorem statements](Challenge.lean) and [completed proof entry point](Solution.lean).
- [Provenance, scope and AI disclosure](formalization.yaml).

**Every collection of 29 four-colour cubes contains eight that build an
exactly-three-colour target. The bound is sharp, and exactly two labelled
28-cube collections fail.** The two obstructions are mirror images: seven
copies of each of four varieties in one orientation class.

![A three-colour target beside the four cube varieties of one obstruction](paper/obstruction-figure.svg)

*Left: a target, with each hidden side the same colour as the side opposite it.
Right: unfolded cubes viewed from outside, each rotated so that its repeated
colour occupies the central square and the squares to its right and above.
These 28 cubes build no three-colour target.*

Each source cube uses all four colours of a fixed palette. Varieties identify
proper rotations, not reflections, and collections may repeat varieties.
The target is a 2×2×2 cube with monochromatic exterior faces using exactly
three colours. Internal faces need not match. Colours remain fixed when
counting the two extremal collections.

This answers the threshold question in Problem 2 of
[Berkove, Eickemeyer and Schulman, *The 4-Color Cubes Puzzle* (2018)](https://math.colgate.edu/~integers/s68/s68.pdf).
The written proof uses corner containment, explicit corner assignments and
elementary counting. A literature search on November 1, 2026 found no later
answer, but Rosenfeld's October 2026 Geombinatorics article remains unread.
Priority has not been independently established.

## Repository layout

- `paper/`: manuscript source and PDF.
- `ThreeColour/`: Lean proofs, generated geometry and formalisation guide.
- `scripts/`: geometry generation, validation, comparator and optional search.
- `data/lower-obstruction.json`: the 28-cube witness and its 120 Hall certificates.
- `.github/workflows/`: CI and the optional Palomar preflight.
- Root Lean files and configuration: build entry points, independent challenge,
  comparator configuration and formalisation metadata.

## Lean dependency

The project pins
[macmahon-min-universal-sets](https://github.com/jasondavies/macmahon-min-universal-sets/tree/3f854795a77cd7c902e4c5a1a5da3322f9cd44fa)
to commit `3f854795a77cd7c902e4c5a1a5da3322f9cd44fa` in both `lakefile.toml`
and `lake-manifest.json`. It reuses `MacMahon.Rotations` and its transitive
physical definitions: the 24 proper rotations, six coordinate face directions
and eight corner positions. It does not import the six-colour classification
proof. Both projects use Lean and mathlib **v4.35.0**.

This avoids maintaining a second copy of the same geometry. The tradeoff is
that the upstream geometry currently imports some six-colour definitions;
a small shared geometry package would be a sensible future extraction if
more projects need it. The fixed commit makes this build independent of
future changes to the upstream default branch. A fresh clone fetches the
public dependency; no sibling checkout or machine-specific path is needed.

## Reproduce

Install [elan](https://github.com/leanprover/elan), Python 3.11 or later and
Ruby, then run:

```sh
lake exe cache get
make check
make paper  # requires latexmk and a LaTeX installation
```

`make check` validates source requirements and metadata, checks the dependency
pin and absence of proof holes, regenerates finite geometry in a temporary
directory, runs the separate Python geometric checker, and builds all Lean
targets. The root `ThreeColour.lean` guards twenty-two axiom reports, permitting only
`propext`, `Classical.choice`, and `Quot.sound`. There is no `native_decide`.
The first Lean build takes several minutes; finite checks are split into
modules for parallel builds. CI repeats these checks and runs the full
comparator on pushes and pull requests.

The public Lean results include:

| Theorem | Claim |
| --- | --- |
| `family_threshold29` | Every arbitrary indexed family of 29 four-colour cubes has a three-colour solution. |
| `family_sharp_threshold29` | Upper bound without source or target catalogues and explicit size-28 counterexample. |
| `family_least_guaranteed_size` | Least-size theorem without source or target catalogues. |
| `family_classify28_geometric` | Classification for arbitrary indexed cubes by proper-rotation equivalence to the source representatives. |
| `physical_threshold29` | Every collection of size 29 has a physical solution. |
| `physical_classify28` | Exactly the two specified size-28 collections fail. |
| `least_guaranteed_size` | 29 is the least size guaranteeing success for all larger collections. |
| `source_catalogue_complete` / `target_catalogue_complete` | Every relevant face assignment occurs up to proper rotation. |
| `source_catalogue_unique` | Distinct source indices are distinct rotation varieties. |
| `reflect_extremal` | Reflection exchanges the two extremal collections. |

`Family.lean` proves the threshold and sharpness directly for arbitrary
indexed face colourings, with exactly four colours per source and an
existential target using exactly three. A solution selects eight distinct
copies and geometric proper rotations. Transport in both directions connects
this model to natural-number multiplicities of the 68 canonical varieties
and extends the classification to arbitrarily oriented input cubes.
A [general corner–rotation theorem](ThreeColour/CornerGeometry.lean), valid for
any palette, proves that cyclic corner matching is equivalent to matching the
three exposed faces by a proper rotation. Small finite checks connect the
catalogue's corner codes to this theorem. The proof does not enumerate all
collections.

## Comparator and Palomar

`Challenge.lean` independently restates nineteen results and their physical
models, importing only mathlib. These include threshold and
sharpness statements without source or target catalogues, geometric
rotation-class counts for the arbitrary-family classification, colour counts
for both catalogues, completeness and
properness of the rotation table, the outward-face rule, and physical mirror
geometry. Its nineteen deliberate `sorry` declarations are
isolated comparator targets. They are not imported by `Solution.lean` or any
proof module, and are excluded from the proof-development hole count.

```sh
make comparator
```

This uses the toolchain's comparator and bundled Lean, NanoDa and con-ron
kernels. Definition and statement mismatches fail before kernel replay;
the full replay can take tens of minutes. `make check` alone does not run it.
It requires `bwrap` and support for its sandbox. The manually triggered
Palomar preflight workflow follows the same pinned pipeline as the earlier
MacMahon repository. Neither a local pass nor this packaging is a registry
submission or acceptance. No registry entry is claimed.

## Computation and review

The [separate checker](scripts/check_three_colour_threshold.py) uses Python's
standard library and generates rotations from quarter-turns. It checks the
68-to-38 corner reduction, the printed entries in both geometric tables,
both exhibited lower obstructions, all 120 targets,
68 one-cube extensions of the first obstruction and 1,000 sampled 29-cube
collections. These finite samples do not prove the upper bound.

The optional search uses OR-Tools' compiled multicore CP-SAT backend:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r requirements.txt
python3 scripts/cube_frame_search.py --palette 4 --target-colours 3 \
  --minimal --seconds 60 --workers 8 \
  --hint data/lower-obstruction.json --output /tmp/four-to-three-search.json
```

That command finds the size-28 optimum. These report no 29-cube obstruction
and no other 28-cube obstruction among the 38 reduced varieties, up to colour
permutation:

```sh
python3 scripts/cube_frame_search.py --palette 4 --target-colours 3 \
  --minimal --size 29 --seconds 60 --workers 8 \
  --output /tmp/four-to-three-size29.json
python3 scripts/cube_frame_search.py --palette 4 --target-colours 3 \
  --minimal --size 28 --exclude-colour-orbit data/lower-obstruction.json \
  --seconds 60 --workers 8 --output /tmp/four-to-three-exclude-extrema.json
```

Both should report `INFEASIBLE`. The checked-in fixture contains the 28-cube
witness and Hall certificates for every target. The geometric checker validates
them on each run and prints its report to stdout. Neither saved run reports nor
solver claims are needed for the Lean proof.

AI contributions and review scope are recorded in [formalization.yaml](formalization.yaml)
and the paper's disclosure. The original GPT-6-Astra review covered an earlier
version; Claude Opus 5.5 contributed later mathematical simplifications and
review. The paper has not received independent human peer review.

Code and manuscript are distributed under the [Apache-2.0 licence](LICENSE).
