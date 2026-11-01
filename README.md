# A sharp threshold for three-colour targets from four-colour cubes

- [Paper (PDF)](paper/macmahon-four-to-three.pdf) and [LaTeX](paper/macmahon-four-to-three.tex).
- [Main Lean results](ThreeColour/Theorems.lean), [physical model](ThreeColour/PhysicalDefs.lean), and [formalisation guide](ThreeColour/README.md).
- [Independent theorem statements](Challenge.lean) and [completed proof entry point](Solution.lean).
- [Provenance, scope and AI disclosure](formalization.yaml).

**Every collection of 29 four-colour cubes contains eight that build an
exactly-three-colour target. The bound is sharp, and exactly two labelled
28-cube collections fail.** The two obstructions are mirror images: seven
copies of each of four varieties in one orientation class.

Each source cube uses all four colours of a fixed palette. Varieties identify
proper rotations, not reflections, and collections may repeat varieties.
The target is a 2×2×2 cube with monochromatic exterior faces using exactly
three colours. Internal faces need not match. Colours remain fixed when
counting the two extremal collections.

This answers the threshold question in Problem 2 of
[Berkove, Eickemeyer and Schulman, *The 4-Color Cubes Puzzle* (2018)](https://math.colgate.edu/~integers/s68/s68.pdf).
The written proof uses corner containment, explicit corner assignments and
elementary counting. The [literature check](research/literature-review.txt) found no later
answer, but Rosenfeld's October 2026 Geombinatorics article remains unread.
Priority has not been independently established.

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
directory, runs the independent Python geometric checker, and builds all Lean
targets. The root `ThreeColour.lean` guards eleven axiom reports, permitting only
`propext`, `Classical.choice`, and `Quot.sound`. There is no `native_decide`.
The first Lean build takes several minutes; finite checks are split into
modules for parallel builds. CI repeats these checks on pushes and pull requests.

The public Lean results include:

| Theorem | Claim |
| --- | --- |
| `physical_threshold29` | Every collection of size 29 has a physical solution. |
| `physical_classify28` | Exactly the two specified size-28 collections fail. |
| `least_guaranteed_size` | 29 is the least size guaranteeing success for all larger collections. |
| `source_catalogue_complete` / `target_catalogue_complete` | Every relevant face assignment occurs up to proper rotation. |
| `source_catalogue_unique` | Distinct source indices are distinct rotation varieties. |
| `reflect_extremal` | Reflection exchanges the two extremal collections. |

The main results quantify over natural-number multiplicities of 68 canonical
source varieties. A physical solution uses eight distinct copies and one
proper rotation per copy. Catalogue coverage is a separate theorem, rather
than an explicit transport theorem for lists of arbitrarily oriented cubes.
A [general corner–rotation theorem](ThreeColour/CornerGeometry.lean), valid for
any palette, proves that cyclic corner matching is equivalent to matching the
three exposed faces by a proper rotation. Small finite checks connect the
catalogue's corner codes to this theorem. The proof does not enumerate all
collections.

## Comparator and Palomar

`Challenge.lean` independently restates nine results and their physical
model, importing only mathlib. Its nine deliberate `sorry` declarations are
isolated comparator targets. They are not imported by `Solution.lean` or any
proof module, and are excluded from the proof-development hole count.

```sh
make comparator
```

This uses the toolchain's comparator and bundled Lean, NanoDa and con-ron
kernels. It requires `bwrap` and support for its sandbox. The manually triggered
Palomar preflight workflow follows the same pinned pipeline as the earlier
MacMahon repository. Neither a local pass nor this packaging is a registry
submission or acceptance. No registry entry is claimed.

## Computation and review

The [independent checker](scripts/check_three_colour_threshold.py) uses Python's
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
  --hint results/q4-to-q3-initial.json --output /tmp/four-to-three-search.json
```

The saved search outputs include the size-28 optimum, a size-29 infeasibility
run, and a size-28 run excluding both extrema. Those runs use the reduced
source family and proved bucket bounds. They are computational checks, not
imported optimality certificates. The Lean proof stands independently of
CP-SAT and the saved JSON results.

GPT-6-Astra (OpenAI), used through Codex, developed the original argument,
computational search, Lean proof and manuscript under Jason Davies's direction.
Claude (Anthropic), through reviews supplied by the author, contributed the
minority-cube argument, edge-count balance proof, degree remark, and shorter
bucket and threshold proofs. Subsequent Codex revisions incorporated these
contributions; the [contribution record](research/claude-review-contributions.txt)
summarises their scope. Claude's model version was not recorded.

A separate AI reviewer found no mathematical errors in the original
development; its [review record](research/independent-review.txt) predates
extraction into this repository and the manuscript rewrites. It covers an
earlier version of the argument. These automated checks are not independent
human peer review.

Code and manuscript are distributed under the [Apache-2.0 licence](LICENSE).
