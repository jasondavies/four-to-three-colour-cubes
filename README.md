# Three-colour cuboids from four-colour cubes

This repository proves sharp thresholds for assembling three-colour cuboids
from four-colour cubes, for every cuboid with side lengths at least two.

[Paper (PDF)](paper/four-to-three-colour-cubes.pdf) ·
[LaTeX](paper/four-to-three-colour-cubes.tex) ·
[Lean results](ThreeColour/CuboidResults.lean) ·
[Formalisation guide](ThreeColour/README.md) ·
[Provenance and AI disclosure](formalization.yaml)

Each source is a unit cube with one colour on each face and **all four colours
of a fixed palette present**. The assembled cuboid must have monochromatic
exterior faces using **exactly three colours**. Internal faces need not match.
Repeated varieties are allowed, and pieces may be moved by proper rotations.
A *variety* is a face colouring up to proper rotation.

## Sharp thresholds for all cuboids

A *frame* consists of the eight corners and the noncorner positions on the
twelve edges. For ordered integer dimensions $2\le a\le b\le c$, it has
$4(a+b+c)-16$ positions. Let $F(a,b,c)$ be the least number of source cubes
that guarantees a frame, and $G(a,b,c)$ the corresponding threshold for a
complete cuboid. The target colouring may depend on the inventory. Then

$$F(a,b,c)=\max\{16a-3,\;4(a+b+c)-16,\;\lfloor(24c-1)/5\rfloor\},$$

$$G(a,b,c)=\max\{abc,\;16a-3,\;\lfloor(24c-1)/5\rfloor\}.$$

The three frame bounds come from colour-bucket capacity, the number of
positions, and balanced checkerboards. They are all sharp.

**A complete cuboid needs no spare cubes for the universal guarantee except
for rods $2\times2\times c$ and the four shapes $2\times3\times3$,
$2\times3\times4$, $3\times3\times3$, $3\times3\times4$.**
In particular, any $n^3$ sources build a complete $n\times n\times n$ cube
when $n\ge4$, starting with any 64 sources for a $4\times4\times4$ cube.

A frame needs no spares precisely when
$b+c\ge3a+4$ and $c\le5(a+b)-19$. Shape matters even for frames with the
same number of positions:

| Dimensions | Frame positions | Frame threshold $F$ | Volume | Complete threshold $G$ |
| --- | ---: | ---: | ---: | ---: |
| $2\times2\times2$ | 8 | 29 | 8 | 29 |
| $3\times3\times3$ | 20 | 45 | 27 | 45 |
| $4\times4\times4$ | 32 | 61 | 64 | 64 |
| $2\times2\times7$ | 28 | 33 | 28 | 33 |
| $2\times3\times6$ | 28 | 29 | 36 | 36 |
| $2\times4\times6$ | 32 | 32 | 48 | 48 |

The threshold 29 for $2\times2\times2$ answers Problem 2 of
[Berkove, Eickemeyer and Schulman, *The 4-Color Cubes Puzzle* (2018)](https://math.colgate.edu/~integers/s68/s68.pdf).

## Proof idea

BES's corner-containment reduction replaces the 68 source varieties by 38
whose corner types are contained in theirs. Every solution after reduction
lifts to the original copies; edge availability is preserved too. The
retained types are monochromatic-corner ($T$), pair-type ($P$), and
checkerboard ($C$). A cube belongs to colour bucket $u$ if it has at least
two of the three corner types $uuv$, with $v\ne u$.

![A T cube links to one colour bucket, a P cube to two, and a checkerboard to none](paper/bucket-figure.svg)

The ordinary varieties ($T$ and $P$) form two orientation classes, each
supplying one cyclic orientation on every triple of colours. They have all
six bichromatic edge types; each checkerboard lacks just one.

At the claimed threshold, the cuboid construction has two cases:

1. **A target with three monochromatic opposite face pairs ($D$) has a corner
   solution.** Index checkerboards by their missing colour pairs, as weights
   on the edges of $K_4$. A weighted triangle lemma chooses a supported
   three-colour target and assigns its
   pairs to the three box directions. Hall's theorem fills the edge positions.
2. **No $D$ corner solution exists.** Orientation counts leave at most six
   cubes outside the larger ordinary class. A large colour bucket, or two
   sufficiently frequent $T$ varieties together with a minority cube,
   supplies the corners and monochromatic edges. Hall's theorem fills
   the remaining edges.

Every position outside the frame exposes at most one face. Since every
source has every palette colour, arbitrary unused copies complete the
cuboid once the inventory reaches its volume.

## Cubes: classification and stability

For $n\times n\times n$ frames, $F(n,n,n)=16n-3$. Exactly two collections
of $16n-4$ sources fail: $4n-1$ copies of each of the four $T$ varieties in
one ordinary orientation class, or the mirror image of that collection.
The figure shows $n=2$; replace seven copies by $4n-1$ for larger frames.

![Why the exceptional 28 cubes fail: missing corner orientations, or eight required cubes with only seven available](paper/obstruction-figure.svg)

*Marked vertices are monochromatic corners. In panel B, opposite target
faces have equal colours, so the hidden bottom face has colour 2.
In panel C, $a,b,c$ are distinct colours.*

The **stability theorem** classifies every failing cube inventory of size
at least $14n$, for $n\ge3$: all sources lie in one ordinary orientation
class, and every colour bucket contains at most $4n-1$ cubes. Consequently,
for $0\le d\le2n-4$, the numbers of failures and inclusion-maximal failures
at size $16n-4-d$ are

$$2\binom{d+15}{15}\qquad\text{and}\qquad2\binom{d+11}{11},$$

respectively. Inclusion-maximal means that adding any source cube makes
the inventory solvable. For deficits $0,1,2$, the counts are $2,32,272$,
with $2,24,156$ maximal. The 32-case result at deficit one also holds for
$n=2$: eight deletions from the two largest obstructions and twenty-four
cases containing one $P$ cube.

## Reproduce

The project pins Lean and mathlib **v4.35.0**, together with
[colour-cubes-core v1.0.0](https://github.com/jasondavies/colour-cubes-core/tree/v1.0.0)
for the physical model and palette-independent geometry. Install
[elan](https://github.com/leanprover/elan), Python 3.11 or later, Ruby and a
C++20 compiler. Lake fetches the Lean dependencies automatically.

For a clean build with CI's single-worker setting:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build ThreeColour.RawChecks
LEAN_NUM_THREADS=1 make check
make paper  # requires latexmk and a LaTeX installation
```

`make check` audits proof sources, metadata and dependency pins, checks
regenerated geometry and figures, runs the independent cube and cuboid
checks, and builds all Lean targets and axiom guards.
[CI](.github/workflows/ci.yml) runs these checks on pushes and pull requests.
For the focused all-cuboid geometry audit and kernel build, use
`make check-cuboids`; for rod and strip results, use `make check-thin`.

## Formal verification

The public threshold statements quantify over arbitrary indexed families
of physical sources. Solutions select distinct copies and proper rotations,
and their targets use exactly three colours.

| Public result | Claim |
| --- | --- |
| `cuboid_frame_threshold` / `cuboid_full_threshold` | Both all-cuboid thresholds, as `IsLeast` statements. |
| `cuboid_frame_exact_cardinality` / `cuboid_full_exact_volume` | The exact conditions for needing no spares. |
| `frame_threshold_n` / `full_threshold_n` | Sharp cube frame and complete-cube thresholds. |
| `family_frame_classification` / `family_near_frame_classification` | The two largest and 32 next-largest cube obstructions. |
| `family_frame_stability` | The failure criterion for $n\ge3$, $N\ge14n$. |
| `family_stability_failure_count` / `family_stability_maximal_count` | The two binomial counts. |
| `family_restricted_frame_of_le` / `frame_target_count` | Forty targets suffice for guaranteed cube frames when $n\ge3$. |

See [CuboidResults.lean](ThreeColour/CuboidResults.lean),
[FrameResults.lean](ThreeColour/FrameResults.lean), and the
[formalisation guide](ThreeColour/README.md) for definitions, module maps
and the remaining endpoints.

The [comparator challenge](Challenge.lean) restates 45 corner and cubic
results, including stability, near-extremal classification and counting,
and the forty-target theorem. [Solution.lean](Solution.lean) supplies their
proofs. Run

```sh
make comparator
```

to compare their statements and definitions with the library, then replay
through Lean, NanoDa and con-ron. This requires `bwrap` and is separate from
`make check`. The challenge copies the library's model definitions and tables;
it does not provide an independently devised model. **Rod, strip and general
cuboid results are checked by the library build and axiom guards, but are
outside the comparator challenge.**

## Computation and repository guide

Independent rotation-based audits check the finite geometry, lower
witnesses and constructive controls. Sampled inventories supplement the
symbolic proofs; they do not prove the universal upper bounds. The optional
corner search uses OR-Tools and is not required by `make check` or Lean.

- [Formalisation and maintenance guide](ThreeColour/README.md): proof structure,
  [audit and search commands](ThreeColour/README.md#independent-audits-and-optional-search),
  comparator scope and release checks.
- [Cuboid construction](research/cuboids/cuboids.py) and
  [physical-rotation audit](research/cuboids/audit.py): a constructive algorithm,
  lower-witness checks and additional inventory controls.
- `paper/`: LaTeX and PDF; `ThreeColour/`: Lean proofs and generated geometry;
  `scripts/`: generation, validation and optional search;
  `data/lower-obstruction.json`: the 28-cube witness and 120 Hall certificates.

Code and manuscript are distributed under the [Apache-2.0 licence](LICENSE).
