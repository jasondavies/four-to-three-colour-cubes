# Formalisation guide

The default `lake build` builds the proof library, the Mathlib-only
`Challenge.lean`, and the `Solution.lean` entry point. All thresholds
quantify over arbitrary indexed source families, distinct selected copies,
proper rotations and exactly three exterior colours. Internal faces are
unrestricted.

## All cuboids

The dependency chain follows the general theorem:

1. [BoxDefs.lean](BoxDefs.lean) defines exposed-face positions for a frame
   and complete cuboid. Cubes are equal-sided instances of these types.
2. [BoxModel.lean](BoxModel.lean) proves position counts, restriction to
   smaller dimensions, and completion using arbitrary unused sources.
3. [BoxAssignment.lean](BoxAssignment.lean) connects grouped Hall matching
   on catalogue inventories to physical placements.
4. [CheckerboardGraph.lean](CheckerboardGraph.lean) and
   [CuboidSelection.lean](CuboidSelection.lean) prove weighted graph
   selection. [CuboidTemplates.lean](CuboidTemplates.lean) and
   [CuboidTemplateChecks.lean](CuboidTemplateChecks.lean) specify and check
   the D/Q/H targets, source pools and corner/edge tags.
5. [CuboidSupply.lean](CuboidSupply.lean),
   [CuboidCornerSelection.lean](CuboidCornerSelection.lean),
   [CuboidGeometry.lean](CuboidGeometry.lean),
   [CuboidConstructions.lean](CuboidConstructions.lean),
   [CuboidCounting.lean](CuboidCounting.lean) and
   [CuboidUpper.lean](CuboidUpper.lean) prove the upper bound.
6. [CuboidLower.lean](CuboidLower.lean) gives the three lower bounds:
   frame cardinality, a bucket obstruction on the shortest-side cube,
   and balanced checkerboards on the longest rod. The checkerboard
   obstruction is proved in [CheckerboardLower.lean](CheckerboardLower.lean).
7. [CuboidResults.lean](CuboidResults.lean) gives both `IsLeast` thresholds
   and the no-spare criteria. [FrameResults.lean](FrameResults.lean) and
   [CuboidCorollaries.lean](CuboidCorollaries.lean) specialise them to
   cubes, rods and strips.

The position model uses side lengths minus two for edge-interior counts.
It has eight corners, four edge groups per axis, six face interiors and
one interior. Off-frame positions expose at most one face. `FullCube.lean`
specialises the cuboid completion theorem; there is one completion
construction.

## Cube classification and stability

The threshold corollaries do not classify failing inventories. These
additional results use the orientation and bucket counting machinery:

- [FrameLower.lean](FrameLower.lean) proves the scaled extremal obstructions
  symbolically in the side length.
- `FrameMatching`, `FrameCertificates`, `FrameDGeometry`,
  `FrameConstructions`, `FrameCounting` and `FrameTheorems` provide
  constructions and counting for the cube classification. `FrameFamily`
  transports the classification to arbitrary physical source families.
- [Stability.lean](Stability.lean) proves the failure criterion for
  $n\ge3$, $N\ge14n$. [StabilityParameters.lean](StabilityParameters.lean)
  encodes twelve pair multiplicities and four bucket slacks.
  [StabilityCounting.lean](StabilityCounting.lean) proves the bijection,
  both binomial counts, and inclusion-maximality among all larger inventories.
- `NearData`, `NearLower`, `NearPurity`, `NearClassification` and
  [NearResults.lean](NearResults.lean) classify the 32 failures at size
  $16n-5$, including the separate $n=2$ endpoint.
- `FrameRestrictedDefs` defines Q/D/U targets and checks their count of
  forty. `family_restricted_frame_of_le` retains a canonical target index
  while proving proper-rotation placements for arbitrary physical sources.
- [ClassCount.lean](ClassCount.lean) expresses failure counts in terms of
  physical rotation classes. [OrdinaryGeometry.lean](OrdinaryGeometry.lean)
  identifies the ordinary-class and bucket tables with their corner-type
  definitions.

## Corner geometry and catalogue

`Inventory` records multiplicities of 68 source varieties. `Stock` labels
individual copies. There are 120 target varieties using exactly three
colours. Source compatibility records presence of a corner; target
occurrences remain distinct positions.

`Core` derives Hall's criterion from Mathlib. `Stats`, `Counting` and
`Classification` establish the corner obstruction classification and
restricted Q/R/D constructions. `Certificates/` checks their finite Hall
certificates, and `Lower` checks deficiencies against every target.
These constructions also supply the $n=2$ classification endpoints.

`Catalogue`, `Encoder`, `Uniqueness` and `RawChecks/` check coverage and
uniqueness over all 4096 face colourings. `CornerCoding`, `CornerData` and
`Physical` connect cyclic corner codes to proper rotations through the
shared ColourCubes geometry library. `Family` and `FrameFamily` transport
between catalogue inventories and arbitrary oriented physical sources.
These representation theorems are needed to state the results without
assuming that input cubes arrive in canonical orientations.

`RestrictedDefs`, `RestrictedGeometry`, `RestrictedCatalogue` and
`RestrictedFamily` give geometric definitions of Q/R/D, catalogue
completeness, and the 28-target corner results. `Reflection` exchanges
the two extremal inventories.

## Reproduction and comparator

Install the pinned Lean toolchain through elan, Python 3.11+, Ruby and a
C++20 compiler. From the repository root:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build ThreeColour.RawChecks
LEAN_NUM_THREADS=1 make check
make paper
```

The serial catalogue prebuild limits memory consumption. `make check`
audits proof sources and pins, validates metadata, regenerates geometry
and figures, runs the independent audits, and builds every library target
and axiom guard. The PDF requires latexmk, a LaTeX installation and
CM-Super outline fonts.

[comparator.json](../comparator.json) lists 58 statements covering the
cuboid thresholds and corollaries, completion and cardinality, corner
results, cube classifications, stability, counts and restricted targets.
[Challenge.lean](../Challenge.lean) imports only Mathlib and restates the
required model definitions. [Solution.lean](../Solution.lean) imports the
proof library, which does not import the challenge. Its intentional
statement holes are not proofs and are excluded from proof-source audits.

```sh
LEAN_NUM_THREADS=1 CON_RON_JOBS=1 make comparator
```

The comparator compares statements and definitions, then replays through
Lean, NanoDa and con-ron from the pinned toolchain. It requires `bwrap`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
Definition agreement does not constitute independent conception of the
physical model. No proof library uses `sorry`, custom axioms or
`native_decide`.

Routine CI runs `make check`. The separate comparator workflow accepts an
exact commit SHA and records the checked revision. Before release, run
both checks on the submitted commit and retain their successful records;
a run against a different revision is not a release verification.

## Independent audits and optional search

- `scripts/check_three_colour_threshold.py` independently reconstructs
  corner geometry, the reduction, finite tables, and lower obstructions.
- `scripts/check_frames.py` checks edge geometry, U-target demands,
  both cube obstructions and all one-cube extensions for $n=2,\ldots,6$.
- `scripts/check-near-frames.sh` builds the C++20 audit of all 32
  near-extremal failures and pair-case extensions for $n=2,\ldots,6$.
  At $n=3,4$ it also checks all 272 deficit-two failures, all 10,608
  saturated-case extensions, and one slack-preserving extension for
  each of the 116 nonsaturated cases.
- [scripts/cuboids](../scripts/cuboids/README.md) contains the general
  constructor and independent geometry, coordinate and inventory audits.
  `make check-cuboids` runs those audits and the focused Lean build.

The symbolic proofs establish the universal results. Sampled inventories
and bounded grids are supplementary tests.

For optional corner searches, install OR-Tools and run:

```sh
python3 scripts/cube_frame_search.py --palette 4 --target-colours 3 \
  --minimal --size 29 --seconds 60 --output /tmp/three-colour-search.json
```

Solver time limits can yield `UNKNOWN`; an unfinished search is not a
proof of infeasibility. Search output is not trusted by the Lean proof.

`make regenerate` reproduces the finite catalogue and frame data.
`make figure` reproduces the obstruction and bucket illustrations.
The Lean kernel checks the generated geometry; generators are not proof
oracles.
