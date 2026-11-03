# Four-colour cubes and three-colour targets

From the repository root, run `lake build ThreeColour` with the pinned Lean and mathlib
v4.35.0. The default `lake build` also builds the independent comparator challenge and solution entry point.
Finite geometry checks are split across modules so Lake can build them in
parallel. The first build is substantially slower than a cached build.

The general results are in `FrameResults.lean`: `frame_threshold_n` proves the
sharp frame threshold $16n-3$ for $n\ge2$, `full_threshold_n` proves the sharp
complete-cube threshold $\max\{n^3,16n-3\}$, and `full_cube_of_four_le` gives
the consequence for $n\ge4$. `FrameFamily.lean` proves the extremal classification
for arbitrary indexed face colourings. Internally, `k=n-2` avoids truncated
subtraction in position counts.

`FrameDefs.lean` indexes frame positions by eight corners and twelve copies
of `Fin k`. `FramePhysical.lean` proves that corner and edge eligibility is
equivalent to proper-rotation matching on the specified exterior faces.
`FrameFamily.lean` transports these placements in both directions between
catalogue inventories and arbitrary oriented input families, including target
rotation and edge-position permutation. `FullCube.lean` adds six face interiors
of size $k^2$ and an interior of size $k^3$, proves that the total is $(k+2)^3$,
and fills the remaining positions with unused copies. No internal faces are constrained.

`FrameMatching.lean` groups interchangeable positions without losing distinct
copy use. The $Q,D,U$ constructions are checked in `FrameCertificates.lean`,
`FrameDGeometry.lean` and `FrameConstructions.lean`; `FrameCounting.lean`
scales the minority and bucket argument. These pools remain preimages of the
reduction, so the proof applies to all 68 original varieties.
`FrameLower.lean` verifies the orientation-or-monochromatic-edge deficiency
for every target and proves the obstruction for all `k`, rather than checking
a bounded range of side lengths. `FrameTheorems.lean` supplies the inventory
threshold and classification; the original 28-cube classification supplies `k=0`.

`NearPurity.lean` strengthens the purity argument to size $16n-5$.
For the 27-cube endpoint, `RMajority0.lean` through `RMajority3.lean`
verify the R construction with an arbitrary supported minority corner.
`NearData.lean` defines 32 explicit templates (eight T parameters and
24 P parameters) and proves their count for every `k`. `NearLower.lean`
proves that all these templates fail, and `NearClassification.lean` proves
that no others fail at that size and that the pair cases are inclusion-maximal.
`NearResults.lean` transports the classification to arbitrary physical families.

`FrameRestrictedDefs.lean` retains the Q/D/U target witness and checks the
count of forty. The frame constructions and counting argument now preserve
that witness, giving `family_restricted_frame_of_le` for `k ≥ 1`. The source
families and rotations are physical; the permitted target set is specified
using the checked catalogue. These extensions are built and axiom-audited
by the default target but are not yet in the 35-statement comparator challenge.

`scripts/generate_frame_data.py` generates `FrameData.lean`; every tag and
rotation in it is checked by Lean. `scripts/check_frames.py` separately checks
the edge facts, reduction, $U$ multisets, both obstructions for $2\le n\le6$,
and all 136 one-cube extensions at each tested side length. Those finite tests
supplement the symbolic Lean proofs.

The public results in `Theorems.lean` are:

- `physical_threshold29`: every collection of size 29 has a solution.
- `physical_classify28`: a collection of size 28 fails exactly when it is one
  of the two specified extremal collections.
- `sharp_threshold29`: the upper bound and a size-28 counterexample together.
- `least_guaranteed_size`: 29 is the least size guaranteeing a solution for
  every collection at least that large.

`Inventory` is a function from the 68 canonical source varieties to natural
number multiplicities. `Stock` labels each individual copy. `PhysicalSolvable`
embeds the eight target positions into this stock and provides one of the 24
proper rotations for each selected copy, matching its three exposed faces.
Internal faces are unrestricted. Targets are the 120 proper-rotation classes
using exactly three of the four fixed colours.

`Catalogue.lean` proves that every four-colour source and every exactly-three-
colour target face assignment occurs up to a proper rotation. `Encoder.lean`
checks that all listed representatives use the required number of colours;
`Uniqueness.lean` proves that distinct source and target indices are distinct rotation
varieties. `Family.lean` transports solutions in both directions between inventories
and arbitrary indexed face assignments. Its `family_threshold29`,
`family_sharp_threshold29`, and `family_least_guaranteed_size` statements
use no source or target catalogue tables: sources use exactly four colours, the existential
target uses exactly three, and distinct selected copies match its exterior
faces by geometric proper rotations. `family_classify28_geometric` extends the
classification to arbitrary families using geometric rotation-class counts,
and is included in the comparator challenge. `family_classify28` is the
internal inventory formulation.
`restricted_classify28` in `Classification.lean` proves the stronger statement used in the paper:
avoiding $Q,R,D$ at size 28 already forces an extremal collection.
`RestrictedDefs.lean` defines the target families geometrically: four faces of
one colour and two differently coloured opposite faces ($Q$) or adjacent faces
($R$), or three monochromatic opposite pairs ($D$). The counting proof retains
these target witnesses. `RestrictedFamily.lean` proves
`family_restricted_of_29_le`, `family_restricted_threshold29`, and
`family_restricted_of_solvable28` for arbitrary indexed families.
`RestrictedGeometry.lean` proves the counts 12, 12, 4, and 28 in total;
`RestrictedCatalogue.lean` proves that these representatives exhaust the
geometric families. These results and target uniqueness are comparator targets.

`ColourCubes.RotationAction` checks how rotations permute the eight positions. `Reflection.lean` proves that physical reflection
exchanges the two extremal collections.

`Core.lean` derives the Hall criterion from mathlib. `Stats.lean` verifies the
source-pool counting identities. These pools are preimages under the corner
reduction: `allCheckers` contains 36 original varieties mapping to six
checkerboards, while the other two pools have sizes 8 and 24. `Counting.lean` and `Classification.lean` prove
the threshold and classification by a related counting argument with named
lemmas. They treat checkerboards and the smaller ordinary class separately;
the written proof combines them as minority cubes. `Certificates/` checks finite Hall
certificates for the sufficient constructions; `Lower.lean` checks a Hall
deficiency for each target and each extremal collection.

`ColourCubes.Corners` proves the corner–rotation correspondence for an arbitrary
palette, allowing repeated colours. The proof checks only the finite geometry
of the 24 rotations and eight oriented frames, then reasons symbolically about
colours. `CornerCoding.lean` checks that the base-four canonical code identifies
exactly cyclically equivalent triples; `CornerData.lean` checks the stored
source and target corners against their face colours. `Physical.lean` combines
these results, replacing 65,280 separate compatibility checks.

`RawChecks/` checks all 4,096 face assignments for catalogue
coverage. This is finite geometry verification, not an exhaustive search over
collections of cubes.

`scripts/generate_three_colour_lean.py` generates six data modules:
`Data.lean`, `LowerData.lean`, `PhysicalDefs.lean`, `RawData.lean`,
`ReflectionData.lean`, and `RData.lean`. Generation is not trusted: the Lean
kernel checks the stated finite properties. The catalogue checks in
`RawChecks/` and the certificate modules are checked-in Lean proofs.
No external solver result is imported as an axiom.
The root `ThreeColour.lean` guards thirty-eight axiom reports, covering the comparator results,
arbitrary-family classification, and both forms of the corner–rotation lemma;
only `propext`, `Classical.choice`, and `Quot.sound` are permitted. There are no
proof holes or uses of `native_decide` in the proof library. The thirty-five intentional
statement holes in `Challenge.lean` are isolated comparator targets.

The separate Python geometry checker also compares both printed tables with
the computed geometry. Attribution and review scope are recorded in
[formalization.yaml](../formalization.yaml).

The shared dependency is `colour_cubes_core`, pinned in `lakefile.toml` and
`lake-manifest.json`. It supplies the palette-independent physical model,
rotations, corner matching and rotation transport; it imports no paper-specific
catalogues or classifications. `FamilySolvable` specialises
`ColourCubes.HasSolution` to targets using exactly three colours.
The standalone challenge imports only mathlib and locally restates the required
core definitions and catalogue data. The comparator checks agreement with the
proof library, then replays the proofs; sharing definitions is not independent
mathematical modelling.

## Verification and maintenance

Run `make check` from the repository root for source and metadata audits,
generated-file checks, the Python geometry checker and the Lean build.
Full kernel replay is a separate command:

```sh
make comparator
```

The comparator replays the 35 challenge results through the toolchain's bundled
Lean, NanoDa and con-ron kernels after checking their statements and definitions.
Replay requires `bwrap` and support for its sandbox. On memory-limited machines,
use `CON_RON_JOBS=1 make comparator` to limit con-ron's workers; this changes
resource use, not the checks performed.

[Routine CI](../.github/workflows/ci.yml) runs on pushes and pull requests.
It builds the memory-heavy `RawChecks` modules serially before the remaining
checks. The first build can take substantially longer than a cached build;
new pushes cancel superseded routine checks.

The separate [Comparator workflow](../.github/workflows/comparator.yml) runs
only on manual request, with serial `RawChecks` builds and `CON_RON_JOBS=1`.
It saves the build cache before replay and allows up to three hours for replay
within a five-hour job. Routine pushes cannot cancel an active replay.
These settings were informed by local tests with 16 GB; they do not establish
that an 8 GB runner can build the project.

Before releasing or archiving a version, require a successful full replay of
that exact commit. Start the Comparator workflow with its `ref` input set to
the full commit SHA, then confirm the successful run summary records the same
SHA. A green routine CI run alone does not certify kernel replay.

The repository also includes a manually triggered
[Palomar preflight workflow](../.github/workflows/palomar-preflight.yml).
No registry submission or acceptance is claimed.
