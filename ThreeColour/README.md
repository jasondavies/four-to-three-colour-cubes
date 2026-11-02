# Four-colour cubes and three-colour targets

From the repository root, run `lake build ThreeColour` with the pinned Lean and mathlib
v4.35.0. The default `lake build` also builds the independent comparator challenge and solution entry point.
Finite geometry checks are split across modules so Lake can build them in
parallel. The first build is substantially slower than a cached build.

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

`FamilyGeometry.lean` checks how rotations permute the eight positions. `Reflection.lean` proves that physical reflection
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

`CornerGeometry.lean` proves the corner–rotation correspondence for an arbitrary
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
The root `ThreeColour.lean` guards twenty-eight axiom reports, covering the comparator results,
arbitrary-family classification, and both forms of the corner–rotation lemma;
only `propext`, `Classical.choice`, and `Quot.sound` are permitted. There are no
proof holes or uses of `native_decide` in the proof library. The twenty-five intentional
statement holes in `Challenge.lean` are isolated comparator targets.

The separate Python geometry checker also compares both printed tables with
the computed geometry. Attribution and review scope are recorded in
[formalization.yaml](../formalization.yaml).

The geometry dependency is `macmahon_min_universal_sets`, pinned in
`lakefile.toml` and `lake-manifest.json`. Only `MacMahon.Rotations` and its
transitive definition imports are used; no six-colour classification result
is imported. The standalone challenge imports only mathlib and contains copies
of the relevant model definitions and tables. The comparator checks their
agreement with the proof library and replays the exported proofs; this is
separation of the statements from the implementation, not independent modelling.

## Verification and maintenance

Run `make check` from the repository root for source and metadata audits,
generated-file checks, the Python geometry checker and the Lean build.
Full kernel replay is a separate command:

```sh
make comparator
```

The comparator replays the 25 challenge results through the toolchain's bundled
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
