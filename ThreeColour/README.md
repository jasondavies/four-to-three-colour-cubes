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
`Uniqueness.lean` proves that distinct source indices are distinct rotation
varieties. `Family.lean` transports solutions in both directions between inventories
and arbitrary indexed face assignments. Its `family_threshold29`,
`family_sharp_threshold29`, and `family_least_guaranteed_size` statements
use no source or target catalogue tables: sources use exactly four colours, the existential
target uses exactly three, and distinct selected copies match its exterior
faces by geometric proper rotations. `family_classify28_geometric` extends the
classification to arbitrary families using geometric rotation-class counts,
and is included in the comparator challenge. `family_classify28` is the
internal inventory formulation.
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
The root `ThreeColour.lean` guards twenty-two axiom reports, covering the comparator results,
arbitrary-family classification, and both forms of the corner–rotation lemma;
only `propext`, `Classical.choice`, and `Quot.sound` are permitted. There are no
proof holes or uses of `native_decide` in the proof library. The nineteen intentional
statement holes in `Challenge.lean` are isolated comparator targets.

The separate Python geometry checker provides additional checks, including
comparison with the printed corner-type table. The original separate AI proof
review covers an earlier version of the argument. Later author-supplied Claude
reviews contributed the manuscript's minority-cube argument, edge-count balance
proof, degree remark and shorter bucket and threshold proofs. These reviews
are not independent human peer review, and formal verification does not
establish novelty.

The geometry dependency is `macmahon_min_universal_sets`, pinned in
`lakefile.toml` and `lake-manifest.json`. Only `MacMahon.Rotations` and its
transitive definition imports are used; no six-colour classification result
is imported. The independent challenge restates the physical model and imports
only mathlib, so comparator checking does not inherit the proof library's
definitions by import.
