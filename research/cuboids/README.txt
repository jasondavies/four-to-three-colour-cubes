Four-to-three cuboids: all-shape research argument
=================================================
6 November 2026

Start with cuboid-theorem.txt and the focused review in REVIEW.txt. It gives a complete
written argument for the proposed sharp classification, for ordered sides
2<=a<=b<=c:

  F(a,b,c)=max{16a-3,4(a+b+c)-16,floor((24c-1)/5)};
  G(a,b,c)=max{abc,16a-3,floor((24c-1)/5)}.

It uses only the established reduction and elementary corner geometry.
In particular the upper proof does not assume the sharp corner, cube, rod
or strip thresholds; all become special cases. The construction uses D,
Q, and one fixed H orientation. It also identifies the exact-cardinality
frame region and all complete-box exceptions.

Status
------
This is a new working proof, with self-review and independent physical
geometry audits. The focused second-pass review found no mathematical gap. It has not
received external mathematical refereeing. Seven arithmetic interfaces
have standalone Lean proofs; the full geometric threshold theorem has
not been formalised. The written argument is now integrated in
paper/cuboids.tex; the thin-cuboid Lean development retains its earlier route.
No literature-priority claim is made.

Review the proof rather than interpreting a successful program as an
exhaustive inventory theorem. The key points are:

1. In the D branch the target may change. Every designated good vertex
   must mean an actual corner solution, and incident weight eight makes
   a vertex good. The weighted triangle lemma then controls all three
   directional demands simultaneously.
2. The H target has tuple (v,w,u,u,u,v). Its shortest-axis uu demand is
   twice a-2; its middle-axis vv demand is b-2. Including corners it
   needs 2a T_u, b T_v, one minority, and one extra majority copy.
3. If D and Q both fail, cardinality forces b+c<=3a+4. This makes the
   majority T counts sufficient for a>=3.
4. For a=2, the two-high-colour case forces at least five minority copies.
   At most three checkerboards miss the high pair, so a suitable minority
   triple exists. This also eliminates the second H orientation formerly
   needed in the strip proof.
5. The lower bounds use target geometry in every axis assignment: pure
   ordinary sources force Q; checkerboards force D. They count corners
   as well as noncorner edge positions.

Files and reproduction
----------------------
cuboid-theorem.txt       Complete written proof and consequences.
cuboids.py              General constructive target choice and exact flow.
audit.py                Independent signed-permutation physical audit.
audit-results.json      Deterministic audit report.
weighted_audit.cpp       Independent weighted-triangle finite audit.
weighted-audit-results.txt  Deterministic weighted audit report.
REVIEW.txt              Focused mathematical review and its limitations.
review_geometry.py      Fresh reconstruction of the inherited geometry.
review-geometry-results.json  Its deterministic report.
ArithmeticReview.lean   Seven unbounded arithmetic checks in Mathlib.
arithmetic-review-results.txt  Kernel axiom reports.

From the repository root:

  python3 -S research/cuboids/audit.py
  c++ -std=c++17 -O3 -Wall -Wextra -pedantic \
    research/cuboids/weighted_audit.cpp -o /tmp/cuboid-weighted-audit
  /tmp/cuboid-weighted-audit
  python3 -S research/cuboids/review_geometry.py

For the optional symbolic arithmetic checks, use the existing pinned
Lean environment:

  lake env lean research/cuboids/ArithmeticReview.lean

The Python construction imports geometry.py and construct.py from the
sibling thin-cuboids research directory. No third-party Python
packages or optimisation solvers are required. The independent audit
constructs proper rotations as determinant-one signed permutations,
separately from the construction's quarter-turn and cyclic-corner model.

Recorded checks
---------------
* 4,730 constructive inventories over 562 selected shapes, including
  unreduced original varieties, checkerboards, Q and 463 H constructions.
* 432 explicit boundary controls, including the two-high-colour cases.
* 48 directional tables and 2,112 H reservation incidences.
* Both lower-witness families against all 648 oriented targets on twelve
  representative shapes (15,552 target/witness checks).
* Numerical inequalities and the exact-cardinality condition on 261,040
  ordered shapes.
* 50,981,147 checkerboard weight vectors, with every allowed good-vertex
  set, at five representative dimension triples.

These computations audit geometry and the constructive proof. They are
not a new certificate-based proof, and the mathematics does not rely on
extrapolating these finite tests to arbitrary dimensions.

Manuscript integration validation, 6 November 2026
------------------------------------------------
make paper produced a 17-page PDF without LaTeX warnings, unresolved
references or box warnings. The title page, new proof section and final
page were rendered and inspected. All local README links and TeX label
references resolve. The packaged geometry reconstruction and seven Lean
arithmetic proofs passed again. The constructor imports the same audited
geometry and matching dependencies from research/thin-cuboids. The larger
inventory and weighted-vector audit records are from the preceding
mathematical review; they were not rerun for the manuscript-only edits.
No new full Lean build, external referee review, commit or publication is
claimed by this integration record.
