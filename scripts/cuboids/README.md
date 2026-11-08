# Cuboid construction and independent audits

`construct.py` implements the D/Q/H target selection from the cuboid proof
and capacitated matching. `geometry.py` constructs the rotations, source
varieties and reduction directly from face colourings.

Run from the repository root:

```sh
python3 -S scripts/cuboids/check_geometry.py
python3 -S scripts/cuboids/check_coordinates.py
python3 -S scripts/cuboids/check_construction.py
```

- `check_geometry.py` independently reconstructs physical rotations and checks
  the reduction, orientation classes, buckets and target families.
- `check_coordinates.py` independently traverses integer-coordinate cuboids
  to check exposed-face demands, threshold arithmetic and the reservation
  case split. It imports no repository code or generated tables.
- `check_construction.py` tests the constructor on sampled and boundary
  inventories, checks its placements through physical rotations, and checks
  lower witnesses and arithmetic regimes. It is the longer audit.

The first two run in `make check`; `make check-cuboids` runs all three and
the focused Lean build. Each prints its results to standard output.

For an additional exhaustive bounded audit of the weighted-triangle lemma:

```sh
c++ -std=c++20 -O3 scripts/cuboids/check_weighted.cpp -o /tmp/check-weighted
/tmp/check-weighted
```

These audits supplement the symbolic proofs. Bounded tests and sampled
inventories do not establish the universal thresholds.
