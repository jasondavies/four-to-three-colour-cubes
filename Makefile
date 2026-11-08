all: lean

lean:
	lake build

check:
	bash scripts/check.sh

check-cuboids:
	python3 -S scripts/cuboids/check_geometry.py
	python3 -S scripts/cuboids/check_coordinates.py
	python3 -S scripts/cuboids/check_construction.py
	LEAN_NUM_THREADS=1 lake build ThreeColour.Cuboid ThreeColour.CuboidCorollaryChecks

comparator:
	bash scripts/verify-comparator.sh

paper:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/four-to-three-colour-cubes.tex

regenerate:
	python3 scripts/generate_three_colour_lean.py
	python3 scripts/generate_frame_data.py

figure:
	python3 scripts/generate_figure.py

.PHONY: all lean check check-cuboids comparator paper regenerate figure
