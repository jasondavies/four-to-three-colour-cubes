all: lean

lean:
	lake build

check:
	bash scripts/check.sh

comparator:
	bash scripts/verify-comparator.sh

paper:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/four-to-three-colour-cubes.tex

regenerate:
	python3 scripts/generate_three_colour_lean.py

figure:
	python3 scripts/generate_figure.py

.PHONY: all lean check comparator paper regenerate figure
