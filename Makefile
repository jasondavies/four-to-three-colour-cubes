all: lean

lean:
	lake build

check:
	bash scripts/check.sh

comparator:
	bash scripts/verify-comparator.sh

paper:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/macmahon-four-to-three.tex

regenerate:
	python3 scripts/generate_three_colour_lean.py

figure:
	python3 scripts/generate_figure.py

.PHONY: all lean check comparator paper regenerate figure
