all: lean

lean:
	lake build

check:
	bash scripts/check.sh

comparator:
	bash scripts/palomar/verify-comparator.sh

paper:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/macmahon-four-to-three.tex

regenerate:
	python3 scripts/generate_three_colour_lean.py

.PHONY: all lean check comparator paper regenerate
