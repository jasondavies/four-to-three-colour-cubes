all: lean

lean:
	lake build

check:
	bash scripts/check.sh

check-thin:
	python3 -S research/thin-cuboids/audit.py
	python3 -S research/thin-cuboids/strip_audit.py
	lake build ThreeColour.Thin

comparator:
	bash scripts/verify-comparator.sh

paper:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/four-to-three-colour-cubes.tex

regenerate:
	python3 scripts/generate_three_colour_lean.py
	python3 scripts/generate_frame_data.py

figure:
	python3 scripts/generate_figure.py

.PHONY: all lean check check-thin comparator paper regenerate figure
