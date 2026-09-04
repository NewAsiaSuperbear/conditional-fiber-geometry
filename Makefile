.PHONY: test paper clean

test:
	python -m pytest

paper:
	cd manuscript && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

clean:
	cd manuscript && latexmk -c main.tex
