PDF=main.pdf
TEX=main.tex

.PHONY: all clean

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX)

clean:
	latexmk -C

