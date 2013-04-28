default : Analyze.pdf

Analyze.tex : Analyze.lhs
	lhs2TeX Analyze.lhs > Analyze.tex

Analyze.aux : Analyze.tex
	xelatex Analyze

Analyze.blg : Analyze.aux
	bibtex Analyze

Analyze.pdf : Analyze.tex Analyze.blg
	xelatex analyze
	xelatex analyze

