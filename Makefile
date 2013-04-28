default : Projectivity.pdf

Projectivity.tex : Projectivity.lhs
	lhs2TeX Projectivity.lhs > Projectivity.tex

Projectivity.aux : Projectivity.tex
	xelatex Projectivity

Projectivity.blg : Projectivity.aux
	bibtex Projectivity

Projectivity.pdf : Projectivity.tex Projectivity.blg
	xelatex Projectivity
	xelatex Projectivity

