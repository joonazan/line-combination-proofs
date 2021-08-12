plan.pdf: plan.tex plan.bbl
	pdflatex plan.tex
	pdflatex plan.tex

plan.bbl: plan.bib plan.aux
	bibtex plan

plan.aux: plan.tex
	pdflatex plan.tex
