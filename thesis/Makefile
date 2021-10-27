correct_round_elimination.pdf: correct_round_elimination.tex correct_round_elimination.bbl
	pdflatex -shell-escape correct_round_elimination
	pdflatex -shell-escape correct_round_elimination

correct_round_elimination.bbl: correct_round_elimination.bib
	pdflatex -shell-escape correct_round_elimination
	bibtex correct_round_elimination

clean:
	rm *.bbl *.aux *.blg *.log *.out *.toc *.pdf *.xmpdata pdfa.xmpi
