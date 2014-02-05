all: main

main:
	pdflatex -halt-on-error main && \
	bibtex main && \
	pdflatex -halt-on-error main && \
	pdflatex -halt-on-error main

pdf: all

clean:
	rm -f *.aux *.pdf *.log *.gz *.bbl *.blg *.aux
