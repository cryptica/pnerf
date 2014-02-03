all: main

main:
	pdflatex -halt-on-error main && \
	bibtex main && \
	pdflatex -halt-on-error main && \
	pdflatex -halt-on-error main


spell:	
	./spellcheck.sh

clean:
	rm -f *~ *.bbl *.blg \#*# *.log *.aux *.thm
	rm -f main.pdf

PHONY: all main mathdraft spell clean