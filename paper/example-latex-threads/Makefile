# Makefile for papers
MAIN = main
.PHONY: clean open spell

all: $(MAIN).pdf

$(MAIN).pdf: *.tex $(MAIN).bbl
	pdflatex $(MAIN)
	pdflatex $(MAIN)

$(MAIN).bbl: biblio.bib $(MAIN).tex
	pdflatex $(MAIN)
	bibtex $(MAIN)

spell:
	aspell -t -c $(MAIN).tex


# Run once, then re-run until it's happy
# Input redirected from /dev/null is like hitting ^C at first error
latex:
	@echo latex $(MAIN).tex </dev/null
	@if latex $(MAIN).tex </dev/null; then \
		true; \
	else \
		stat=$$?; touch $(MAIN).dvi; exit $$stat; \
	fi 
	bibtex $(MAIN) || true
	@echo latex $(MAIN).tex </dev/null
	@while grep "Rerun to get cross" $(MAIN).log; do \
		echo latex $(MAIN).tex </dev/null; \
		if latex $(MAIN).tex </dev/null; then \
			true; \
		else \
			stat=$$?; touch $(MAIN).dvi; exit $$stat; \
		fi; \
	done
	dvips -e 0 -t letter -P pdf -o $(MAIN).ps $(MAIN).dvi ;

clean:
	rm -f $(MAIN).aux $(MAIN).bbl $(MAIN).log $(MAIN).out $(MAIN).ps $(MAIN).pdf $(MAIN).dvi $(MAIN).blg *.bak *.auto *~




