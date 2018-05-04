MODULES  := MSNorm
VS            := $(MODULES:%=src/%.v)
TEX           := $(MODULES:%=latex/%.v.tex)
VS_DOC        := $(MODULES:%=%.v)

.PHONY: coq clean doc html pdf

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) \
		COQC = "coqc -R src MSNorm" \
		COQDEP = "coqdep -R src MSNorm" \
		-o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend 
	cd latex; rm -f *.log *.aux *.dvi *.v.tex *.toc *.bbl *.blg *.idx *.ilg *.pdf *.ind *.out *.fls *.gz *.fdb_latexmk

doc: latex/MSNorm.pdf

COQDOC = coqdoc -R . MSNorm

latex/%.v.tex: Makefile src/%.v src/%.glob
	cd src ; $(COQDOC) --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/MSNorm.pdf: latex/MSNorm.tex $(TEX) latex/MSNorm.bib
	cd latex ; pdflatex MSNorm ; pdflatex MSNorm ; bibtex MSNorm ; pdflatex MSNorm ; pdflatex MSNorm

latex/%.pdf: latex/%.tex latex/MSNorm.bib
	cd latex ; pdflatex $* ; pdflatex $* ; bibtex $* ; makeindex $* ; pdflatex $* ; pdflatex $*

html: Makefile $(VS) src/toc.html
	mkdir -p html
	cd src ; $(COQDOC) --interpolate --no-externals $(VS_DOC) \
		-d ../html
	cp src/toc.html html/

PDF_OPEN = xdg-open latex/MSNorm.pdf&		

ifeq ($(OS),Windows_NT) # Se o Sistema Operacional for Windows...
else # Caso o Sistema Operacional seja Mac OS, modifica-se a variável pdf
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S), Darwin)
PDF_OPEN = open -a Skim latex/MSNorm.pdf&
endif
endif

# Assume-se o Linux como sistema operacional padrão
pdf:    doc
	$(PDF_OPEN)


