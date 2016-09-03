#
# Makefile
#

.SUFFIXES:
.SUFFIXES: .dvi .pdf .ps .tex .eps .jpg .png .bbl .aux .ppm .pnm .png .gif .jpg .cfg .elf .out .dep .stex .spdf

SLIDE=	slide

# HANDOUT= $(subst .pdf,.spdf,$(SLIDE))
HANDOUT= handout
TMP=  tmp
BACKDIR= back

LATEX=   platex --kanji=utf8
DVIPDFM= dvipdfmx

all:	$(SLIDE).pdf

handout:
	rm -f $(TMP).*
	sed -e 's/dvipdfmx/dvipdfmx,handout/' $(SLIDE).tex > $(TMP).tex
	$(LATEX) $(TMP).tex && $(LATEX) $(TMP).tex && $(DVIPDFM) $(TMP)
	pdfnup --a4paper --keepinfo --nup 2x2 --frame true --scale 0.9 --landscape --outfile $(HANDOUT).pdf $(TMP).pdf
	/bin/rm -f $(TMP).*

backup:
	/bin/cp *.tex *.eps *.obj Makefile $(BACKDIR)

clean:
	/bin/rm -f *.dvi *.out *.nav *.snm *.vrb *.toc *.aux *.log $(TMP).*

.tex.dvi:
	$(LATEX) $< && $(LATEX) $<

.dvi.pdf: 
	$(DVIPDFM) $<
