#
# Makefile
#

.SUFFIXES: .dvi .pdf .ps .tex .eps .jpg .png .bbl .aux .ppm .pnm .png .gif .jpg .cfg .elf .out .dep .stex .spdf

SLIDE=	slide.pdf
HANDOUT= handout.pdf

COMMON= macro.tex

BACKDIR= back
TMPDIR=  tmp

LATEX=   platex --kanji=utf
DVIPDFM= dvipdfmx

all:	slide handout

handout:	$(HANDOUT)

slide:	$(SLIDE)

backup:
	/bin/cp *.tex *.eps *.obj Makefile $(BACKDIR)

clean:
	/bin/rm -f *.dvi *.out *.nav *.snm *.vrb *.toc *.aux *.log *.pdf

.tex.dvi:
	$(LATEX) $< && $(LATEX) $<

.dvi.pdf:
	$(DVIPDFM) $<

handout.tex:	slide.tex
	/bin/rm -f handout.tex
	sed -e 's/]{beamer}/,handout]{beamer} \\usepackage{pgfpages} \\pgfpagesuselayout{4 on 1}[a4paper,landscape,border shrink=5mm]/' slide.tex > handout.tex
	$(LATEX) handout && $(LATEX) handout && $(DVIPDFM) handout.dvi
