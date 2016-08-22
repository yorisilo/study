#
# Makefile
#

.SUFFIXES:
.SUFFIXES: .dvi .pdf .ps .tex .eps .jpg .png .bbl .aux .ppm .pnm .png .gif .jpg .cfg .elf .out .dep .stex .spdf

SOURCE= paper.tex sec1.tex sec2.tex sec3.tex sec4.tex sec5.tex
TARGET= paper
PLATEX=platex --kanji=utf
BIBTEX=bibtex
DVIPDFM=dvipdfmx

all: 	$(TARGET).pdf

paper.pdf:	$(SOURCE)
	$(PLATEX) $(TARGET) && $(BIBTEX) $(TARGET)  && \
	$(PLATEX) $(TARGET) && $(DVIPDFM) $(TARGET)

.PHONY:	backup
backup:
	/bin/cp -f $(SOURCE) Makefile back

.PHONY:	clean
clean:
	/bin/rm -f *.dvi *.aux *.out *.pdf

.PHONY:	allclean
allclean:
	/bin/rm -f *.dvi *.aux *.out *.pdf
