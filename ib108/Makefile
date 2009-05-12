files = sada3.pdf

all: $(files)
	xpdf -remote latex -reload

$(files): %.pdf: %.tex
	pdflatex $<
	pdflatex $<

clean:
	-rm -f *.log *.aux *.out
