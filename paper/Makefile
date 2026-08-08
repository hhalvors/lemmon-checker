# Build the paper and put it where the web app serves it from.
#
# The /paper route reads static/lemmon-fitch.pdf, and static/ is copied into
# the Docker image at build time. So editing the .tex and recompiling is not
# enough: the PDF has to reach static/ and be committed. Forgetting that step
# is how a paper comes to document a version that no longer exists, which is
# the failure this file exists to prevent.
#
#   make        build and install
#   make clean  remove the LaTeX droppings

TEX  := lemmon-fitch.tex
PDF  := lemmon-fitch.pdf
DEST := ../static/$(PDF)

.PHONY: all clean

all: $(DEST)

# Twice, so that cross-references to theorems and sections resolve.
$(PDF): $(TEX)
	pdflatex -interaction=nonstopmode $(TEX)
	pdflatex -interaction=nonstopmode $(TEX)

$(DEST): $(PDF)
	cp $(PDF) $(DEST)
	@echo
	@echo "Installed to $(DEST) -- remember to commit it."

clean:
	rm -f *.aux *.log *.out *.toc
