PANDOC = pandoc
IFORMAT = markdown

FLAGS = --standalone --mathjax=$(MATHJAX)


ifdef MATHJAX_LOCAL
  MATHJAX = ${MATHJAX_LOCAL}
else
  MATHJAX ?= "https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML"
endif

TEMPLATE_HTML = template/template.html

all: index.html protocols.html symmetric.html asymmetric.html

index.html: index_src.md $(TEMPLATE_HTML)
	$(PANDOC) \
	  --template $(TEMPLATE_HTML)\
          --citeproc\
	  -t html -o $@ $<

protocols.html: protocols_src.md $(TEMPLATE_HTML)
	$(PANDOC) \
	  --template $(TEMPLATE_HTML)\
          --citeproc\
	  --syntax ressources/cross-tool-syntax.xml \
	  -t html -o $@ $<

symmetric.html: symmetric_src.md $(TEMPLATE_HTML)
	$(PANDOC) \
	  --template $(TEMPLATE_HTML)\
          --citeproc\
	  -t html -o $@ $<

asymmetric.html: asymmetric_src.md $(TEMPLATE_HTML)
	$(PANDOC) \
	  --template $(TEMPLATE_HTML)\
          --citeproc\
	  -t html -o $@ $<

clean:
	-rm -f *.html
