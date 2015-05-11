# Thanks to: http://adam.chlipala.net/cpdt/html/Large.html

MODULES := Debug Util StringUtil Instruction Graph Execution Graphviz \
  GraphvizCompressed Processor PipeGraph FiveStage FiveStageViCLCreateOnly \
  SimpleFiveStage FiveStageL1Only FiveStageSuperscalar FiveStageOOO \
  FiveStageL1OnlyOOO OpenSPARCT1 Piton
VS      := $(MODULES:%=%.v)
DOCS    := $(MODULES:%=../doc/PipeGraph.%.html)

.PHONY: all coq doc clean

all: coq doc pipecheck

pipecheck: Main.native
	cp Main.native pipecheck

Main.native: Main.ml PipeGraph.ml HerdGraph.ml coq
	ocamlbuild $@

PipeGraph.ml: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

doc: coq $(VS)
	mkdir -p ../doc
	coqdoc --html -d ../doc $(VS)

Makefile.coq: Makefile $(VS)
	coq_makefile  $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ocamlbuild -clean Main.native
	-rm -f pipecheck
	-rm -f PipeGraph.ml
	-rm -f PipeGraph.mli
	-rm -f Makefile.coq
	-rm -f $(DOCS)
	-rm -f ../doc/index.html
	-rm -f ../doc/coqdoc.css
