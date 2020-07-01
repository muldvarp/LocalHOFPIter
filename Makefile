OCAMLC=ocamlc

all:
	$(OCAMLC) HOFPIteration.ml example1.ml -o example1
	$(OCAMLC) HOFPIteration.ml example2.ml -o example2
