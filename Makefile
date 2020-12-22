OCAMLC=ocamlc

all:
	$(OCAMLC) HOFPIteration.ml example1.ml -o example1
	$(OCAMLC) HOFPIteration.ml example2.ml -o example2
	$(OCAMLC) HOFPIteration.ml example3.ml -o example3
	$(OCAMLC) HOFPIteration.ml example4.ml -o example4
