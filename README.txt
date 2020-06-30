This is a prototypical implementation exemplifying the concept of local 
higher-order fixpoint iteration. It is written in OCaml. 

Make sure that the executable `ocamlc' is available, and possibly set the
path to it in Makefile. Then execute

> make all

to create executables example<i>. These show the evaluation of a (possibly
nested) higher-order fixpoint formula over particular structures. The 
examples are described in the paper "Local Higher-Order Fixpoint Iteration"
by F. Bruse, M. Lange, M. Sälzer of the University of Kassel, Germany, and
J. Kreiker of the University of Applied Sciences Fulda, Germany. 

- example1 formalises a non-context-free reachability problem
- example2 parses a word w.r.t. a higher-order grammar
