This is a prototypical implementation exemplifying the concept of local 
higher-order fixpoint iteration. It is written in OCaml. 


=== COMPILATION ===

Make sure that the executable `ocamlc' is available, and possibly set the
path to it in Makefile. Then execute

> make all

to create executables. These show the evaluation of a (possibly nested)
higher-order fixpoint formula over particular structures.


=== INCLUDED EXAMPLES ===

The examples are described in the paper "Local Higher-Order Fixpoint
Iteration" by F. Bruse, M. Lange, M. Sälzer of the University of Kassel,
Germany, and J. Kreiker of the University of Applied Sciences Fulda,
Germany. 

- Example 1 formalises a non-context-free reachability problem as an
  order-1 evaluation problem. Usage:

    example1 <n>

  with <n> a natural number. Default is n=2.

- Example 2 formalises a context-sensitive parsing problem as an order-2
  evaluation problem. Usage:

    example2 <s>

  where <s> is a string interpreted as a sequence of tokens for a grammar
  that recognizes words over the alphabet {'b','c','s'} (for 'block', 'code',
  'space'). Default is "bsc". 

- Example 3 formalises a model checking problem for a non-regular property
  as an order-1 evaluation problem. Usage:

    example3 <n>

  with <n> being the number of states of the underlying transition system
  in question. Default is n=2.

- Example 4 formalises a strictness analysis problem applied to a function
  of order 2. Usage:

    example4 <n>

  with <n> being the number of elements in the underlying linear domain.
  Default is n=2.


=== VERBOSITY LEVEL ===

This generic local higher-order fixpoint iteration algorithm, resp. its
implementation is supposed to aid the understanding of the interaction
between higher-order functions and local fixpoint iteration. To this end,
a call to function "evaluate" in a module storing higher-order lattices
with some argument term phi creates a lot of output, telling the user
about the current filling state of function tables in the iteration. The
amount of information printed out can be set to different levels. In
order to change this level, edit HOFPIteration.ml, set the value of the
variable "verbosity" to something between 0 (silent) and 4 (very detailed)
and recompile.


=== CREATING NEW EXAMPLES ===

Follow the pattern seen in example<n>.ml: create a module that defines
a lattice by implementing the type signature Lattice from HOFPIteration.ml.
Functor MakeHOLattice turns this into a module which implements the
corresponding higher-order lattices over this base one, and contains a
function evaluate which takes a muHO term and evaluates it over this
family of lattices. 
