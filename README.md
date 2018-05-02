# Sequent Prover

Implementation of Lukas Stevens & Joshua von Mutius

# Build Information

To build the test executable run `ocamlbuild tests.native`

The tests output the graphviz representatio of the proof trees.
e.g.


Test Test<Number>:
digraph etc {
...
}


Even though there are function declaration which do not have exhaustive pattern
matches those are only used in functions where there always is a node and not
something else.
