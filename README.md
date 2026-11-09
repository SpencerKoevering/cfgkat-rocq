# CF-GKAT in Rocq

Rocq formalization accompanying the paper *CF-GKAT: A Complete Calculus for
Non-Local Control Flow* by Spencer Van Koevering, Alexandra Silva, Cheng Zhang,
and Tobias Kappé.

The `[Rocq]` links in the paper point to the tag `arxiv-v1` of this repository.

## Building

Requires the Rocq Prover 9.1 or 9.2 with its standard library
(e.g. `opam install rocq-prover`).

```sh
make -f CoqMakefile          # compile everything
make -f CoqMakefile html     # rocqdoc HTML in html/
```

## Layout

- `syntax/`: expressions, tests, and the axioms (`Axioms.v`)
- `semantics/`: automata, label resolution, expression semantics, bisimulation
- `soundness/`: soundness of the axioms (`Soundness.v`)
- `completeness/`: the fundamental theorem and completeness (`Completeness.v`)
- `examples/`: case studies; `main.v` checks the main results
