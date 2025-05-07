# MetaCoqAnimation

Project to implement and verify an animation algorithm for the WebAssembly semantics in MetaRocq.


## Building

You have to have the `rocq-released` registry of `opam`. You can obtain it by running `opam repo add rocq-released https://rocq-prover.org/opam/released` if you do not already have it.

To install the dependencies, run `opam install . --deps-only`. The project builds at least with Rocq 9.0.0.

To build the project use `make`.
