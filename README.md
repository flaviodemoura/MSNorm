# MSNorm
A constructive formalisation of the Modular Strong Normalisation Theorem.

Modularity is a desirable property of rewrite systems because it allows a combined system to inherit the properties of its components. Termination is not modular, nevertheless under certain restrictions modularity can be recovered. In this work we present a formalisation of the Modular Strong Normalisation Theorem in the Coq proof assistant. The formalised proof is constructive in the sense that it does not rely on classical logic, which is interesting from the computational point of view due to the corresponding algorithmic content of proofs.

This repository contains the source file of the Coq formalisation of the Modular Strong Normalisation Theorem and related documentation.

The source file is located in the src directory: src/MSNorm.v.

The documentation of the formalisation can be automatically generated using "make coq" and then "make pdf".

The formalisation is compatible with Coq 8.8.0.
