# Real Numbers Formalized as Dedekind Cuts in Coq

This repository contains a formalization of the real numbers as Dedekind cuts in
Coq, along with proofs of various theorems about them. The formalization is
based on the definitions introduced in Chapter 11.2 of the book [*Homotopy Type
Theory: Univalent Foundations of Mathematics* (2013) by The Univalent
Foundations Program](https://homotopytypetheory.org/book).

## Overview

All the source code is located in `my_reals.v`, and it uses **Coq 8.17.1**. 
It includes the following:
* Type `my_R` representing Dedekind cuts.
* Map `Q_to_R : Q -> my_R`.
* Addition `(+') : my_R -> my_R -> my_R`.
* Additive inverse `(-') : my_R -> my_R`.
* Equality `(=') : my_R -> my_R -> Prop`.
* Proof that `(=')` is an equivalence relation.
* Proof that `(+')` is correct, that is, `(Q_to_R x) +' (Q_to_R y) =' Q_to_R (x + y)`.
  As a corollary, 1 + 1 = 2.
* Proof that `(-')` is correct, that is, `(-' Q_to_R q) =' (Q_to_R (- q))`.
* Proof that `-' -' x =' x`.
* Proof that `(my_R, 0, +', -')` is an abelian group.

## License

This code is licensed under the terms of the MIT license.
