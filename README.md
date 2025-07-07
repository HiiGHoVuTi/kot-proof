# Kot-Proof

`kot-proof` is a Rocq formalisation of the [`kot` OCaml library](https://github.com/fpottier/kot) that offers an implementation of Kaplan,
Okasaki, and Tarjan's persistent catenable deques,
as described in the paper
[Simple Confluently Persistent Catenable Lists](http://www.aladdin.cs.cmu.edu/papers/pdfs/y2000/catenable.pdf).

It offers proofs of correctness, thread-safety and O(1) amortised single-threaded time complexity.
