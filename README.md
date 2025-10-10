# Kot-Proof

`kot-proof` is a Rocq formalisation of the [`kot` OCaml library](https://github.com/fpottier/kot) that offers an implementation of Kaplan,
Okasaki, and Tarjan's persistent catenable deques,
as described in the paper
[Simple Confluently Persistent Catenable Lists](http://www.aladdin.cs.cmu.edu/papers/pdfs/y2000/catenable.pdf).

It offers proofs of correctness, thread-safety and O(1) amortised single-threaded time complexity.

# Related Article

If you are coming from the corresponding article, the main theorems are showcased in `theories/article.v`.

# Compiling the Proof

First, install the dependencies:
```sh
make install-deps
```

Then, activate the opam switch and compile the project:
```sh
eval $(opam env --switch=kot-proof)
make
```
