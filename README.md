# Kot-Proof

`kot-proof` is a Rocq formalisation of the [`kot` OCaml library](https://github.com/fpottier/kot) that offers an implementation of Kaplan,
Okasaki, and Tarjan's persistent catenable deques,
as described in the paper
[Simple Confluently Persistent Catenable Lists](http://www.aladdin.cs.cmu.edu/papers/pdfs/y2000/catenable.pdf).

It offers proofs of correctness, thread-safety and O(1) amortised single-threaded time complexity.

# Related Article

If you are coming from the corresponding article, the main theorems are showcased in `theories/article.v`.

## What order to read the files

- `common.v` contains the axioms for buffers and the Heaplang implementation for deques
- `tick.v` contains axioms for time credits (listed as axioms but implementations are available)
- `shared_ref.v` contains the two stable reference interfaces
- `deque_(corr|cost).v` contains the definition of the deque predicate for the given proof
- `(push|concat|pop)_(corr|cost).v`/`(pop|eject)_(corr|cost)_lemmas.v` ontains the proof for the specific function, either the cost or correction analysis

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
