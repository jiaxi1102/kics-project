# Hedgehog plucking-polynomial unimodality

## Status

This directory contains a proposed resolution of Conjecture 4.1 from Ibarra,
Landry, Montoya-Vega, and Przytycki, together with a machine-checked Lean 4
formalization of the coefficient theorem. The argument has not yet been
peer-reviewed or priority-confirmed by the original authors.

## Problem and reduction

For a hedgehog (star) rooted tree with `n` rays and delays in `{1,2}`, the
published Proposition 2.5 gives

```text
Q(T,f) = p_n(q) [n-1]_q!,
p_n(q) = epsilon_0 + epsilon_1 q + ... + epsilon_(n-1) q^(n-1),
epsilon_i in {0,1}.
```

The paper asks whether every such `Q(T,f)` is unimodal.

## Stronger coefficient theorem

For every `n` and every zero-one polynomial `p_n` supported in degrees
`0,...,n-1`, the polynomial

```text
p_n(q) [n-1]_q!
```

is unimodal. This is stronger than the hedgehog conjecture because it applies
to every zero-one coefficient pattern, independent of whether that pattern is
viewed as a delay function.

The proof has two ingredients.

1. `p_n(q)[n-1]_q` is unimodal. Its coefficient differences are nonnegative
   before the two central indices and nonpositive after them. The only middle
   difference is `epsilon_(n-1)-epsilon_0`, which selects one of two adjacent
   modes.
2. Multiplication by any further quantum integer `[r]_q` preserves
   unimodality. If `b_k = a_k + ... + a_(k-r+1)`, then
   `b_(k+1)-b_k = a_(k+1)-a_(k+1-r)`. For a unimodal `a`, this comparison can
   cross from nonnegative to nonpositive at most once.

See `PROOF.md` for the mathematical proof.

## Formalization boundary

`Hedgehog.lean` formalizes the complete coefficient argument, including the
moving-window preservation theorem and the final universal zero-one theorem.
It does not re-formalize the recursive rooted-tree definition of `Q(T,f)` or
reprove Proposition 2.5; the last bridge from the coefficient theorem to the
original tree conjecture uses that published factorization.

## Reproduce

Pinned versions: Lean `4.33.1`, mathlib `v4.33.1`.

```bash
lake update
lake build
lake env lean Hedgehog.lean
```

CI additionally rejects `sorry`/`admit`, checks the compiled environment with
Lean's official `leanchecker`, and runs an axiom audit allowing only
`propext`, `Classical.choice`, and `Quot.sound`.
