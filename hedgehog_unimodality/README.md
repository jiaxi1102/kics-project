# Hedgehog plucking-polynomial unimodality

This isolated Lean 4 package formalizes the new coefficient theorem used to
resolve Conjecture 4.1 of Ibarra, Landry, Montoya-Vega, and Przytycki:
hedgehog trees whose leaf delays lie in `{1,2}` have unimodal plucking
polynomials.

The published factorization is

```text
Q(T,f) = p_n(q) [n-1]_q!,
p_n(q) = epsilon_0 + epsilon_1 q + ... + epsilon_(n-1) q^(n-1),
epsilon_i in {0,1}.
```

The proof has two ingredients.

1. `p_n(q)[n-1]_q` is unimodal. Away from the two central candidate modes,
   its first differences are automatically nonnegative on the left and
   nonpositive on the right. The only undecided comparison is
   `c_(n-1)-c_(n-2)=epsilon_(n-1)-epsilon_0`, which merely selects one of the
   two adjacent modes.
2. Multiplication by every further quantum integer `[r]_q` preserves
   unimodality. If `b` is the moving window of width `r` over `a`, then
   `b_(k+1)-b_k = a_(k+1)-a_(k+1-r)`. Before the mode this is nonnegative,
   after the window passes the mode it is nonpositive, and through the
   transition it is nonincreasing, so it can change sign at most once.

`Hedgehog.lean` proves the general zero-one coefficient theorem. CI requires:

- Lean elaboration and `lake build`;
- axiom audit, allowing only Lean's standard `propext`, `Classical.choice`,
  and `Quot.sound`;
- independent checking with `nanoda`;
- rejection of `sorry`.

The exact CI transcript is committed as `hedgehog-verification.log` on this
branch.
