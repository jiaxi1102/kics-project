# Proof of the zero-one quantum-factorial theorem

## Theorem

Let

\[
p(q)=\sum_{i=0}^{n-1}\varepsilon_iq^i,
\qquad \varepsilon_i\in\{0,1\}.
\]

Then

\[
p(q)[n-1]_q!
\]

has a unimodal coefficient sequence, where
\([r]_q=1+q+\cdots+q^{r-1}\).

Together with Proposition 2.5 of Ibarra--Landry--Montoya-Vega--Przytycki,
which identifies a hedgehog plucking polynomial with exactly this product,
this proves their Conjecture 4.1 for delays in `{1,2}`.

## 1. The first quantum-integer factor

Extend the coefficient sequence by zero outside `0,...,n-1`; write it as
`a_k`. Let `c_k` be the coefficient of `q^k` in `p(q)[n-1]_q`. Thus

\[
c_k=\sum_{j=0}^{n-2}a_{k-j}.
\]

Adjacent coefficients satisfy the telescoping identity

\[
c_{k+1}-c_k=a_{k+1}-a_{k-n+2}.
\]

There are only three regimes.

- If `k<n-2`, then `k-n+2<0`, so the exiting term vanishes and
  `c_{k+1}-c_k=a_{k+1}\ge 0`.
- If `k=n-2`, then
  `c_{n-1}-c_{n-2}=a_{n-1}-a_0`. This single comparison chooses whether the
  mode is `n-2` or `n-1`.
- If `k\ge n-1`, then `a_{k+1}=0`, so
  `c_{k+1}-c_k=-a_{k-n+2}\le 0`.

Hence `p(q)[n-1]_q` is unimodal.

## 2. A moving window preserves unimodality

Let `(a_k)` be any weakly unimodal sequence and let

\[
b_k=\sum_{j=0}^{r-1}a_{k-j}.
\]

Again,

\[
b_{k+1}-b_k=a_{k+1}-a_{k+1-r}. \tag{1}
\]

Suppose `a` has a mode at `m`. Choose the least `t` in `0,...,r-1` for which

\[
a_{m+t+1}\le a_{m+t+1-r}. \tag{2}
\]

Such a `t` exists: at `t=r-1`, inequality (2) is
`a_{m+r}\le a_m`, which follows from the nonincreasing right side of `a`.

For `k<m+t`, the right-hand side of (1) is nonnegative:

- before `m`, both compared indices lie on the nondecreasing side;
- from `m` to `m+t-1`, nonnegativity follows from the minimality of `t`.

For `k\ge m+t`, it is nonpositive:

- once `k\ge m+r-1`, both compared indices lie on the nonincreasing side;
- in the transition range, the leading endpoint `a_{k+1}` can only decrease,
  while the trailing endpoint `a_{k+1-r}` can only increase. Inequality (2)
  therefore persists.

Thus `b_k` increases up to `m+t` and decreases afterward. Multiplication by
`[r]_q` preserves unimodality.

## 3. Finish

By Section 1, `p(q)[n-1]_q` is unimodal. Apply the moving-window lemma
successively for

\[
[n-2]_q,[n-3]_q,\ldots,[1]_q.
\]

The final product is `p(q)[n-1]_q!`, so it is unimodal.

## Lean correspondence

In `Hedgehog.lean`:

- `Window r a` is the coefficient sequence after multiplication by `[r]_q`;
- `window_succ_sub_window` is identity (1);
- `window_preserves_unimodal` formalizes Section 2;
- `binary_first_window_unimodal` formalizes Section 1;
- `binary_quantumFactorial_unimodal` proves the theorem;
- `hedgehog_plucking_coefficients_unimodal` specializes it to arbitrary
  `{1,2}` delay patterns.

The formal theorem is stronger than the required specialization because it
covers every zero-one polynomial supported in `0,...,n-1`.
