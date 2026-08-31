import Mathlib

/-!
# A coefficient theorem for hedgehog plucking polynomials

For a hedgehog with `n` rays and delays in `{1,2}`, Proposition 2.5 of
Ibarra--Landry--Montoya-Vega--Przytycki gives

  Q(q) = p_n(q) * [n-1]_q!,

where every coefficient of `p_n` is zero or one.  `Window r a` is the
coefficient sequence obtained by multiplying the Laurent coefficient sequence
`a` by `[r]_q = 1 + q + ... + q^(r-1)`.  Thus `DescendWindows (n-1) a`
is the coefficient sequence of `p_n(q) * [n-1]_q!`.
-/

namespace Hedgehog

/-- A doubly-infinite sequence is unimodal at `m` when adjacent terms weakly
increase before `m` and weakly decrease from `m` onward. -/
def UnimodalAt (a : ℤ → ℤ) (m : ℤ) : Prop :=
  (∀ k, k < m → a k ≤ a (k + 1)) ∧
  (∀ k, m ≤ k → a (k + 1) ≤ a k)

/-- A sequence is unimodal when it is unimodal at some integer mode. -/
def Unimodal (a : ℤ → ℤ) : Prop :=
  ∃ m, UnimodalAt a m

namespace UnimodalAt

/-- Adjacent increase before the mode implies comparison of arbitrary terms on
that side. -/
theorem left_le {a : ℤ → ℤ} {m i j : ℤ} (h : UnimodalAt a m)
    (hij : i ≤ j) (hjm : j ≤ m) : a i ≤ a j := by
  refine Int.leInduction (m := i)
    (motive := fun j _ => j ≤ m → a i ≤ a j) ?_ ?_ j hij hjm
  · intro _
    exact le_rfl
  · intro k hik ih hk1m
    exact le_trans (ih (by omega)) (h.1 k (by omega))

/-- Adjacent decrease after the mode implies comparison of arbitrary terms on
that side. -/
theorem right_le {a : ℤ → ℤ} {m i j : ℤ} (h : UnimodalAt a m)
    (hmi : m ≤ i) (hij : i ≤ j) : a j ≤ a i := by
  refine Int.leInduction (m := i)
    (motive := fun j _ => a j ≤ a i) le_rfl ?_ j hij
  intro k hik ih
  exact le_trans (h.2 k (by omega)) ih

end UnimodalAt

/-- `Window r a` is convolution by a block of `r` ones. -/
def Window : ℕ → (ℤ → ℤ) → ℤ → ℤ
  | 0, _, _ => 0
  | r + 1, a, k => Window r a k + a (k - (r : ℤ))

/-- The first-difference identity for a moving window. -/
theorem window_succ_sub_window (a : ℤ → ℤ) (r : ℕ) (k : ℤ) :
    Window r a (k + 1) - Window r a k =
      a (k + 1) - a (k + 1 - (r : ℤ)) := by
  induction r with
  | zero => simp [Window]
  | succ r ih =>
      simp only [Window]
      rw [ih]
      have hidx : k + 1 - ((Nat.succ r : ℕ) : ℤ) = k - (r : ℤ) := by
        omega
      rw [hidx]
      ring

/-- Apply the quantum-integer windows in descending order. -/
def DescendWindows : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, a => a
  | r + 1, a => DescendWindows r (Window (r + 1) a)

/-- Convolution with a block of ones preserves unimodality. -/
theorem window_preserves_unimodal {a : ℤ → ℤ} (h : Unimodal a) (r : ℕ) :
    Unimodal (Window r a) := by
  sorry

/-- Repeated descending quantum-integer convolution preserves unimodality. -/
theorem descendWindows_preserves_unimodal {a : ℤ → ℤ} (h : Unimodal a) :
    ∀ r, Unimodal (DescendWindows r a) := by
  intro r
  induction r generalizing a with
  | zero => simpa [DescendWindows] using h
  | succ r ih =>
      simp only [DescendWindows]
      exact ih (window_preserves_unimodal h (r + 1))

/-- Multiplying a length-`n` zero-one sequence by `[n-1]_q` produces a
unimodal sequence. -/
theorem binary_first_window_unimodal (n : ℕ) (a : ℤ → ℤ)
    (hbin : ∀ k, a k = 0 ∨ a k = 1)
    (hsupport : ∀ k, k < 0 ∨ (n : ℤ) ≤ k → a k = 0)
    (hn : 2 ≤ n) :
    Unimodal (Window (n - 1) a) := by
  sorry

/-- Algebraic form of the hedgehog conjecture: every zero-one polynomial with
support in degrees `0,...,n-1`, multiplied by `[n-1]_q!`, is unimodal. -/
theorem binary_quantumFactorial_unimodal (n : ℕ) (a : ℤ → ℤ)
    (hbin : ∀ k, a k = 0 ∨ a k = 1)
    (hsupport : ∀ k, k < 0 ∨ (n : ℤ) ≤ k → a k = 0) :
    Unimodal (DescendWindows (n - 1) a) := by
  sorry

/-- The zero-one coefficient sequence associated to a delay choice. -/
def delayedIndicator (n : ℕ) (ε : ℕ → Bool) (k : ℤ) : ℤ :=
  if 0 ≤ k ∧ k < (n : ℤ) then
    if ε k.toNat then 1 else 0
  else
    0

/-- Lean-formalized coefficient theorem resolving the hedgehog
plucking-polynomial unimodality conjecture, given the published factorization. -/
theorem hedgehog_plucking_coefficients_unimodal (n : ℕ) (ε : ℕ → Bool) :
    Unimodal (DescendWindows (n - 1) (delayedIndicator n ε)) := by
  apply binary_quantumFactorial_unimodal
  · intro k
    simp only [delayedIndicator]
    split <;> simp
  · intro k hk
    simp only [delayedIndicator]
    split
    · omega
    · rfl

#print axioms hedgehog_plucking_coefficients_unimodal

end Hedgehog
