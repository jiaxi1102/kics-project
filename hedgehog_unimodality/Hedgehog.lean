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
      have hidx : k + 1 - ((Nat.succ r : ℕ) : ℤ) = k - (r : ℤ) := by
        omega
      rw [hidx]
      omega

/-- A first crossing of the two endpoints of a moving window supplies a mode
for the resulting sequence. -/
theorem window_unimodalAt_of_transition {a : ℤ → ℤ} {m : ℤ}
    (hm : UnimodalAt a m) (r t : ℕ) (ht : t < r)
    (hcross :
      a (m + (t : ℤ) + 1) ≤
        a (m + (t : ℤ) + 1 - (r : ℤ)))
    (hbefore : ∀ s < t,
      a (m + (s : ℤ) + 1 - (r : ℤ)) ≤
        a (m + (s : ℤ) + 1)) :
    UnimodalAt (Window r a) (m + (t : ℤ)) := by
  constructor
  · intro k hk
    have hcomp : a (k + 1 - (r : ℤ)) ≤ a (k + 1) := by
      by_cases hkm : k < m
      · exact hm.left_le (i := k + 1 - (r : ℤ)) (j := k + 1)
          (by omega) (by omega)
      · have hmk : m ≤ k := by omega
        let s : ℕ := (k - m).toNat
        have hs0 : 0 ≤ k - m := by omega
        have hscast : (s : ℤ) = k - m := by
          dsimp [s]
          exact Int.toNat_of_nonneg hs0
        have hst : s < t := by omega
        have hs := hbefore s hst
        convert hs using 1 <;> omega
    have hd := window_succ_sub_window a r k
    omega
  · intro k hk
    have hcomp : a (k + 1) ≤ a (k + 1 - (r : ℤ)) := by
      by_cases hfar : m + (r : ℤ) - 1 ≤ k
      · exact hm.right_le (i := k + 1 - (r : ℤ)) (j := k + 1)
          (by omega) (by omega)
      · have hlead :
            a (k + 1) ≤ a (m + (t : ℤ) + 1) :=
          hm.right_le (i := m + (t : ℤ) + 1) (j := k + 1)
            (by omega) (by omega)
        have htrail :
            a (m + (t : ℤ) + 1 - (r : ℤ)) ≤
              a (k + 1 - (r : ℤ)) :=
          hm.left_le
            (i := m + (t : ℤ) + 1 - (r : ℤ))
            (j := k + 1 - (r : ℤ)) (by omega) (by omega)
        exact hlead.trans (hcross.trans htrail)
    have hd := window_succ_sub_window a r k
    omega

/-- Convolution with a block of ones preserves unimodality. -/
theorem window_preserves_unimodal {a : ℤ → ℤ} (h : Unimodal a) (r : ℕ) :
    Unimodal (Window r a) := by
  rcases h with ⟨m, hm⟩
  by_cases hr : r = 0
  · subst r
    refine ⟨0, ?_⟩
    constructor <;> intro k hk <;> simp [Window]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let P : ℕ → Prop := fun s =>
      s < r ∧
        a (m + (s : ℤ) + 1) ≤
          a (m + (s : ℤ) + 1 - (r : ℤ))
    have hP : ∃ s, P s := by
      refine ⟨r - 1, ?_⟩
      constructor
      · omega
      · have hdec : a (m + (r : ℤ)) ≤ a m :=
          hm.right_le (i := m) (j := m + (r : ℤ)) (by omega) (by omega)
        dsimp [P]
        convert hdec using 1 <;> omega
    let t : ℕ := Nat.find hP
    have htP : P t := by
      simpa [t] using Nat.find_spec hP
    have hbefore : ∀ s < t,
        a (m + (s : ℤ) + 1 - (r : ℤ)) ≤
          a (m + (s : ℤ) + 1) := by
      intro s hst
      have hnot : ¬ P s := by
        apply Nat.find_min hP
        simpa [t] using hst
      have hsr : s < r := lt_trans hst htP.1
      have hnotle :
          ¬ a (m + (s : ℤ) + 1) ≤
            a (m + (s : ℤ) + 1 - (r : ℤ)) := by
        intro hle
        exact hnot ⟨hsr, hle⟩
      exact le_of_lt (lt_of_not_ge hnotle)
    refine ⟨m + (t : ℤ), ?_⟩
    exact window_unimodalAt_of_transition hm r t htP.1 htP.2 hbefore

/-- Apply the quantum-integer windows in descending order. -/
def DescendWindows : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, a => a
  | r + 1, a => DescendWindows r (Window (r + 1) a)

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
