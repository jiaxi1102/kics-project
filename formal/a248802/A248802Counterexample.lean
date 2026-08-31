import Mathlib

/-- OEIS A248802: the least prime factor of `2^(2^n+2) + 3`. -/
def A248802 (n : ℕ) : ℕ :=
  (2 ^ (2 ^ n + 2) + 3).minFac

/-- The inner exponent at index 7044 is 206 modulo 233. -/
theorem innerExponent_mod_233 :
    (2 ^ 7044 + 2) % 233 = 206 := by
  have hpow : (2 : ZMod 233) ^ 7044 = 204 := by
    calc
      (2 : ZMod 233) ^ 7044 = (2 : ZMod 233) ^ (26 + 29 * 242) := by norm_num
      _ = (2 : ZMod 233) ^ 26 * ((2 : ZMod 233) ^ 29) ^ 242 := by
        rw [pow_add, pow_mul]
      _ = 204 := by norm_num
  have hcast : ((2 ^ 7044 + 2 : ℕ) : ZMod 233) = 206 := by
    push_cast
    rw [hpow]
    norm_num
  have hmod := (ZMod.natCast_eq_natCast_iff' (2 ^ 7044 + 2) 206 233).mp hcast
  norm_num at hmod ⊢
  exact hmod

/-- The huge outer power is reduced using the order-233 relation modulo 1399. -/
theorem outerPower_mod_1399 :
    (2 : ZMod 1399) ^ (2 ^ 7044 + 2) = 1396 := by
  calc
    (2 : ZMod 1399) ^ (2 ^ 7044 + 2) =
        (2 : ZMod 1399) ^
          (((2 ^ 7044 + 2) % 233) + 233 * ((2 ^ 7044 + 2) / 233)) := by
            rw [Nat.mod_add_div]
    _ = (2 : ZMod 1399) ^ ((2 ^ 7044 + 2) % 233) *
          (((2 : ZMod 1399) ^ 233) ^ ((2 ^ 7044 + 2) / 233)) := by
            rw [pow_add, pow_mul]
    _ = 1396 := by
      rw [innerExponent_mod_233]
      norm_num

/-- A compact independently checkable divisor certificate. -/
theorem divisor_1399_at_7044 :
    1399 ∣ 2 ^ (2 ^ 7044 + 2) + 3 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [outerPower_mod_1399]
  norm_num

/-- Therefore the least prime factor at index 7044 is strictly below 1669. -/
theorem A248802_at_7044_ne_1669 :
    A248802 7044 ≠ 1669 := by
  intro h
  have hleast :
      (2 ^ (2 ^ 7044 + 2) + 3).minFac ≤ 1399 :=
    Nat.minFac_le_of_dvd (by norm_num) divisor_1399_at_7044
  change (2 ^ (2 ^ 7044 + 2) + 3).minFac = 1669 at h
  omega

/--
OEIS A248802 Conjecture 5 is false as stated.
The parameter `n = 51` satisfies `n % 5 ≠ 2`, but its sequence index is
`138 * 51 + 6 = 7044`, where 1399 already divides the defining number.
-/
theorem oeis_A248802_conjecture_5_disproof :
    ¬ (∀ n : ℕ, n % 5 ≠ 2 → A248802 (138 * n + 6) = 1669) := by
  intro h
  have h51 : A248802 (138 * 51 + 6) = 1669 := h 51 (by norm_num)
  have hindex : 138 * 51 + 6 = (7044 : ℕ) := by norm_num
  rw [hindex] at h51
  exact A248802_at_7044_ne_1669 h51
