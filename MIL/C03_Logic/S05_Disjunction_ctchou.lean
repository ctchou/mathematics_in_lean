import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
--  sorry
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg] ; exact h
  . rw [abs_of_neg] ; linarith ; exact h

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
--  sorry
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg] ; linarith ; exact h
  . rw [abs_of_neg] ; exact h

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
--  sorry
  rcases le_or_gt 0 (x + y) with h | h
  . rw [abs_of_nonneg h]
    have hx := le_abs_self x
    have hy := le_abs_self y
    linarith
  . rw [abs_of_neg h]
    have hx := neg_le_abs_self x
    have hy := neg_le_abs_self y
    linarith

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
--  sorry
  rcases le_or_gt 0 y with h | h
  . rw [abs_of_nonneg h]
    constructor
    . tauto
    . intro h1
      rcases h1 with h' | h' <;> linarith
  . rw [abs_of_neg h]
    constructor
    . tauto
    . intro h1
      rcases h1 with h' | h' <;> linarith

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
--  sorry
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
    constructor
    . intro h1
      constructor <;> linarith
    . tauto
  . rw [abs_of_neg h]
    constructor
    . intro h1
      constructor <;> linarith
    . rintro ⟨h1, h2⟩
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
--  sorry
  rcases h with ⟨x, y, h⟩
  have hx : 0 ≤ x^2 := pow_two_nonneg x
  have hy : 0 ≤ y^2 := pow_two_nonneg y
  rcases h with h | h <;> linarith

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
--  sorry
  have h1 : (x - 1) * (x + 1) = 0 := by
    calc (x - 1) * (x + 1) = x^2 - 1 := by ring
         _ = 0 := by linarith
  have h2 : x - 1 = 0 ∨ x + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h3
  . left ; linarith
  . right ; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
--  sorry
  have h1 : (x - y) * (x + y) = 0 := by
    calc (x - y) * (x + y) = x^2 - y^2 := by ring
         _ = 0 := by linarith
  have h2 : x - y = 0 ∨ x + y = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h3
  . left ; linarith
  . right ; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)
omit [IsDomain R]

lemma aux : ∀ a b : R, a + b = 0 → a = -b := by
  intro a b h
  calc a = a + b + -b := by abel
       _ = -b := by simp [h]

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
--  sorry
  have h1 : (x - 1) * (x + 1) = 0 := by
    calc (x - 1) * (x + 1) = x^2 - 1 := by ring
         _ = 0 := by {rw [h] ; ring }
  have h2 : x - 1 = 0 ∨ x + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h3
  . left ; apply eq_of_sub_eq_zero h3
  . right ; apply aux x 1 h3

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
--  sorry
  have h1 : (x - y) * (x + y) = 0 := by
    calc (x - y) * (x + y) = x^2 - y^2 := by ring
         _ = 0 := by simp [h]
  have h2 : x - y = 0 ∨ x + y = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h3
  . left ; apply eq_of_sub_eq_zero h3
  . right ; apply aux x y h3

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
--  sorry
  constructor
  . intro h
    by_cases h' : P
    . right ; apply h h'
    . left ; exact h'
  . intro h
    rcases h with h' | h'
    . by_contra! h''
      apply h' h''.1
    . intro h''
      exact h'
