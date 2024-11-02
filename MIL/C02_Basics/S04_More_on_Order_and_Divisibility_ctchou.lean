import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
--  sorry
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h

lemma lem0 : ∀ x y : ℝ, min x y = min y x := by
  intro x y
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

lemma lem1 : ∀ x y z : ℝ, x ≤ y → min x z ≤ min y z := by
  intro x y z h
  apply le_min
  . have h' : min x z ≤ x := by apply min_le_left
    apply le_trans h' h
  . apply min_le_right

lemma lem2 : ∀ x y z : ℝ, min (min x y) z ≤ min x (min y z) := by
  intro x y z
  apply le_min
  . calc min (min x y) z ≤ min x y := by apply min_le_left
                       _ ≤ x := by apply min_le_left
  . apply lem1
    apply min_le_right

example : min (min a b) c = min a (min b c) := by
--  sorry
  apply le_antisymm
  . apply lem2
  . rw [(lem0 a (min b c)), (lem0 (min a b) c), (lem0 b c), (lem0 a b)]
    apply lem2

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
--  sorry
  apply le_min
  . have h1 : min a b ≤ a := by apply min_le_left
    linarith
  . have h2 : min a b ≤ b := by apply min_le_right
    linarith

example : min a b + c = min (a + c) (b + c) := by
--  sorry
  apply le_antisymm
  . apply aux
  . have h1 : min (a + c) (b + c) ≤ a + c := by apply min_le_left
    have h2 : min (a + c) (b + c) ≤ b + c := by apply min_le_right
    have h1' : min (a + c) (b + c) - c ≤ a := by linarith
    have h2' : min (a + c) (b + c) - c ≤ b := by linarith
    have h3 : min (a + c) (b + c) - c ≤ min a b := by apply le_min h1' h2'
    linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
--  sorry
  have h1: |a| ≤ |a - b| + |b| := by
    calc |a| = |(a - b) + b| := by ring
           _ ≤ |a - b| + |b| := by apply abs_add
  linarith

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
--  sorry
  have h' : ∃ u, w = u * x := by
    apply exists_eq_mul_left_of_dvd
    exact h
  rcases h' with ⟨u, h'⟩
  rw [h']
  apply dvd_iff_exists_eq_mul_left.mpr
  use (y*z + x + u * u * x)
  ring

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
--  sorry
  have h : ∀ x y : ℕ, gcd x y ∣ gcd y x := by
    intro x y
    apply dvd_gcd
    apply gcd_dvd_right
    apply gcd_dvd_left
  apply Nat.dvd_antisymm
  apply h
  apply h

end
