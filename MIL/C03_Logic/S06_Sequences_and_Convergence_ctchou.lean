import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
--  . linarith
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
--  sorry
  intro N hN
  rw [ge_iff_le, max_le_iff] at hN
  have hs' : |s N - a| < ε/2 := hs N hN.1
  have ht' : |t N - b| < ε/2 := ht N hN.2
  calc |s N + t N - (a + b)| = |(s N - a) + (t N - b)| := by abel_nf
       _ ≤ |(s N - a)| + |(t N - b)| := by apply abs_add_le
       _ < ε/2 + ε/2 := by linarith
       _ = ε := by linarith

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
--  sorry
  intro ε hε
  simp
  have hc : 0 < ε / |c| := by { apply div_pos hε acpos }
  rcases cs (ε/|c|) hc with ⟨Ns, hs⟩
  use Ns
  intro n hN
  have hs' : |s n - a| < ε/|c| := by { apply hs n hN }
  calc |c * s n - c * a| = |c * (s n - a)| := by { congr ; ring }
       _ = |c| * |s n - a| := by { rw [abs_mul] }
       _ < |c| * (ε / |c|) := by { apply mul_lt_mul_of_pos_left hs' acpos }
       _ = ε := by { field_simp }

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
--  sorry
  intro n hn
  calc |s n| = |a + (s n - a)| := by { congr ; abel }
           _ ≤ |a| + |s n - a| := by apply abs_add_le
           _ < |a| + 1 := by { apply add_lt_add_left (h n hn) }

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
--  sorry
  use (max N₀ N₁)
  intro n hn
  rw [ge_iff_le, max_le_iff] at hn
  simp ; simp at h₁
  have hsn : |s n| < B := h₀ n hn.left
  have htn : |t n| < ε / B := h₁ n hn.right
  calc |s n * t n| = |s n| * |t n| := by { rw [abs_mul] }
       _ ≤ B * |t n| := by { apply mul_le_mul_of_nonneg_right (le_of_lt hsn) (abs_nonneg (t n)) }
       _ < B * (ε / B) := by { apply mul_lt_mul_of_pos_left htn Bpos }
       _ = ε := by { field_simp }

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
