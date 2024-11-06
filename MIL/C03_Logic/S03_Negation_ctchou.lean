import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
--  sorry
  intro h'
  rcases h' with ⟨a, fubfa⟩
  rcases h a with ⟨x, hx⟩
  have : a ≤ f x := by exact fubfa x
  linarith

example : ¬FnHasUb fun x ↦ x := by
--  sorry
  intro h
  rcases h with ⟨a, ha⟩
  have : a + 1 ≤ a := by exact h (a + 1)
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
--  sorry
  apply lt_of_not_ge
  intro hab
  have : f a ≥ f b := by { apply h ; exact hab }
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
--  sorry
  intro hmf
  have : f a ≤ f b := by { apply hmf ; exact h }
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
  -- sorry
    intro x y hxy
    linarith
  have h' : f 1 ≤ f 0 := le_refl _
  -- sorry
  have : (1 : ℝ) ≤ 0 := by
    exact h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
--  sorry
  apply le_of_not_gt
  intro hx
  have : x < x/2 := by
    apply h (x/2)
    linarith
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
--  sorry
  intro x hpx
  have : ∃ x, P x := by
    use x
  contradiction

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
--  sorry
  rintro ⟨x, hx⟩
  have : ¬ P x := by exact h x
  contradiction

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
--  sorry
  by_contra h'
  apply h
  intro x
  by_contra h''
  have : ∃ x, ¬ P x := by use x
  contradiction

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
--  sorry
  intro hp
  rcases h with ⟨x, hx⟩
  have : P x := by exact hp x
  contradiction

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
--  sorry
  by_contra h'
  contradiction

example (h : Q) : ¬¬Q := by
--  sorry
  intro h'
  contradiction

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
--  sorry
  intro a
  by_contra h'
  have : FnHasUb f := by
    use a
    intro x
    apply le_of_not_gt
    intro h''
    apply h'
    use x
  contradiction

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
--  sorry
  dsimp [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
