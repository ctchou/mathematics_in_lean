import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
--  sorry
  simp

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
--  sorry
  rw [subset_def]
  simp
  intro y x xs fxy
  have xy : x = y := h fxy
  rw [← xy]
  exact xs

example : f '' (f ⁻¹' u) ⊆ u := by
--  sorry
  rw [subset_def]
  simp

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
--  sorry
  rw [subset_def]
  simp
  intro y yu
  have h' := h y
  rcases h' with ⟨x, fxy⟩
  use x
  constructor
  . rw [fxy] ; exact yu
  . exact fxy

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
--  sorry
  rw [subset_def]
  simp
  intro x xs
  use x
  have xt := h xs
  use xt

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
--  sorry
  rw [subset_def]
  simp
  intro x xu
  apply h xu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
--  sorry
  ext
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
--  sorry
  rw [subset_def]
  simp
  intro y x xs xt fxy
  constructor <;> use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
--  sorry
  rw [subset_def]
  simp
  intro x xs y yt fyx
  use y
  simp [yt, fyx]
  have yx : y = x := h fyx
  simp [yx, xs]

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
--  sorry
  simp [subset_def]
  intro x xs ht
  use x
  simp [xs]
  intro xt
  apply ht x xt
  rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
--  sorry
  simp [subset_def]

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
--  sorry
  ext y
  simp
  constructor
  . rintro ⟨⟨x, xs, fxy⟩, yv⟩
    use x
    simp [xs, fxy, yv]
  . rintro ⟨x, ⟨xs, fxv⟩, fxy⟩
    simp [← fxy, fxv]
    use x

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
--  sorry
  simp [subset_def]
  intro y x xs fxu fxy
  simp [← fxy, fxu]
  use x

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
--  sorry
  simp [subset_def]
  intro x xs fxu
  simp [fxu]
  use x

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
--  sorry
  simp [subset_def]
  rintro x (xs | fxu)
  . left ; use x
  . right ; exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
--  sorry
  ext y
  simp
  constructor
  . rintro ⟨x, ⟨i, xai⟩, fxy⟩
    use i
    use x
  . rintro ⟨i, ⟨x, xai, fxy⟩⟩
    use x
    simp [fxy]
    use i

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
--  sorry
  simp [subset_def]
  intro x xai i
  use x
  simp [xai i]

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
--  sorry
  simp [subset_def]
  intro y aefxy
  have efxy := aefxy i
  rcases efxy with ⟨x, xai, fxy⟩
  use x
  simp [fxy]
  intro i'
  have efxy' := aefxy i'
  rcases efxy' with ⟨x', xai', fxy'⟩
  have fxx' : f x = f x' := by simp [fxy, fxy']
  have xx' : x = x' := by apply injf fxx'
  simp [xx', xai']

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
--  sorry
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
--  sorry
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
--  sorry
  intro x
  simp
  intro xnneg y ynneg sqrt_eq
  calc x = (sqrt x)^2 := by { rw [sq_sqrt xnneg] }
       _ = (sqrt y)^2 := by { rw [sqrt_eq] }
       _ = y := by { rw [sq_sqrt ynneg] }

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
--  sorry
  intro x
  simp
  intro xnneg y ynneg sq_eq
  calc x = √(x^2) := by { rw [sqrt_sq xnneg] }
       _ = √(y^2) := by { rw [sq_eq] }
       _ = y := by { rw [sqrt_sq ynneg] }

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
--  sorry
  ext y
  simp
  constructor
  . rintro ⟨x, xnneg, sqrtx_y⟩
    rw [← sqrtx_y]
    apply sqrt_nonneg
  . intro ynneg
    use (y^2)
    simp [pow_two_nonneg y, sqrt_sq ynneg]

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
--  sorry
  ext y
  simp
  constructor
  . rintro ⟨x, x2_y⟩
    simp [← x2_y, pow_two_nonneg x]
  . intro y_nneg
    use (√ y)
    apply sq_sqrt y_nneg

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

#print LeftInverse
#print RightInverse

example : Injective f ↔ LeftInverse (inverse f) f := by
--  sorry
  constructor
  . intro inj_f x
    have f_inv : f (inverse f (f x)) = f x := by
      apply inverse_spec
      use x
    apply inj_f f_inv
  . intro l_inv x y fxy
    calc x = inverse f (f x) := by rw [l_inv x]
         _ = inverse f (f y) := by rw [fxy]
         _ = y := by rw [l_inv y]

example : Surjective f ↔ RightInverse (inverse f) f := by
--  sorry
  constructor
  . intro surj_f y
    rcases surj_f y with ⟨x, fxy⟩
    apply inverse_spec
    use x
  . intro r_inv y
    use (inverse f y)
    exact r_inv y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
--  sorry
    unfold S
    simp [h₁]
  have h₃ : j ∉ S := by
--  sorry
    simp [← h, h₁]
  contradiction

-- COMMENTS: TODO: improve this
end
