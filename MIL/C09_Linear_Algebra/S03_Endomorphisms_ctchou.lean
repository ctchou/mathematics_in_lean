import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common




variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  LinearMap.mul_eq_comp φ ψ -- `rfl` would also work

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ



/-
Submodule.eq_bot_iff.{u_1, u_3} {R : Type u_1} {M : Type u_3} [Semiring R] [AddCommMonoid M] [Module R M]
  (p : Submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = 0
-/
#check Submodule.eq_bot_iff
/-
Submodule.mem_inf.{u_1, u_3} {R : Type u_1} {M : Type u_3} [Semiring R] [AddCommMonoid M] [Module R M]
  {p q : Submodule R M} {x : M} : x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q
-/
#check Submodule.mem_inf
/-
LinearMap.mem_ker.{u_1, u_2, u_5, u_7, u_11} {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : Type u_7} [Semiring R]
  [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂} {F : Type u_11}
  [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂] {f : F} {y : M} : y ∈ ker f ↔ f y = 0
-/
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
--  sorry
  ext v ; simp
  constructor
  . rintro ⟨h_P, h_Q⟩
    rcases h with ⟨a, b, cop⟩
    have cop_v : aeval φ (a * P + b * Q) v = v := by simp [cop]
    simp [h_P, h_Q] at cop_v
    exact cop_v.symm
  . intro h ; simp [h]

/-
Submodule.add_mem_sup.{u_1, u_3} {R : Type u_1} {M : Type u_3} [Semiring R] [AddCommMonoid M] [Module R M]
  {S T : Submodule R M} {s t : M} (hs : s ∈ S) (ht : t ∈ T) : s + t ∈ S ⊔ T
-/
#check Submodule.add_mem_sup
/-
map_mul.{u_4, u_5, u_9} {M : Type u_4} {N : Type u_5} {F : Type u_9} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
  (f : F) (x y : M) : f (x * y) = f x * f y
-/
#check map_mul
/-
LinearMap.mul_apply.{u_1, u_5} {R : Type u_1} {M : Type u_5} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)
  (x : M) : (f * g) x = f (g x)
-/
#check LinearMap.mul_apply
/-
LinearMap.ker_le_ker_comp.{u_1, u_2, u_3, u_5, u_7, u_8} {R : Type u_1} {R₂ : Type u_2} {R₃ : Type u_3} {M : Type u_5}
  {M₂ : Type u_7} {M₃ : Type u_8} [Semiring R] [Semiring R₂] [Semiring R₃] [AddCommMonoid M] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [Module R M] [Module R₂ M₂] [Module R₃ M₃] {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
  [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) : ker f ≤ ker (g.comp f)
-/
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
--  sorry
  apply le_antisymm
  . apply sup_le
    . rw [mul_comm, map_mul]
      apply LinearMap.ker_le_ker_comp
    . rw [map_mul]
      apply LinearMap.ker_le_ker_comp
  . intro x hx
    rcases h with ⟨U, V, hUV⟩
    have key : x = aeval φ (U*P) x + aeval φ (V*Q) x := by simpa using congr((aeval φ) $hUV.symm x)
    rw [key, add_comm]
    apply Submodule.add_mem_sup
    . rw [mem_ker] at *
      have eq1 : P * (V * Q) = V * (P * Q) := by ring
      rw [← mul_apply, ← map_mul, eq1, map_mul, mul_apply, hx, map_zero]
    . rw [mem_ker] at *
      have eq2:  Q * (U * P) = U * (P * Q) := by ring
      rw [← mul_apply, ← map_mul, eq2, map_mul, mul_apply, hx, map_zero]


example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true (we will discuss dimension below)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
