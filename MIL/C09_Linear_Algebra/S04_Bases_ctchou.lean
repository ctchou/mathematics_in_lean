import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


section matrices

-- Adding vectors
#eval !![1, 2] + !![3, 4]  -- !![4, 6]

-- Adding matrices
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- Multiplying matrices
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

open Matrix

-- matrices acting on vectors on the left
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- matrices acting on vectors on the left, resulting in a size one matrix
#eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

-- matrices acting on vectors on the right
#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]
#eval row (Fin 1) ![1, 2] -- !![1, 2]

#eval col (Fin 1) ![1, 2] -- !![1; 2]

-- vector dot product
#eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

-- matrix transpose
#eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

-- determinant
#eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

-- trace
#eval !![(1 : ℤ), 2; 3, 4].trace -- `5`



#simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`

#norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`

#norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det -- `a * d – b * c`


#norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]
#norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 6]⁻¹ -- 0


example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    norm_num
  simp

example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  norm_num [Matrix.inv_def]
  exact one_fin_two.symm

section

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
  norm_num

example {n : ℕ} (v : Fin n → ℝ) :
    Matrix.vandermonde v = Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ)) :=
  rfl

example {n : ℕ} (v : Fin n → ℝ) :
    Matrix.vandermonde v = Matrix.of (fun i j : Fin n => v i ^ (j : ℕ)) :=
  rfl

variable {n : ℕ} (v : Fin n → ℝ)
#check (fun i j : Fin n ↦ v i ^ (j : ℕ))
#check (fun i j : Fin n => v i ^ (j : ℕ))
#check (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ)
#check (fun _ => 1 : Fin 2 → Fin 2 → ℤ)

end

end matrices

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section

variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- The basis vector with index ``i``
#check (B i : V)

-- the linear isomorphism with the model space given by ``B``
#check (B.repr : V ≃ₗ[K] ι →₀ K)

-- the component function of ``v``
#check (B.repr v : ι →₀ K)

-- the component of ``v`` with index ``i``
#check (B.repr v i : K)

noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)

-- The family of vectors underlying the above basis is indeed ``b``.
example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
    Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
  Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i


variable [DecidableEq ι]

example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl


example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp


example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
  B.sum_repr v




example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
    Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
  Finsupp.linearCombination_apply_of_mem_supported K h

example : Finsupp.linearCombination K B (B.repr v) = v :=
  B.linearCombination_repr v
variable (f : ι → V) in
#check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)
section

variable {W : Type*} [AddCommGroup W] [Module K W]
         (φ : V →ₗ[K] W) (u : ι → W)

#check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

#check (B.constr K u : V →ₗ[K] W)

example (i : ι) : B.constr K u (B i) = u i :=
  B.constr_basis K u i

example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h




variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open LinearMap

#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.

example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v


variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']

example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
  simp

end


open Module LinearMap Matrix

-- Some lemmas coming from the fact that `LinearMap.toMatrix` is an algebra morphism.
/-
LinearMap.toMatrix_comp.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} {R : Type u_1} [CommSemiring R] {l : Type u_2}
  {m : Type u_3} {n : Type u_4} [Fintype n] [Fintype m] [DecidableEq n] {M₁ : Type u_5} {M₂ : Type u_6}
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)
  {M₃ : Type u_7} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃) [Finite l] [DecidableEq m] (f : M₂ →ₗ[R] M₃)
  (g : M₁ →ₗ[R] M₂) : (toMatrix v₁ v₃) (f ∘ₗ g) = (toMatrix v₂ v₃) f * (toMatrix v₁ v₂) g
-/
#check toMatrix_comp
/-
LinearMap.id_comp.{u_3, u_4, u_10, u_11} {R₂ : Type u_3} {R₃ : Type u_4} {M₂ : Type u_10} {M₃ : Type u_11} [Semiring R₂]
  [Semiring R₃] [AddCommMonoid M₂] [AddCommMonoid M₃] {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
  {σ₂₃ : R₂ →+* R₃} (f : M₂ →ₛₗ[σ₂₃] M₃) : LinearMap.id.comp f = f
-/
#check id_comp
/-
LinearMap.comp_id.{u_3, u_4, u_10, u_11} {R₂ : Type u_3} {R₃ : Type u_4} {M₂ : Type u_10} {M₃ : Type u_11} [Semiring R₂]
  [Semiring R₃] [AddCommMonoid M₂] [AddCommMonoid M₃] {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
  {σ₂₃ : R₂ →+* R₃} (f : M₂ →ₛₗ[σ₂₃] M₃) : f.comp LinearMap.id = f
-/
#check comp_id
/-
LinearMap.toMatrix_id.{u_1, u_4, u_5} {R : Type u_1} [CommSemiring R] {n : Type u_4} [Fintype n] [DecidableEq n]
  {M₁ : Type u_5} [AddCommMonoid M₁] [Module R M₁] (v₁ : Basis n R M₁) : (toMatrix v₁ v₁) LinearMap.id = 1
-/
#check toMatrix_id

-- Some lemmas coming from the fact that ``Matrix.det`` is a multiplicative monoid morphism.
/-
Matrix.det_mul.{v, u_2} {n : Type u_2} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R] (M N : Matrix n n R) :
  (M * N).det = M.det * N.det
-/
#check Matrix.det_mul
/-
Matrix.det_one.{v, u_2} {n : Type u_2} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R] : det 1 = 1
-/
#check Matrix.det_one

example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
--  sorry
  have basis_change : M = P' * M' * P := by rw [← toMatrix_comp, ← toMatrix_comp, id_comp, comp_id]
  rw [basis_change, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, ← toMatrix_comp, comp_id, toMatrix_id, det_one, one_mul]

end

section
#check (Module.finrank K V : ℕ)

-- `Fin n → K` is the archetypical space with dimension `n` over `K`.
example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
  Module.finrank_fin_fun K

-- Seen as a vector space over itself, `ℂ` has dimension one.
example : Module.finrank ℂ ℂ = 1 :=
  Module.finrank_self ℂ

-- But as a real vector space it has dimension two.
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex


example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V  :=
  Module.finrank_pos_iff


example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
  apply (Module.finrank_pos_iff (R := K)).1
  exact h

variable {ι : Type*} (B : Basis ι K V)

example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B

example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite
end

section
variable (E F : Submodule K V) [FiniteDimensional K V]

open Module

example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F

example : finrank K E ≤ finrank K V := Submodule.finrank_le E

example (h : finrank K V < finrank K E + finrank K F) :
    Nontrivial (E ⊓ F : Submodule K V) := by
--  sorry
  rw [← Module.finrank_pos_iff (R := K)]
  have h0 := Submodule.finrank_sup_add_finrank_inf_eq E F
  have h1 := Submodule.finrank_le E
  have h2 := Submodule.finrank_le F
  have h3 := Submodule.finrank_le (E ⊔ F)
  linarith

end

#check V -- Type u_2
#check Module.rank K V -- Cardinal.{u_2}


universe u v -- `u` and `v` will denote universe levels

variable {ι : Type u} (B : Basis ι K V)
         {ι' : Type v} (B' : Basis ι' K V)

example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'

example [FiniteDimensional K V] :
    (Module.finrank K V : Cardinal) = Module.rank K V :=
  Module.finrank_eq_rank K V
