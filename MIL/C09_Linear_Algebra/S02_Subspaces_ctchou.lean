import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx


noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp


def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
--    dsimp
--    sorry
    simp
  add_mem' := by
    simp
    intro a b aH bH
    apply H.add_mem aH bH
  smul_mem' := by
    -- dsimp
    -- sorry
    simp
    intro k v vH
    apply H.smul_mem k vH

example (U : Submodule K V) : Module K U := inferInstance

example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance

example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]

example (x : V) : x ∈ (⊤ : Submodule K V) := trivial

example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K


-- If two subspaces are in direct sum then they span the whole space.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- If two subspaces are in direct sum then they intersect only at zero.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- If subspaces are in direct sum then they span the whole space.
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- If subspaces are in direct sum then they pairwise intersect only at zero.
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_independent.pairwiseDisjoint hij).eq_bot

-- Those conditions characterize direct sums.
/-
DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top.{u, v, u_1} {R : Type u} [Ring R] {ι : Type v}
  [dec_ι : DecidableEq ι] {M : Type u_1} [AddCommGroup M] [Module R M] (A : ι → Submodule R M) :
  IsInternal A ↔ CompleteLattice.Independent A ∧ iSup A = ⊤
-/
#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

-- The relation with external direct sums: if a family of subspaces is
-- in internal direct sum then the map from their external direct sum into `V`
-- is a linear isomorphism.
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end

example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  induction h using Submodule.span_induction with
  | mem y h =>
--      sorry
      rcases h with y_S | y_T
      . use y ; simp ; apply y_S
      . use 0 ; simp ; apply y_T
  | zero =>
--      sorry
      use 0 ; simp
  | add x y hx hy hx' hy' =>
--      sorry
      rcases hx' with ⟨xs, xs_S, xt, xt_T, x_eq⟩
      rcases hy' with ⟨ys, ys_S, yt, yt_T, y_eq⟩
      have xy_S := S.add_mem xs_S ys_S
      have xy_T := T.add_mem xt_T yt_T
      use (xs + ys), xy_S, (xt + yt), xy_T
      rw [x_eq, y_eq] ; module
  | smul a x hx hx' =>
--      sorry
      rcases hx' with ⟨xs, xs_S, xt, xt_T, x_eq⟩
      have a_xs_S := S.smul_mem a xs_S
      have a_xt_T := T.smul_mem a xt_T
      use (a • xs), a_xs_S, (a • xt), a_xt_T
      rw [x_eq] ; module

section

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)

example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`



open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm

/-
Submodule.mem_map_of_mem.{u_1, u_3, u_5, u_7, u_9} {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7}
  [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
  [RingHomSurjective σ₁₂] {F : Type u_9} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂] {f : F} {p : Submodule R M}
  {r : M} (h : r ∈ p) : f r ∈ Submodule.map f p
-/
#check Submodule.mem_map_of_mem
/-
Submodule.mem_map.{u_1, u_3, u_5, u_7, u_9} {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [Semiring R]
  [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
  [RingHomSurjective σ₁₂] {F : Type u_9} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂] {f : F} {p : Submodule R M}
  {x : M₂} : x ∈ Submodule.map f p ↔ ∃ y ∈ p, f y = x
-/
#check Submodule.mem_map
/-
Submodule.mem_comap.{u_1, u_3, u_5, u_7, u_9} {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [Semiring R]
  [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂} {x : M} {F : Type u_9}
  [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂] {f : F} {p : Submodule R₂ M₂} : x ∈ Submodule.comap f p ↔ f x ∈ p
-/
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
--  sorry
  constructor
  . intro h v v_E
    simp
    apply h ⟨v, v_E, rfl⟩
  . intro h w ⟨v, v_E, eq_w⟩
    rw [← eq_w]
    apply h v_E

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange


open Submodule

/-
Submodule.map_comap_eq.{u_1, u_2, u_5, u_6, u_10} {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : Type u_6}
  [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
  {F : Type u_10} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂] [RingHomSurjective τ₁₂] (f : F)
  (q : Submodule R₂ M₂) : map f (comap f q) = range f ⊓ q
-/
#check Submodule.map_comap_eq
/-
Submodule.comap_map_eq.{u_1, u_2, u_4, u_5, u_8} {R : Type u_1} {R₂ : Type u_2} {M : Type u_4} {M₂ : Type u_5}
  [Semiring R] [Semiring R₂] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
  [RingHomSurjective τ₁₂] {F : Type u_8} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂] (f : F) (p : Submodule R M) :
  comap f (map f p) = p ⊔ ker f
-/
#check Submodule.comap_map_eq

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
--  sorry
  toFun := (fun F => ⟨comap E.mkQ F, by
    conv_lhs => rw [← E.ker_mkQ, ← comap_bot]
    gcongr
    apply bot_le⟩
  )
  invFun := (fun P => map E.mkQ P)
  left_inv := (fun P => by
    dsimp
    rw [Submodule.map_comap_eq, E.range_mkQ]
    exact top_inf_eq P
  )
  right_inv := by
    intro P
    ext x
    dsimp only
    rw [Submodule.comap_map_eq, E.ker_mkQ, sup_of_le_left]
    exact P.2
