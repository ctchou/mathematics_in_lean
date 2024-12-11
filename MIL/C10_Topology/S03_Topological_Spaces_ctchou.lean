import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.DenseEmbedding
import Batteries.Tactic.Instances

open Set Filter Topology

section
variable {X : Type*} [TopologicalSpace X]

example : IsOpen (univ : Set X) :=
  isOpen_univ

example : IsOpen (∅ : Set X) :=
  isOpen_empty

example {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) :=
  isOpen_iUnion hs

example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  isOpen_iInter_of_finite hs

variable {Y : Type*} [TopologicalSpace Y]

example {f : X → Y} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

example {f : X → Y} {x : X} : ContinuousAt f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
  Iff.rfl

example {f : X → Y} {x : X} : ContinuousAt f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
  Iff.rfl

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff

example (x : X) : pure x = 𝓟 {x} := by simp only [principal_singleton]

example (x : X) : pure x ≤ 𝓝 x :=
  pure_le_nhds x

example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x :=
  h.self_of_nhds

example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
  eventually_eventually_nhds.mpr h

/-
TopologicalSpace.mkOfNhds.{u} {α : Type u} (n : α → Filter α) : TopologicalSpace α
-/
#check TopologicalSpace.mkOfNhds

/-
TopologicalSpace.nhds_mkOfNhds.{u} {α : Type u} (n : α → Filter α) (a : α) (h₀ : pure ≤ n)
  (h₁ : ∀ (a : α), ∀ s ∈ n a, ∀ᶠ (y : α) in n a, s ∈ n y) : 𝓝 a = n a
-/
#check TopologicalSpace.nhds_mkOfNhds

/-
mem_nhds_iff.{u} {X : Type u} {x : X} {s : Set X} [TopologicalSpace X] : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t
-/
#check mem_nhds_iff

example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
    (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
    ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' := by
--  sorry
  intro a s s_in
  let t := { y | s ∈ n y }
  use t
  constructor
  . refine H a (fun x ↦ x ∈ s) s_in
  constructor
  . intro x ; simp [t]
    intro s_nx
    exact H₀ x s_nx
  . simp [t]

end

-- BOTH.
variable {X Y : Type*}

example (f : X → Y) : TopologicalSpace X → TopologicalSpace Y :=
  TopologicalSpace.coinduced f

example (f : X → Y) : TopologicalSpace Y → TopologicalSpace X :=
  TopologicalSpace.induced f

example (f : X → Y) (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) :
    TopologicalSpace.coinduced f T_X ≤ T_Y ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
  coinduced_le_iff_le_induced

#check coinduced_compose

#check induced_compose

example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ s, T'.IsOpen s → T.IsOpen s :=
  Iff.rfl

example (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) (f : X → Y) :
    Continuous f ↔ TopologicalSpace.coinduced f T_X ≤ T_Y :=
  continuous_iff_coinduced_le

example {Z : Type*} (f : X → Y) (T_X : TopologicalSpace X) (T_Z : TopologicalSpace Z)
      (g : Y → Z) :
    @Continuous Y Z (TopologicalSpace.coinduced f T_X) T_Z g ↔
      @Continuous X Z T_X T_Z (g ∘ f) := by
  rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]

example (ι : Type*) (X : ι → Type*) (T_X : ∀ i, TopologicalSpace (X i)) :
    (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
      ⨅ i, TopologicalSpace.induced (fun x ↦ x i) (T_X i) :=
  rfl

example [TopologicalSpace X] [T2Space X] {u : ℕ → X} {a b : X} (ha : Tendsto u atTop (𝓝 a))
    (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

example [TopologicalSpace X] [RegularSpace X] (a : X) :
    (𝓝 a).HasBasis (fun s : Set X ↦ s ∈ 𝓝 a ∧ IsClosed s) id :=
  closed_nhds_basis a

example [TopologicalSpace X] {x : X} :
    (𝓝 x).HasBasis (fun t : Set X ↦ t ∈ 𝓝 x ∧ IsOpen t) id :=
  nhds_basis_opens' x

/-
IsDenseInducing.continuousAt_extend.{u_1, u_2, u_3} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [TopologicalSpace α]
  [TopologicalSpace β] {i : α → β} [TopologicalSpace γ] [T3Space γ] {b : β} {f : α → γ} (di : IsDenseInducing i)
  (hf : ∀ᶠ (x : β) in 𝓝 b, ∃ c, Tendsto f (comap i (𝓝 x)) (𝓝 c)) : ContinuousAt (di.extend f) b
-/
#check IsDenseInducing.continuousAt_extend

theorem aux {X Y A : Type*} [TopologicalSpace X] {c : A → X}
      {f : A → Y} {x : X} {F : Filter Y}
      (h : Tendsto f (comap c (𝓝 x)) F) {V' : Set Y} (V'_in : V' ∈ F) :
    ∃ V ∈ 𝓝 x, IsOpen V ∧ c ⁻¹' V ⊆ f ⁻¹' V' := by
--  sorry
  have h1 : f ⁻¹' V' ∈ comap c (𝓝 x) := h V'_in
  have ⟨U, U_in, U_V'⟩ := mem_comap.mp h1
  have ⟨V, V_U, V_open, x_V⟩ := mem_nhds_iff.mp U_in
  use V
  repeat' constructor
  . apply mem_nhds_iff.mpr
    refine ⟨V, subset_refl V, V_open, x_V⟩
  . assumption
  . exact subset_trans (Set.preimage_mono V_U) U_V'

example [TopologicalSpace X] [TopologicalSpace Y] [T3Space Y] {A : Set X}
    (hA : ∀ x, x ∈ closure A) {f : A → Y} (f_cont : Continuous f)
    (hf : ∀ x : X, ∃ c : Y, Tendsto f (comap (↑) (𝓝 x)) (𝓝 c)) :
    ∃ φ : X → Y, Continuous φ ∧ ∀ a : A, φ a = f a := by
--  sorry
  choose φ hφ using hf
  use φ
  constructor
  . rw [continuous_iff_continuousAt]
    intro x
    suffices ∀ V' ∈ 𝓝 (φ x), IsClosed V' → φ ⁻¹' V' ∈ 𝓝 x by
      simpa [ContinuousAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
    intro V' V'_in V'_closed
    obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, IsOpen V ∧ (↑) ⁻¹' V ⊆ f ⁻¹' V' := aux (hφ x) V'_in
    suffices : ∀ y ∈ V, φ y ∈ V'
    exact mem_of_superset V_in this
    intro y y_in
    have hVx : V ∈ 𝓝 y := V_op.mem_nhds y_in
    haveI : (comap ((↑) : A → X) (𝓝 y)).NeBot := by simpa [mem_closure_iff_comap_neBot] using hA y
    apply V'_closed.mem_of_tendsto (hφ y)
    exact mem_of_superset (preimage_mem_comap hVx) hV
  . intro a
    have lim : Tendsto f (𝓝 a) (𝓝 (φ a)) := by
      simp [nhds_induced]
      exact hφ a
    exact tendsto_nhds_unique lim f_cont.continuousAt

/-
Filter.HasBasis.tendsto_right_iff.{u_1, u_2, u_5} {α : Type u_1} {β : Type u_2} {ι' : Sort u_5} {la : Filter α}
  {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β} {f : α → β} (hlb : lb.HasBasis pb sb) :
  Tendsto f la lb ↔ ∀ (i : ι'), pb i → ∀ᶠ (x : α) in la, f x ∈ sb i
-/
#check HasBasis.tendsto_right_iff

example [TopologicalSpace X] [FirstCountableTopology X]
      {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 a) :=
  mem_closure_iff_seq_limit

variable [TopologicalSpace X]

example {F : Filter X} {x : X} : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) :=
  Iff.rfl

example {s : Set X} :
    IsCompact s ↔ ∀ (F : Filter X) [NeBot F], F ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a F :=
  Iff.rfl

example [FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
    (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

variable [TopologicalSpace Y]

example {x : X} {F : Filter X} {G : Filter Y} (H : ClusterPt x F) {f : X → Y}
    (hfx : ContinuousAt f x) (hf : Tendsto f F G) : ClusterPt (f x) G :=
  ClusterPt.map H hfx hf

example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
--  sorry
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by
    rw [Filter.push_pull, map_principal]
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by
    apply (NeBot.of_map (m := f))
    rw [map_eq, inf_of_le_right F_le]
    assumption
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  have ⟨x, x_s, h_cl⟩ := @hs (𝓟 s ⊓ comap f F) Hne Hle
  use (f x)
  constructor
  . exact Set.mem_image_of_mem f x_s
  . apply h_cl.map hf.continuousAt
    rw [Tendsto, map_eq]
    exact inf_le_right

example {ι : Type*} {s : Set X} (hs : IsCompact s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
    (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_finite_subcover U hUo hsU

section
variable (X : Type*) [TopologicalSpace X]
#instances (T2Space X)
#instances (T25Space X)
end

section
variable (X : Type*) [TopologicalSpace X] [T3Space X]
#synth (T2Space X)
#synth (T25Space X)
end
