import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set
open Filter
open Topology

variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

-- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  Continuous.comp continuous_dist ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
--  sorry
  continuity

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
--  sorry
  apply Continuous.comp hf
  apply Continuous.add
  . apply Continuous.pow
    apply continuous_id
  . apply continuous_id

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ x, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl

example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (Eventually.of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s := by
--  sorry
  have hc : IsClosed (closure s) := by exact isClosed_closure
  have hsc : ∀ n, u n ∈ closure s := by
    intro n
    apply subset_closure (hs n)
  apply hc.mem_of_tendsto hu
  exact Eventually.of_forall hsc (f := atTop)

/-
Metric.nhds_basis_ball.{u} {α : Type u} [PseudoMetricSpace α] {x : α} : (𝓝 x).HasBasis (fun x ↦ 0 < x) (Metric.ball x)
-/
#check Metric.nhds_basis_ball
/-
Filter.HasBasis.mem_iff.{u_1, u_4} {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p : ι → Prop} {s : ι → Set α}
  {t : Set α} (hl : l.HasBasis p s) : t ∈ l ↔ ∃ i, p i ∧ s i ⊆ t
-/
#check HasBasis.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

/-
IsCompact.{u_1} {X : Type u_1} [TopologicalSpace X] (s : Set X) : Prop
-/
#check IsCompact
/-
CompactIccSpace.isCompact_Icc.{u_1} {α : Type u_1} :
  ∀ {inst : TopologicalSpace α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α}, IsCompact (Icc a b)
-/
#check isCompact_Icc

example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ

/-
IsCompact.isClosed.{u_1} {X : Type u_1} [TopologicalSpace X] [T2Space X] {s : Set X} (hs : IsCompact s) : IsClosed s
-/
#check IsCompact.isClosed

example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff

/-
isClosed_le.{u, v} {α : Type u} {β : Type v} [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]
  [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) : IsClosed {b | f b ≤ g b}
-/
#check isClosed_le

/-
IsClosed.isCompact.{u} {X : Type u} [TopologicalSpace X] {s : Set X} [CompactSpace X] (h : IsClosed s) : IsCompact s
-/
#check IsClosed.isCompact

/-
Set.eq_empty_or_nonempty.{u} {α : Type u} (s : Set α) : s = ∅ ∨ s.Nonempty
-/
#check eq_empty_or_nonempty

#check mem_empty_iff_false
#check not_mem_empty


example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
--  sorry
  rw [Metric.uniformContinuous_iff]
  intro ε ε_pos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  have φ_cont : Continuous φ := by continuity
  let K := { p : X × X | ε ≤ φ p }
  rcases Set.eq_empty_or_nonempty K with K_empty | K_nonempty
  . use 1
    constructor
    . norm_num
    . intro a b _
      by_contra! dist_f_ab
      have : K.Nonempty := by
        rw [nonempty_def]
        use (a,b)
        simp [K, φ, dist_f_ab]
      simp [K_empty] at this
  . let ψ : X × X → ℝ := fun p ↦ ε
    have ψ_cont : Continuous ψ := by continuity
    have K_closed : IsClosed K := isClosed_le ψ_cont φ_cont
    have K_compact : IsCompact K := IsClosed.isCompact K_closed
    let d : X × X → ℝ := fun p ↦ dist p.1 p.2
    have d_cont : Continuous d := by continuity
    have K_d_min : ∃ p ∈ K, ∀ q ∈ K, d p ≤ d q := K_compact.exists_isMinOn K_nonempty (d_cont.continuousOn)
    rcases K_d_min with ⟨p, p_K, p_d_min⟩
    let δ := dist p.1 p.2
    use δ
    constructor
    . by_contra! δ_nonpos
      have δ_nonneg : 0 ≤ δ := dist_nonneg
      have δ_zero : δ = 0 := le_antisymm δ_nonpos δ_nonneg
      rw [dist_eq_zero] at δ_zero
      have φ_p_zero : φ p = 0 := by simp [φ, δ_zero]
      simp [K] at p_K
      linarith
    . intro a b dist_ab
      by_contra! dist_f_ab
      let q := (a,b)
      have q_K : q ∈ K := by simp [K, φ, dist_f_ab]
      have := p_d_min q q_K
      linarith

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

open BigOperators

open Finset

/-
tendsto_pow_atTop_nhds_zero_of_lt_one.{u_4} {𝕜 : Type u_4} [LinearOrderedField 𝕜] [Archimedean 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) : Tendsto (fun n ↦ r ^ n) atTop (𝓝 0)
-/
#check tendsto_pow_atTop_nhds_zero_of_lt_one
/-
Filter.Tendsto.mul.{u_2, u_3} {α : Type u_2} {M : Type u_3} [TopologicalSpace M] [Mul M] [ContinuousMul M] {f g : α → M}
  {x : Filter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x ↦ f x * g x) x (𝓝 (a * b))
-/
#check Tendsto.mul
/-
dist_le_range_sum_dist.{u} {α : Type u} [PseudoMetricSpace α] (f : ℕ → α) (n : ℕ) :
  dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, dist (f i) (f (i + 1))
-/
#check dist_le_range_sum_dist
/-
Finset.sum_le_sum.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [OrderedAddCommMonoid N] {f g : ι → N} {s : Finset ι}
  (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
-/
#check sum_le_sum
/-
Finset.mul_sum.{u_1, u_3} {ι : Type u_1} {α : Type u_3} [NonUnitalNonAssocSemiring α] (s : Finset ι) (f : ι → α)
  (a : α) : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
-/
#check mul_sum

lemma aux (k : ℕ) : ∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ i = 2 - 2 * (1 / 2) ^ k := by
  induction' k with k ih
  . simp
  rw [sum_range_succ, ih]
  ring

theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / (2 ^ N)) * 2 < ε := by
--    sorry
    have half_to_zero := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : 1/2 < (1 : ℝ))
    rw [Metric.tendsto_atTop] at half_to_zero
    have ⟨N, hN1⟩ := half_to_zero (ε/2) (by linarith : ε/2 > (0 : ℝ))
    use N
    have hN2 := hN1 N (by linarith : N ≥ N)
    simp [← one_div, div_pow] at hN2
    linarith
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by { rw [dist_comm] ; simp }
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := by { exact dist_le_range_sum_dist (fun i ↦ u (N + i)) k }
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := by { apply sum_le_sum ; intro i _ ; exact hu (N + i) }
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by { rw [mul_sum] ; congr ; ext i ; ring_nf }
    _ ≤ 1 / 2 ^ N * 2 := by {
      have : (0 : ℝ) < 1 / 2 ^ N := by simp
      apply (mul_le_mul_left this).mpr
      rw [aux]
      have : (0 : ℝ) < 2 * (1 / 2) ^ k := by simp
      linarith
    }
    _ < ε := by { linarith }


open Metric

/-
Dense.exists_mem_open.{u} {X : Type u} {s : Set X} [TopologicalSpace X] (hs : Dense s) {U : Set X} (ho : IsOpen U)
  (hne : U.Nonempty) : ∃ x ∈ s, x ∈ U
-/
#check Dense.exists_mem_open

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n := by
--    sorry
    intro n
    simp [B]
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n := by
--    sorry
    intro n x δ δ_pos
    have xδ_open : IsOpen (ball x δ) := isOpen_ball
    obtain ⟨y, y_fn, y_xδ⟩ : ∃ y ∈ f n, y ∈ ball x δ := by
      have : (ball x δ).Nonempty := by simp [nonempty_ball, δ_pos]
      apply Dense.exists_mem_open (hd n) xδ_open this
    have y_inter : y ∈ f n ∩ ball x δ := mem_inter y_fn y_xδ
    have inter_open : IsOpen (f n ∩ ball x δ) := IsOpen.inter (ho n) xδ_open
    rw [Metric.isOpen_iff] at inter_open
    have ⟨ε, ε_pos, yε_inter⟩ := inter_open y y_inter
    use y, min (ε / 2) (B (n+1))
    constructor
    . have h1 : 0 < ε / 2 := by linarith
      have h2 : 0 < B (n + 1) := by simp [B]
      exact lt_min h1 h2
    constructor
    . apply min_le_right
    . have h1 : closedBall y (min (ε / 2) (B (n + 1))) ⊆ ball y ε := by
        intro ; simp ; intros ; linarith
      apply subset_trans h1
      apply subset_trans yε_inter
      intro ; simp;  intros
      constructor
      . linarith
      . assumption
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
    belonging to all `f n`. For this, we construct inductively a sequence
    `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
    in the previous ball and in `f n`, and such that `r n` is small enough to ensure
    that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
    to all the `f n`. -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry
