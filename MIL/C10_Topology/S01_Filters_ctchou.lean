import MIL.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

def principal {α : Type*} (s : Set α) : Filter α
    where
-- sorry
  sets := { t | s ⊆ t }
  univ_sets := by { simp }
  sets_of_superset := by { simp ; apply subset_trans }
  inter_sets := by { simp ; intros ; constructor <;> assumption }

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
-- sorry
    univ_sets := by simp
    sets_of_superset := by
      simp
      intros s t a hs hst
      use a
      intro b hab
      exact hst (hs b hab)
    inter_sets := by
      simp
      intro s1 s2 a1 hs1 a2 hs2
      use (max a1 a2)
      intro b hb
      rw [max_le_iff] at hb
      rcases hb with ⟨hb1, hb2⟩
      have := hs1 b hb1
      have := hs2 b hb2
      tauto
  }

/-
Filter.Tendsto.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Prop
-/
#check Tendsto

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
--  sorry
  intro z zH
  rw [preimage_comp]
  apply hf
  apply hg
  assumption

variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

/-
le_inf_iff.{u} {α : Type u} [SemilatticeInf α] {a b c : α} : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c
-/
#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
--  sorry
  simp [Tendsto, nhds_prod_eq, Filter.le_prod]

example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀

/-
Filter.HasBasis.tendsto_iff.{u_1, u_2, u_4, u_5} {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {ι' : Sort u_5}
  {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β} {f : α → β}
  (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
  Tendsto f la lb ↔ ∀ (ib : ι'), pb ib → ∃ ia, pa ia ∧ ∀ x ∈ sa ia, f x ∈ sb ib
-/
#check Filter.HasBasis.tendsto_iff

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp

example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have h1 : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  have h2 := h1.tendsto_iff (nhds_basis_Ioo_pos x₀) (f := u)
  rw [h2]
  simp

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

/-
Filter.Eventually.of_forall.{u} {α : Type u} {p : α → Prop} {f : Filter α} (hp : ∀ (x : α), p x) : ∀ᶠ (x : α) in f, p x
-/
#check Eventually.of_forall
/-
Filter.Eventually.mono.{u} {α : Type u} {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ (x : α) in f, p x)
  (hq : ∀ (x : α), p x → q x) : ∀ᶠ (x : α) in f, q x
-/
#check Eventually.mono
/-
Filter.Eventually.and.{u} {α : Type u} {p q : α → Prop} {f : Filter α} :
  Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
-/
#check Eventually.and

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩

/-
mem_closure_iff_clusterPt.{u} {X : Type u} {x : X} {s : Set X} [TopologicalSpace X] : x ∈ closure s ↔ ClusterPt x (𝓟 s)
-/
#check mem_closure_iff_clusterPt
/-
Filter.le_principal_iff.{u} {α : Type u} {s : Set α} {f : Filter α} : f ≤ 𝓟 s ↔ s ∈ f
-/
#check le_principal_iff
/-
Filter.neBot_of_le.{u} {α : Type u} {f g : Filter α} [hf : f.NeBot] (hg : f ≤ g) : g.NeBot
-/
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M := by
--  sorry
  rw [mem_closure_iff_clusterPt, ClusterPt]
  rw [Tendsto] at hux
  have huM : map u atTop ≤ 𝓟 M := by
    rw [le_principal_iff]
    apply huM
  have huxM : map u atTop ≤ 𝓝 x ⊓ 𝓟 M := by
    rw [le_inf_iff]
    tauto
  apply neBot_of_le huxM
