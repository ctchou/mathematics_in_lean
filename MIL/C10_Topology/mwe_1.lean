
import Mathlib.Topology.MetricSpace.Basic

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  intro ε ε_pos
  have ⟨δ, δ_pos, hf'⟩ := hf ε ε_pos
  have ⟨N, hu'⟩ := hu δ δ_pos
  use N
  intro n n_N
  have h1 := hu' n n_N
  exact hf' (u n) h1

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦ (
    have ⟨δ, δ_pos, hf'⟩ := hf ε ε_pos
    have ⟨N, hu'⟩ := hu δ δ_pos
    ⟨N, fun n n_N ↦ (
      have h1 := hu' n n_N
      have h2 := hf' (u n) h1
      show |(f ∘ u) n - f x₀| ≤ ε from h2
      )
    ⟩
  )

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦ (
    have ⟨δ, δ_pos, hf'⟩ := hf ε ε_pos
    have ⟨N, hu'⟩ := hu δ δ_pos
    ⟨N, fun n n_N ↦ (
      have h1 := hu' n n_N
      have h2 := hf' (u n) h1
      h2
      )
    ⟩
  )

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦ (hf ε ε_pos).elim
   fun δ ⟨δ_pos, hf'⟩ ↦ (hu δ δ_pos).elim
     fun N hu' ↦ ⟨N, fun n n_N ↦ hf' (u n) <| hu' n n_N⟩

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦ (hf ε ε_pos).elim
   fun δ ⟨δ_pos, hδ⟩ ↦ (hu δ δ_pos).elim
     fun N hN ↦ ⟨N, fun n n_ge ↦ hδ (u n) <| hN n n_ge⟩

variable (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀)
include hf hu

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have := hf _ _
    sorry

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have := hf _ ε_pos
    _

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    _

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have := hδ _ _
    _

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have : |f (u x) - _| ≤ _ := hδ _ _
    _

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have (x) : |f (u x) - _| ≤ _ := hδ _ _
    _

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have := hu _ _
    have (n) : |f (u n) - _| ≤ _ := hδ _ _
    _

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have ⟨N, hN⟩ := hu _ δ_pos
    have (n) : |f (u n) - _| ≤ _ := hδ _ _
    _

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have ⟨N, hN⟩ := hu _ δ_pos
    have (n) : |f (u n) - _| ≤ _ := hδ _ _
    ⟨N, fun n hn => _⟩

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have ⟨N, hN⟩ := hu _ δ_pos
    ⟨N, fun n hn =>
      hδ _ _⟩

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have ⟨N, hN⟩ := hu _ δ_pos
    ⟨N, fun n hn =>
      hδ _ (hN _ _)⟩

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos ↦
    have ⟨δ, δ_pos, hδ⟩ := hf _ ε_pos
    have ⟨N, hN⟩ := hu _ δ_pos
    ⟨N, fun n hn =>
      hδ _ (hN _ hn)⟩

example : sequence_tendsto (f ∘ u) (f x₀) :=
  fun _ ε_pos ↦
    have ⟨_, δ_pos, hδ⟩ := hf _ ε_pos
    have ⟨N, hN⟩ := hu _ δ_pos
    ⟨N, fun _ hn => hδ _ (hN _ hn)⟩
