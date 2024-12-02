
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
  fun ε ε_pos ↦ (hf ε ε_pos).elim
   fun δ ⟨δ_pos, hδ⟩ ↦ (hu δ δ_pos).elim
     fun N hN ↦ ⟨N, fun n n_ge ↦ hδ (u n) <| hN n n_ge⟩
