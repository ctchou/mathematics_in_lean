import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Topology.MetricSpace.Basic

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

example (h : a ≤ b) : 0 ≤ b - a := by
--  sorry
 calc 0 = -a + a := by simp
      _ ≤ -a + b := by apply add_le_add_left h
      _ = b + -a := by rw [add_comm]
      _ = b - a := by { rw [← sub_eq_add_neg] }

end
