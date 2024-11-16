
import MIL.Common
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Defs

example (h : Finite Nat) : False := by
  simp [not_finite Nat]

example (h : Fintype Nat) : False := by
  simp [not_finite Nat]
