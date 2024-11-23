
import Mathlib.GroupTheory.QuotientGroup.Basic
--set_option diagnostics true
--set_option diagnostics.threshold 0
variable {G : Type*} [Group G] {M : Subgroup G} [M.Normal]

#check G ⧸ M
#check G = G
#check M = M
#check (G ⧸ M) = (G ⧸ M)
