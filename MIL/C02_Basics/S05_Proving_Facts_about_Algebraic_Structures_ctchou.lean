import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

lemma inf_lemma0 : x ⊓ y = y ⊓ x := by
--  sorry
  have h : ∀ a b : α, a ⊓ b ≤ b ⊓ a := by
    intro a b
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  apply le_antisymm
  apply h
  apply h

lemma inf_lemma1 : ∀ a b c : α, a ≤ b → a ⊓ c ≤ b ⊓ c := by
  intro a b c h
  apply le_inf
  . have h' : a ⊓ c ≤ a := by apply inf_le_left
    apply le_trans h' h
  . apply inf_le_right

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
--  sorry
  have h1 : ∀ a b c : α, a ⊓ b ⊓ c ≤ a ⊓ (b ⊓ c) := by
    intro a b c
    apply le_inf
    . calc a ⊓ b ⊓ c ≤ a ⊓ c := by { apply inf_lemma1 ; apply inf_le_left }
                   _ ≤ a := by apply inf_le_left
    . apply inf_lemma1 ; apply inf_le_right
  apply le_antisymm
  . apply h1
  . rw [(inf_lemma0 x (y ⊓ z)), (inf_lemma0 (x ⊓ y) z), (inf_lemma0 y z), (inf_lemma0 x y)]
    apply h1

lemma sup_lemma0 : x ⊔ y = y ⊔ x := by
--  sorry
  have h : ∀ a b : α, a ⊔ b ≤ b ⊔ a := by
    intro a b
    apply sup_le
    apply le_sup_right
    apply le_sup_left
  apply le_antisymm
  apply h
  apply h

lemma sup_lemma1 : ∀ a b c : α, a ≤ b → c ⊔ a ≤ c ⊔ b := by
--  sorry
  intro a b c h
  apply sup_le
  . apply le_sup_left
  . have h' : b ≤ c ⊔ b := by apply le_sup_right
    apply le_trans h h'

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
--  sorry
  have h1 : ∀ a b c : α, a ⊔ b ⊔ c ≤ a ⊔ (b ⊔ c) := by
    intro a b c
    apply sup_le
    . apply sup_lemma1 ; apply le_sup_left
    . calc c ≤ a ⊔ c := by { apply le_sup_right }
          _ ≤ a ⊔ (b ⊔ c) := by { apply sup_lemma1 ; apply le_sup_right }
  apply le_antisymm
  . apply h1
  . rw [(sup_lemma0 x (y ⊔ z)), (sup_lemma0 (x ⊔ y) z), (sup_lemma0 y z), (sup_lemma0 x y)]
    apply h1

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
--  sorry
  apply le_antisymm
  . apply inf_le_left
  . apply le_inf
    . apply le_refl
    . apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
--  sorry
  apply le_antisymm
  . apply sup_le
    . apply le_refl
    . apply inf_le_left
  . apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

lemma aux1 (h : a ≤ b) : 0 ≤ b - a := by
--  sorry
 calc 0 = -a + a := by abel
      _ ≤ -a + b := by apply add_le_add_left h
      _ = b - a := by abel

lemma aux2 (h: 0 ≤ b - a) : a ≤ b := by
--  sorry
  calc a = a + 0 := by abel
       _ ≤ a + (b - a) := by apply add_le_add_left h
       _ = b := by abel

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
--  sorry
  have h1 : 0 ≤ b - a := by
    apply aux1
    exact h
  apply aux2
  have h2 : 0 ≤ (b - a) * c := by
    apply mul_nonneg
    . exact h1
    . exact h'
  calc 0 ≤ (b - a) * c := by apply h2
       _ = b * c - a * c := by noncomm_ring

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
--  sorry
  have h : 0 ≤ 2 * (dist x y) := by
    calc 0 = dist x x := by rw [dist_self]
         _ ≤ dist x y + dist y x := by apply dist_triangle
         _ = 2 * (dist x y) := by {rw [← dist_comm x y] ; ring}
  linarith

end
