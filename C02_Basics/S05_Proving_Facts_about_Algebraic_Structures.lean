import Mathlib.Tactic
import Mathlib.Util.Delaborators
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

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  . show x ⊓ y ≤ y ⊓ x
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  . show y ⊓ x ≤ x ⊓ y
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . apply le_inf
    . trans x ⊓ y
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    . trans x ⊓ y
      apply inf_le_left
      apply inf_le_right
    . apply inf_le_right
  . apply le_inf
    . apply le_inf
      . apply inf_le_left
      . trans y ⊓ z
        apply inf_le_right
        apply inf_le_left
    . trans y ⊓ z
      apply inf_le_right
      apply inf_le_right


example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  . apply sup_le
    apply sup_le
    . apply le_sup_left
    . trans y ⊔ z
      apply le_sup_left
      apply le_sup_right
    . trans y ⊔ z
      apply le_sup_right
      apply le_sup_right
  . apply sup_le
    . trans x ⊔ y
      apply le_sup_left
      apply le_sup_left
    apply sup_le
    . trans x ⊔ y
      apply le_sup_right
      apply le_sup_left
    . apply le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  . show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    . apply le_refl
    . apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . show x ⊔ x ⊓ y ≤ x
    apply sup_le
    apply le_refl
    apply inf_le_left
  . show x ≤ x ⊔ x ⊓ y
    apply le_sup_left


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
  rw [h (a ⊔ b) a c]
  rw [inf_comm (a ⊔ b), absorb1]
  rw [inf_comm (a ⊔ b), h, ← sup_assoc, inf_comm c a, absorb2, inf_comm c b]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [sup_comm (a ⊓ b), absorb2]
  rw [sup_comm (a ⊓ b), h, sup_comm c a, ← inf_assoc, absorb1, sup_comm c b]


end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, add_comm, sub_eq_add_neg, add_comm b]
  exact add_le_add_left h (-a)


example (h: 0 ≤ b - a) : a ≤ b := by
  have := add_le_add_left h a
  rw [add_comm a (b - a), sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, add_zero] at this
  exact this

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have : 0 ≤ (b - a) * c := by
    apply mul_nonneg
    . show 0 ≤ b - a
      rw [← sub_self a, sub_eq_add_neg, add_comm, sub_eq_add_neg, add_comm b]
      exact add_le_add_left h (-a)
    exact h'
  rw [sub_mul] at this
  rw [← add_zero (a * c), ← sub_add_cancel (b * c) (a * c), add_comm (b * c - a * c)]
  apply add_le_add_left this

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have := dist_triangle y x y
  rw [dist_self, dist_comm, ← two_mul] at this
  linarith

end
