import Mathlib.Tactic

/-
ORDERINGS 03
-/


example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  constructor <;> intro h
  <;> intro a b c
  <;> apply le_antisymm

  -- a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c
  sorry

  -- a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c)
  apply sup_le <;> all_goals apply inf_le_inf_left
  exact le_sup_left
  exact le_sup_right

  -- a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c)
  apply le_inf <;> apply sup_le_sup_left
  exact inf_le_left
  exact inf_le_right

  -- (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ b ⊓ c
  specialize h (a ⊔ b) a c
  rw [h]
  apply sup_le

  trans a
  exact inf_le_right
  exact le_sup_left
