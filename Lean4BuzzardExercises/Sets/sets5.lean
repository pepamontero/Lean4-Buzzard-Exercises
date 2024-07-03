import Mathlib.Tactic -- import all the tactics
import Lean4BuzzardExercises.Sets.sets1

/-
SETS 05
Equality of sets
Introducing tactic ext
-/

open Set

variable (X : Type)
  (A B C D E : Set X)

example : A ∪ A = A := by
  ext x
  rw [mem_union_iff]
  constructor <;> intro h

  cases' h with h h <;> exact h

  left
  exact h

example : A ∩ A = A := by
  ext x
  rw [Set.mem_inter_iff]
  constructor <;> intro h

  exact h.left

  constructor <;> exact h


example : A ∩ ∅ = ∅ := by
  sorry

example : A ∪ univ = univ := by sorry

example : A ⊆ B → B ⊆ A → A = B := by sorry

example : A ∩ B = B ∩ A := by sorry

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by sorry

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by sorry

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by sorry

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by sorry
