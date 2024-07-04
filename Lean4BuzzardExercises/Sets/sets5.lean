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

/-
Note: most of these can be finished by using "exact?"
(maybe after an extra line)
but I will do them with the definitions
-/

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
  ext x
  rw [Set.mem_inter_iff]
  constructor <;> intro h

  exact h.right

  by_contra
  exact h


example : A ∪ univ = univ := by
  ext x
  rw [mem_union_iff]
  constructor <;> intro

  trivial

  by_contra h
  rw [not_or] at h
  apply h.right
  trivial


example : A ⊆ B → B ⊆ A → A = B := by
  intro h1 h2
  ext x
  constructor <;> intro h3

  apply h1
  exact h3

  apply h2
  exact h3


example : A ∩ B = B ∩ A := by
  ext x
  rw [Set.mem_inter_iff, Set.mem_inter_iff]
  constructor
  all_goals intro h
  all_goals constructor
  all_goals try exact h.right
  all_goals exact h.left


example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff]
  constructor <;> intro h
  all_goals constructor
  all_goals try constructor
  exact h.left
  exact h.right.left
  exact h.right.right
  exact h.left.left
  exact h.left.right
  exact h.right


example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  rw [mem_union_iff, mem_union_iff, mem_union_iff, mem_union_iff]
  constructor <;> intro h
  all_goals cases' h with h h
  all_goals try cases' h with h h
  left; left; exact h
  left; right; exact h
  right; exact h
  left; exact h
  right; left; exact h
  right; right; exact h


example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  rw [mem_union_iff, Set.mem_inter_iff, Set.mem_inter_iff, mem_union_iff, mem_union_iff]
  constructor
  all_goals intro h

  constructor <;> cases' h with h h

  left; exact h
  right; exact h.left

  left; exact h
  right; exact h.right

  have h1 : (x ∈ A ∨ x ∈ B)
  exact h.left
  have h2 : (x ∈ A ∨ x ∈ C)
  exact h.right

  cases' h1 with h1 h1
  left; exact h1

  cases' h2 with h2 h2
  left; exact h2
  right; constructor; exact h1; exact h2


example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  symm
  exact Eq.symm (inter_union_distrib_left A B C)
