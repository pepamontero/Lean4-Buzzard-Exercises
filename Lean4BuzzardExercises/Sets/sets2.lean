import Mathlib.Tactic

/-
SETS 02
The empty set (∅) and the universal set (Set.univ)
-/

open Set

variable (X : Type)
  (A B C D E : Set X)
  (x y z : X)

open Set

example : x ∈ (univ : Set X) := by
  trivial

example : x ∈ (∅ : Set X) → False := by
  intro h
  cases h

example : A ⊆ univ := by
  intro a _
  trivial

example : ∅ ⊆ A := by
  intro a h
  cases h
