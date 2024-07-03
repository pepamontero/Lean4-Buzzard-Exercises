import Mathlib.Tactic

/-
SETS 04
Making sets from predicates
-/

theorem mem_def (X : Type) (P : X → Prop) (a : X) :
    a ∈ {x : X | P x} ↔ P a := by
  rfl

open Set

def IsEven (n : ℕ) : Prop :=
  ∃ t, n = 2 * t


example : 74 ∈ {n : ℕ | IsEven n} := by
  rw [Set.mem_def]
  use 37

def Real.IsEven (r : ℝ) :=
  ∃ t : ℝ, r = 2 * t

example : ∀ x, x ∈ {r : ℝ | Real.IsEven r} := by
  intro x
  rw [Set.mem_def]
  use (x / 2)
  ring

example : ∀ x, x ∉ {r : ℝ | 0 < r ∧ r < 0} := by
  intro x
  by_contra hn
  rw [Set.mem_def] at hn
  have h : x > 0 ∧ x < 0
  exact hn
  apply not_lt_of_gt h.left
  exact h.right
