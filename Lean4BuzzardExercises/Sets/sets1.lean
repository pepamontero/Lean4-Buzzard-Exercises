import Mathlib.Tactic

/-
SETS 01
Introduction to subsets, unions and intersections
-/

variable (X : Type)
  (A B C D : Set X) -- A,B,C,D are subsets of `X`

-- DEFINITIONS
theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

variable (x : X)

theorem mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

theorem mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  Iff.rfl



example : A ⊆ A := by
  rfl

example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro h1 h2
  rw [subset_def] at *
  intro y
  intro hA
  apply h2
  apply h1
  exact hA

example : A ⊆ A ∪ B := by
  rw [subset_def]
  intro y hy
  rw [mem_union_iff]
  left
  exact hy

example : A ∩ B ⊆ A := by
  rw [subset_def]
  intro y hy
  rw [mem_inter_iff] at hy
  exact hy.left

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
  intro h1 h2
  rw [subset_def] at *
  intro y hy
  rw [mem_inter_iff]
  constructor
  apply h1
  exact hy
  apply h2
  exact hy

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
  intro h1 h2
  rw [subset_def] at *
  intro y h3
  rw [mem_union_iff] at h3
  cases' h3 with h3 h3
  apply h1
  exact h3
  apply h2
  exact h3

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := by
  intro h1 h2
  rw [subset_def] at *
  intro y h3
  rw [mem_union_iff] at *
  cases' h3 with h3 h3
  left
  apply h1
  exact h3
  right
  apply h2
  exact h3

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
  intro h1 h2
  rw [subset_def] at *
  intro y h3
  rw [mem_inter_iff] at *
  constructor
  apply h1
  exact h3.left
  apply h2
  exact h3.right
