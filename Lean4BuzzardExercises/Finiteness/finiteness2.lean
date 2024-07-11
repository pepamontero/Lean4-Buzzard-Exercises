import Mathlib.Tactic

/-
FINITENESS 02
The lattice of finite sets
-/


variable (X : Type)

open scoped Classical

noncomputable section

example : Lattice (Finset X) :=
  inferInstance

example (a b : Finset X) : Finset X :=
  a ⊔ b

example : Finset X :=
  ⊥

-- Note: there needn't be a largest finite subset neccessarily

-- Pushing forward finsets
variable (Y : Type) (f : X → Y)

example (S : Finset X) : Finset Y :=
  Finset.image f S
-- or
example (S : Finset X) : Finset Y :=
  S.image f

-- Exercises

example (S : Finset X) (y : Y) : y ∈ S.image f ↔ ∃ x ∈ S, f x = y := by
  exact Finset.mem_image

example (S : Finset X) (x : X) (hx : x ∈ S) : f x ∈ S.image f := by
  exact Finset.mem_image_of_mem f hx

example (S T : Finset X) (h : S ≤ T) : S.image f ≤ T.image f := by
  intro y hy
  rw [Finset.mem_image] at *
  cases' hy with a ha
  use a
  constructor
  apply h
  exact ha.left
  exact ha.right
