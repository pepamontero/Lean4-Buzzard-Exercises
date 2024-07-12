import Mathlib.Tactic

/-
FINITENESS O3
Finite types in Lean
-/


-- Finite types by Prop `Finite X`
variable (X : Type) [Finite X]
variable (Y : Type) [Finite Y]

example : Finite (X × Y) :=
  inferInstance

example : Finite (X → Y) :=
  inferInstance

-- The type `Fin n`
example : Fin 37 :=
  ⟨3, by linarith⟩

example : Finite (Fin 37) :=
  inferInstance


-- Finite tyoes by Type `Fintype X`
variable (X : Type) [Fintype X]

/-
We can see that `Fintype X` is really just a term `elems` of
type `Finset X` with a proof that `∀ (x : X), x ∈ elems`
-/
example : X = X := by
  rename_i foo
  cases foo
  rfl

example (n : ℕ) : Fintype (Fin n) :=
  inferInstance

open scoped BigOperators

example : ∑ x : Fin 10, x = 45 := by
  rfl

example : ∑ x : Fin 10, x = 25 := by
  rfl

example : ∑ x : Fin 10, x.val = 45 := by
  rfl
