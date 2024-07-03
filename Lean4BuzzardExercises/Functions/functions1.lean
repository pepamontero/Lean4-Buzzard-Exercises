import Mathlib.Tactic
open Function
variable (X Y Z : Type)

/-
FUNCTIONS 01
-/

-- DEFINITIONS

theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl

theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b := by
  rfl

theorem id_eval (x : X) : id x = x := by
  rfl

theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl

-- EXERCISES

example : Injective (id : X → X) := by

  rw [injective_def]
  intro a b
  rw [id_eval]
  rw [id_eval]
  intro h
  exact h

example : Surjective (id : X → X) := by

  rw [surjective_def]
  intro b
  use b
  rw [id_eval]

-- Theorem: if f : X → Y and g : Y → Z are injective,
-- then so is g ∘ f
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  rw [injective_def] at *
  intro a b h
  apply hg at h
  -- Note: Lean reads (g ∘ f) a = g (f a) identically
  apply hf at h
  exact h

-- Theorem: composite of two surjective functions
-- is surjective.
example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  rw [surjective_def] at *
  intro b
  specialize hg b
  cases' hg with x hx
  specialize hf x
  cases' hf with a ha
  use a
  rw [← ha] at hx
  exact hx

example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  intro h
  rw [injective_def] at *
  intro a b h1

  have h2 : g (f a) = g (f b)
  rw [h1]

  specialize h a b
  apply h
  exact h2

-- This is another one
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  intro h
  rw [surjective_def] at *
  intro b
  specialize h b
  cases' h with a ha
  use (f a)
  exact ha
