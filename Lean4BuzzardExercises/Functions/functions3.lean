import Mathlib.Tactic
import Lean4BuzzardExercises.Functions.functions1

/-
FUNCTIONS 03
Results about surjectivity and injectivity in composition
-/

/-
Q: If `f : X → Y` and `g : Y → Z` and `g ∘ f` is injective,
  is it true that `g` is injective?"
A: No. We want to see a counter example
-/

-- We have inductive types: X = {a}, Y = {b, c}, Z = {d}

inductive X : Type
  | a : X -- X.a

inductive Y : Type
  | b : Y
  | c : Y

inductive Z : Type
  | d : Z

-- Define f by f(X.a)=Y.b
def f : X → Y
  | X.a => Y.b

-- define g by g(Y.b) = g(Y.c) = Z.d
def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d

-- `g ∘ f` is injective and surjective, since it takes a to d only
-- but g is not injective, and f is not surjective

-- Observations:
example (z : Z) : z = Z.d := by
  cases z
  rfl

theorem Yb_ne_Yc : Y.b ≠ Y.c := by
  intro h
  cases h

-- EXERCISES

theorem gYb_eq_gYc : g Y.b = g Y.c := by
  rw [g]

open Function

/-
1. (g ∘ f) injective ≠> f injective
-/

theorem gf_injective : Injective (g ∘ f) := by
  rw [Injective]
  intro x y _

  have h2 : f x = Y.b
  rw [f]

  have h3 : g Y.b = Z.d
  rw [g]

  have h4 : (g ∘ f) x = g Y.b
  rw [← h2]

  rw [h3] at h4

theorem g_not_injective : ¬ Injective g := by
  intro h
  rw [injective_def] at h
  specialize h Y.b Y.c

  have hn : Y.b = Y.c
  apply h
  rw [g]

  cases hn

example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Injective (ψ ∘ φ) → Injective ψ := by
  intro h
  apply g_not_injective
  specialize h X Y Z f g
  apply h
  exact gf_injective


/-
2. (g ∘ f) surjective ≠> f surjective
-/
theorem gf_surjective : Surjective (g ∘ f) := by
  rw [surjective_def]
  intro x
  use X.a

theorem f_not_surjective : ¬ Surjective f := by
  intro h1
  rw [surjective_def] at h1
  specialize h1 Y.c
  cases' h1 with x hx
  cases x

  have h : f X.a = Y.b
  rw [f]

  rw [hx] at h
  cases h

-- Another question from IUM
example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ := by
  intro h
  apply f_not_surjective
  specialize h X Y Z f g
  apply h
  exact gf_surjective
