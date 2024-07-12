import Mathlib.Tactic

/-
BIJECTIONS 01
Introduction to Bijective functions in Lean
-/


variable (X Y : Type) (f : X → Y)

example : Prop :=
  Function.Bijective f
-- =
example : Prop :=
  f.Bijective

-- Bijective = Injective and Surjective
example : f.Bijective ↔ f.Injective ∧ f.Surjective := by
  rfl

example : f.Bijective ↔
    (∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂) ∧ ∀ y : Y, ∃ x : X, f x = y := by
  rfl


-- Exercises

example : (∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id) → f.Bijective := by
  intro h
  cases' h with g h
  constructor

  · have hg : Function.Surjective g
    · intro x
      use f x
      have h1 : g (f x) = (g ∘ f) x
      · rfl
      rw [h1]
      rw [h.right]
      rfl

    intro x1 x2 hx
    have hg' : Function.Surjective g
    exact hg
    specialize hg x1
    specialize hg' x2

    cases' hg with y1 hy1
    cases' hg' with y2 hy2

    rw [← hy1, ← hy2] at hx

    have h1 : (y : Y) → f (g y) = (f ∘ g) y
    · intro y; rfl
    rw [h1, h1] at hx
    rw [h.left] at hx

    rw [← hy1, ← hy2]
    simp at hx
    rw [hx]

  · intro y
    use g y
    have h1 : f (g y) = (f ∘ g) y
    · rfl
    rw [h1]
    rw [h.left]
    rfl


example : f.Bijective → ∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id := by
  intro h
  cases' h with hinj hsurj
  choose g hg using hsurj
  use g
  constructor

  · ext y
    apply hg

  · ext x
    simp
    have h : f (g (f x)) = f x
    · apply hg
    apply hinj at h
    exact h
