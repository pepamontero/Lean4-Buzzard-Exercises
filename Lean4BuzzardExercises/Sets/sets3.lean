import Mathlib.Tactic

/-
SETS 03
Not in (∉) and complement (ᶜ) of a set
-/

/-
If you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Q: ¿why?
x ∈ Aᶜ ↔ x ∉ A ↔ ¬ x ∈ A ↔ (x ∈ A → False)
so then by applying h is applying x ∈ A → False
-/

open Set

variable (X : Type)
  (A B C D E : Set X)
  (x y z : X)


example : x ∉ A → x ∈ A → False := by
  intro h1 h2
  trivial

example : x ∈ A → x ∉ A → False := by
  intro h1 h2
  trivial

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro h1 h2
  by_contra hA
  rw [subset_def] at h1
  apply h2
  apply h1
  exact hA

example : x ∉ (∅ : Set X) := by
  by_contra hx
  apply hx

example : x ∈ Aᶜ → x ∉ A := by
  intro h1
  trivial

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor

  intro h
  by_contra hn
  cases' hn with w hw
  apply hw
  apply h

  intro h
  intro w
  by_contra hn
  apply h
  use w
  exact hn

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor

  intro h
  by_contra hn
  cases' h with w hw
  specialize hn w
  exact hn hw

  intro h
  by_contra hn
  apply h
  intro x
  by_contra hn'
  apply hn
  use x
  by_contra hn''
  exact hn' hn''
