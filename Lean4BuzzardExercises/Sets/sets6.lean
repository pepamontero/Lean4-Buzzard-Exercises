import Mathlib.Tactic

/-
SETS 06
Pushback ( f(S) ) and pullback ( f⁻¹(S) )
-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

theorem pushback_def (X Y : Type) (f : X → Y) (S : Set X) :
    f '' S = {y : Y | ∃ x : X, x ∈ S ∧ f x = y} := by
  rfl

theorem pullback_def (X Y : Type) (f : X → Y) (T : Set Y) :
    f ⁻¹' (T) = {x : X | f x ∈ T} := by
  rfl

theorem member_set_iff (X : Type) (x : X) (P : X → Bool) : x ∈ {y : X | P y} ↔ P x := by
  rfl

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x h
  rw [pushback_def, pullback_def]
  use x


example : f '' (f ⁻¹' T) ⊆ T := by
  intro y h
  rw [pushback_def, pullback_def] at h
  cases' h with x hx
  rw [← hx.right]
  exact hx.left

example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor

  -- =>
  intro h x hx
  apply h
  use x

  -- <=
  intro h y hy
  cases' hy with x hx
  rw [← hx.right]
  apply h
  exact hx.left


example : id ⁻¹' S = S := by
  ext x
  constructor <;> intro h <;> exact h


example : id '' S = S := by
  ext x
  constructor <;> intro h

  -- id '' S ⊆ S
  cases' h with w hw

  have h2 : id w = x ↔ w = x
  exact Eq.congr_right (by rfl)

  cases' hw with hw1 hw2

  rw [h2] at hw2
  rw [← hw2]
  exact hw1

  -- S ⊆ id '' S
  use x
  constructor
  exact h
  rfl


-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by sorry

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by sorry
