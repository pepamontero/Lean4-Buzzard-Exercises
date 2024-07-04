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

  have h1 : ∃ (x : X), x ∈ S ∧ f x = y
  exact hy

  cases' h1 with x hx

  have h2 : x ∈ f ⁻¹' T
  apply h
  exact hx.left
  rw [← hx.right]
  exact h2



-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by sorry

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by sorry

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by sorry

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by sorry
