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

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x h

  rw [pushback_def, pullback_def]



example : f '' (f ⁻¹' T) ⊆ T := by sorry

-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by sorry

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
