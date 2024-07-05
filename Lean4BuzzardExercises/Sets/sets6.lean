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


variable (Z : Type) (g : Y → Z) (U : Set Z)

example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  constructor <;> intro h

  /-    =>
  We know that
  `x ∈ (g ∘ f) ⁻¹ (U) = {x : X | (g ∘ f) (x) ∈ U}`
  and we want to see that
  `x ∈ f⁻¹(g⁻¹(U)) = {x : X | f x ∈ g⁻¹(U)} = {x : X | f x ∈ {y : Y | g y ∈ U}}`
  Thus, what we really need is `f x ∈ g⁻¹(U)`, or `(g ∘ f) x ∈ U`
  But this follows from the fact that `x ∈ (g ∘ f)⁻¹ (U)`
  -/
  apply h

  /-    <=
  Similar -/
  apply h

-- NOTAS
/-
  Sabemos que:
  f : X → Y
  g : Y → Z
  g ∘ f : X → Z

  U ⊆ Z-/

  /-
  f(S) = {y : Y | ∃ x : X, x ∈ S ∧ f x = y}
  f⁻¹(T) = {x : X | f x ∈ T}
  -/


example : g ∘ f '' S = g '' (f '' S) := by
  ext z
  constructor <;> intro h

  /- =>
  We know `x ∈ (g ∘ f) (S)`
  We want to know if `x ∈ g(f(S))`, with
  g(f(S)) = {z : Z | ∃ y : Y, y ∈ f(S) ∧ g y = z} =
    {z : Z | ∃ y : Y, y ∈ {y : Y | ∃ x : X, x ∈ S ∧ f x = y} ∧ g y = z} =
    {z : Z | ∃ x : X, x ∈ S ∧ g (f x) = z}
  -/
  cases' h with x hx
  use f x
  constructor
  use x
  constructor
  exact hx.left
  rfl
  exact hx.right

  -- <= (Similar)
  cases' h with y hy
  cases' hy with hy1 hy2
  cases' hy1 with x hx
  use x
  constructor
  exact hx.left
  rw [← hx.right] at hy2
  exact hy2
