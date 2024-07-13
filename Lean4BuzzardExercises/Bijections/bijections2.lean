import Mathlib.Tactic

/-
BIJECTIONS 02
Bijection as constructive type in Lean
-/

/-
An elemento of type `X ≃ Y` has 4 elements:
- toFun: a function `f : X → Y`
- invFun: its inverse `g : Y → X`
- left_inv: a proof that `∀ x, g (f x) = x`
- right_inf: a proof that `∀ y, f (g y) = y`
-/

-- Example
def bijection1 : ℚ ≃ ℚ where
  toFun := id
  invFun := id
  left_inv :=
    by
    intro q
    rfl
  right_inv q := rfl

-- Exercise
def bijection2 : ℚ ≃ ℚ where
  toFun q := 3 * q + 4
  invFun r := (r - 4) / 3
  left_inv := by
    intro r
    ring
  right_inv := by
    intro q
    ring


example : bijection1 ≠ bijection2 := by
  unfold bijection1 bijection2
  intro h
  simp at h
  cases' h with h1 _
  rw [Function.funext_iff] at h1
  specialize h1 37
  norm_num at h1
