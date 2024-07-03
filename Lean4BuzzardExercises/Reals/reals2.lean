import Mathlib.Tactic

/-
REALS 02
Introducing tactic ring
-/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example : ∀ a b : ℝ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  intro a b
  use 3
  ring_nf

example : ∃ x : ℝ, ∀ y : ℝ, y + y = x * y := by
  use 2
  intro y
  ring

example : ∀ x : ℝ, ∃ y, x + y = 2 := by
  intro x
  use 2 - x
  ring

example : ∀ x : ℝ, ∃ y, x + y ≠ 2 := by
  intro x
  use 2 - x + 1
  ring_nf
  norm_num
