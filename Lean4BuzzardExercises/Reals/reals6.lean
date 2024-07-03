import Mathlib.Tactic
import Lean4BuzzardExercises.Reals.reals5

/-
REALS 06
More results on limits of sequences
-/

/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by

  rw [tendsTo_def] at *
  intro ε hε
  specialize h (ε / 37) (by linarith)
  cases' h with B hB
  use B
  intro n hn
  specialize hB n hn
  rw [abs_lt] at *
  constructor
  linarith
  linarith

-- AUX
-- If x ≠ 0, x * x⁻¹ = 1
theorem nonneg_inverse_mul_eq_identity {x : ℝ} (h : ¬ x = 0): 1 = x * x⁻¹ := by
  rw [IsUnit.eq_mul_inv_iff_mul_eq]
  ring
  exact Ne.isUnit h

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by

  rw [tendsTo_def] at *
  intro ε hε

  -- show ε / c > 0
  have hεc : ε / c > 0
  apply Real.mul_pos
  exact hε
  exact inv_pos_of_pos hc

  -- use ε' = ε / c, choose B for that ε'
  specialize h (ε / c) hεc
  cases' h with B hB
  use B
  intro n hn
  specialize hB n hn
  rw [abs_lt] at *
  constructor

  -- PART 1 → I want to rewrite hB.left so it looks like my goal
  rw [← mul_lt_mul_iff_of_pos_right hc] at hB

  have hB1 : -(ε / c) * c = -ε
  ring_nf
  rw [mul_assoc ε c (c⁻¹)]
  rw [← nonneg_inverse_mul_eq_identity (by linarith)]
  ring

  have hB2 : (a n - t) * c = c * a n - c * t
  rw [CommMonoid.mul_comm]
  rw [mul_sub_left_distrib]

  rw [hB1] at hB
  rw [hB2] at hB
  exact hB.left

  -- PARTE 2  → I want to rewrite hB.right so it looks like my goal
  have hBR : a n - t < ε / c
  exact hB.right
  rw [← mul_lt_mul_iff_of_pos_right hc] at hBR

  have hB1 : ε / c * c = ε
  ring_nf
  rw [mul_assoc ε c (c⁻¹)]
  rw [← nonneg_inverse_mul_eq_identity (by linarith)]
  ring

  have hB2 : (a n - t) * c = c * a n - c * t
  rw [CommMonoid.mul_comm]
  rw [mul_sub_left_distrib]

  rw [hB1] at hBR
  rw [hB2] at hBR
  exact hBR
