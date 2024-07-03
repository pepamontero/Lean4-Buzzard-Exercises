import Mathlib.Tactic
import Lean4BuzzardExercises.Reals.reals5

/-
REALS 06
More results on limits of sequences
-/

/-------------- 1 --------------
If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`
-/

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

/-------------- 2 --------------
If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`.
-/

-- AUX
-- If x ≠ 0, x * x⁻¹ = 1
theorem nonneg_inverse_mul_eq_identity {x : ℝ} (h : ¬ x = 0): 1 = x * x⁻¹ := by
  rw [IsUnit.eq_mul_inv_iff_mul_eq]
  ring
  exact Ne.isUnit h


theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by

  rw [tendsTo_def] at *
  intro ε hε

  -- use ε' = ε / c, choose B for that ε'
  specialize h (ε / c) (by exact div_pos hε hc)
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

  -- PART 2  → I want to rewrite hB.right so it looks like my goal
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


/-------------- 3 --------------
If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/

theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by

  -- The idea of the proof is using -c > 0 and last result

  have hc1 : -c > 0
  linarith

  have ha : TendsTo (- a) (-t)
  apply tendsTo_neg
  exact h

  have ha2 : TendsTo (fun n => (- c) * (- a n)) ((- c) * (- t))
  apply tendsTo_pos_const_mul
  exact ha
  exact hc1

  rw [tendsTo_def]
  rw [tendsTo_def] at ha2

  intro ε hε
  specialize ha2 ε hε
  cases' ha2 with B hB
  use B
  intro n hn
  specialize hB n hn
  rw [neg_mul_neg c (a n)] at hB
  rw [neg_mul_neg c t] at hB
  exact hB

/-AUX-/
theorem tendsTo_zero_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t):
    TendsTo (fun n ↦ 0 * a n) 0 := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize h ε hε
  cases' h with B hB
  use B
  intro n _
  ring_nf
  rw [abs_lt] at *
  constructor
  linarith
  linarith

theorem tendsTo_zero_zero : TendsTo (fun _ ↦ 0) 0 := by
  rw [tendsTo_def]
  intro ε hε
  use 1
  intro n _
  ring_nf
  rw [abs_lt]
  constructor
  linarith
  linarith

theorem real_tricotomy {x : ℝ} : x = 0 ∨ x > 0 ∨ x < 0 := by
  have h : x = 0 ∨ ¬ x = 0
  exact eq_or_ne x 0
  cases' h with c1 c2
  left
  exact c1

  have h : x ≥ 0 ∨ x ≤ 0
  exact LinearOrder.le_total 0 x
  cases' h with h1 h2
  right
  left
  exact lt_of_le_of_ne h1 fun a => c2 (id (Eq.symm a))
  right
  right
  exact lt_of_le_of_ne h2 c2


/-------------- 4 --------------
If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`.
-/

theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by

  have hc : c = 0 ∨ c > 0 ∨ c < 0
  exact real_tricotomy

  -- case c = 0
  cases' hc with hc1 hc2
  rw [hc1]
  ring_nf
  apply tendsTo_zero_zero

  -- case c > 0
  cases' hc2 with hc1 hc2
  apply tendsTo_pos_const_mul
  exact h
  exact hc1

  -- case c < 0
  apply tendsTo_neg_const_mul
  exact h
  exact hc2


/-------------- 5 --------------
If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`.
-/

theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by

  have h2 : TendsTo (fun n => c * a n) (c * t)
  apply tendsTo_const_mul
  exact h

  rw [tendsTo_def] at *
  intro ε hε
  specialize h2 ε hε
  cases' h2 with B hB
  use B
  intro n hn
  specialize hB n hn

  rw [CommMonoid.mul_comm (a n) c]
  rw [CommMonoid.mul_comm t c]
  exact hB


/-------------- 6 --------------
If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`.
-/

theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by

  have h : TendsTo (fun n => (a n - b n) + b n) (t + u)
  apply tendsTo_add
  exact h1
  exact h2

  rw [tendsTo_def]
  rw [tendsTo_def] at h
  intro ε hε
  specialize h ε hε
  cases' h with B hB
  use B
  intro n hn
  specialize hB n hn
  rw [sub_add_cancel (a n) (b n)] at hB
  exact hB


/-------------- 7 --------------
If `a(n)` tends to `t` then `a(n)-t` tends to `0`.
-/

theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by

  constructor

  -- =>
  intro h
  rw [← add_right_neg t]
  apply tendsTo_add_const
  exact h

  -- <=
  intro h
  rw [tendsTo_def] at *
  intro ε hε
  specialize h ε hε
  cases' h with B hB
  use B
  intro n hn
  specialize hB n hn
  rw [sub_zero (a n - t)] at hB
  exact hB


/-AUX-/
theorem square_of_square_root {x : ℝ} (hx : x > 0): Real.sqrt x * Real.sqrt x = x := by
  rw [← Real.sqrt_mul]
  rw [Real.sqrt_mul_self_eq_abs]
  exact abs_of_pos hx
  exact le_of_lt hx

theorem mul_lt_mul_of_lt_of_lt'' {x y z w : ℝ} (hy : y > 0) (hz : z ≥ 0)
    (h1 : x < y) (h2 : z < w) : x * z < y * w := by

  have h : z > 0 ∨ z = 0
  exact LE.le.gt_or_eq hz
  cases' h with hz1 hz2

  exact mul_lt_mul_of_lt_of_lt' h1 h2 hy hz1

  rw [hz2]
  ring_nf
  have hw : w > 0
  rw [← hz2]
  exact h2
  exact Real.mul_pos hy hw


/-------------- 8 --------------
If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero.
-/

theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by

  rw [tendsTo_def] at *
  intro ε hε
  specialize ha (Real.sqrt ε) (by exact Real.sqrt_pos_of_pos hε)
  specialize hb (Real.sqrt ε) (by exact Real.sqrt_pos_of_pos hε)
  cases' ha with B1 hB1
  cases' hb with B2 hB2
  use max B1 B2
  intro n hn
  rw [max_le_iff] at hn
  specialize hB1 n hn.left
  specialize hB2 n hn.right
  ring_nf
  rw [sub_zero] at *
  rw [abs_mul]
  rw [← square_of_square_root hε]
  exact mul_lt_mul_of_lt_of_lt'' (by exact Real.sqrt_pos_of_pos hε) (by exact abs_nonneg (b n)) hB1 hB2


/-------------- 8 --------------
If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`.
-/

theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by

  rw [tendsTo_sub_lim_iff]
  rw [tendsTo_def] at *

  intro ε hε

  have h : (n : ℕ) → a n * b n - t * u - 0 = (a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u
  intro n
  ring_nf

  simp [h]

  sorry
