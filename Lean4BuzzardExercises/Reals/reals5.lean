import Mathlib.Tactic
import Lean4BuzzardExercises.Reals.reals3

/-
REALS 05
More results on limits of sequences
-/

theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  rw [tendsTo_def]
  rw [tendsTo_def] at ha
  -- initialize
  intros ε hε
  apply ha at hε

  -- show that |-a n - -t| = |a n - t|
  have h2 : (n : ℕ) → |-a n - -t| = |a n - t|
  intros n
  rw [← abs_neg (-a n - -t)]
  ring_nf

  cases' hε with B hB
  use B
  intros n hn
  rw [h2]
  apply hB
  exact hn

theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) := by

  rw [tendsTo_def] at *

  intros ε hε

  -- find B1 and B2 existing for ε/2 > 0
  specialize ha (ε / 2) (by linarith)
  cases' ha with B1 hB1

  -- similarly, for B2 (diff notation)
  obtain ⟨B2, hB2⟩ := hb (ε / 2) (by linarith)

  -- take B = max {B1, B2}
  use max B1 B2
  intro n hn
  rw [max_le_iff] at hn
  specialize hB1 n hn.left
  specialize hB2 n hn.right

  rw [abs_lt] at *
  constructor
  linarith
  linarith


theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by

  apply tendsTo_add
  exact ha
  apply tendsTo_neg
  exact hb
