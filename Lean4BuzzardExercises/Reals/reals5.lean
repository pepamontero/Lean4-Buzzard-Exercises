import Mathlib.Tactic
import Lean4BuzzardExercises.Reals.reals3


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

  -- cases for exist!!
  cases' hε with B hB
  use B
  intros n hn
  rw [h2]
  apply hB
  exact hn
