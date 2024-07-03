import Mathlib.Tactic
import Lean4BuzzardExercises.Reals.reals3

theorem convergent_is_bounded (a : ℕ → ℝ) (t : ℝ) : TendsTo a t →
    ∃ (K : ℝ), ∀ (n : ℕ), K > |a n| := by

  intro ha
  rw [tendsTo_def] at ha
  specialize ha 1 (by linarith)
  cases' ha with B hB
  use (1 + |t|) -- should actually be max (1 + |t|) (max a n)
  intro n

  have hn : B ≤ n ∨ n < B
  exact le_or_lt B n

  cases' hn with h1 h2

  specialize hB n h1
  rw [← sub_add_cancel (a n) t]
  have h : |a n - t + t| ≤ |a n - t| + |t|
  exact abs_add (a n - t) t
  have h' : |a n - t| + |t| < 1 + |t|
  rw [← add_lt_add_iff_right |t|] at hB
  exact hB
  exact lt_of_le_of_lt h h'

  -- now i should be able to use that the a n with n < B
  -- are finite and thus have a max
  sorry
