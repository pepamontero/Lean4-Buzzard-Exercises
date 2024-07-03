import Mathlib.Tactic

/-
REALS 03
Working with sequences of real numbers
Introducing tactic rewrite (rw)
-/


-- Definition of a(n) tends to t when n tends to infinity
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl

theorem tendsTo_thirtyseven : TendsTo (fun _ ↦ 37) 37 := by
  rw [TendsTo]
  intros e he
  use 1
  intros
  norm_num
  exact he

theorem tendsTo_const (c : ℝ) : TendsTo (fun _ ↦ c) c := by
  rw [TendsTo]
  intros e he
  use 1
  intros
  ring_nf
  norm_num
  exact he

theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) := by
  -- rewrite definition of tends to
  rw [tendsTo_def]
  rw [tendsTo_def] at h
  -- initialize
  intros ε hε
  apply h at hε
  ring_nf
  exact hε
