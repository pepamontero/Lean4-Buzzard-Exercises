import Mathlib.Tactic

/-
LOGIC 05
Working with iif
Introducing tactics rfl, rw
-/

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h
  rw [h]
  intro h
  rw [h]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1
  intro h2
  rw [h1]
  exact h2

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h1
  constructor
  exact h1.right
  exact h1.left
  intro h1
  constructor
  exact h1.right
  exact h1.left

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro h1
  constructor
  exact h1.left.left
  constructor
  exact h1.left.right
  exact h1.right
  intro h1
  constructor
  constructor
  exact h1.left
  exact h1.right.left
  exact h1.right.right

example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  exact hP
  trivial
  intro h
  exact h.left

example : False ↔ P ∧ False := by
  constructor
  intro hF
  constructor
  by_contra
  exact hF
  exact hF
  intro h
  exact h.right

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ
  intro hRS
  constructor
  intro h
  constructor
  rw [← hPQ]
  exact h.left
  rw [← hRS]
  exact h.right
  intro h
  constructor
  rw [hPQ]
  exact h.left
  rw [hRS]
  exact h.right

example : ¬(P ↔ ¬P) := by
  by_contra h
  have h1 : P → ¬ P
  rw [← h]
  intro hP
  exact hP
  have h2 : ¬ P → P
  rw [← h]
  intro hP
  exact hP
  apply h1
  apply h2
  by_contra hP
  apply h1
  exact hP
  exact hP
  by_contra h3
  apply h1
  apply h2
  exact h3
  apply h2
  exact h3
