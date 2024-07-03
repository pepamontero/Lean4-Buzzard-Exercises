import Mathlib.Tactic

/- LOGIC 04
And conjuction
Introducing tactics cases, constructor
-/

example : P ∧ Q → P := by
  intro h
  exact h.left

example : P ∧ Q → Q := by
  intro h
  exact h.right

example : (P → Q → R) → P ∧ Q → R := by
  intro h1
  intro h2
  apply h1
  exact h2.left
  exact h2.right

example : P → Q → P ∧ Q := by
  intros hP hQ
  constructor
  exact hP
  exact hQ

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  exact h.right
  exact h.left

example : P → P ∧ True := by
  intro hP
  constructor
  exact hP
  trivial

example : False → P ∧ False := by
  intro h
  constructor
  by_contra
  exact h
  exact h

example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1
  intro h2
  constructor
  exact h1.left
  exact h2.right

example : (P ∧ Q → R) → P → Q → R := by
  intro h1
  intro hP
  intro hQ
  apply h1
  constructor
  exact hP
  exact hQ
