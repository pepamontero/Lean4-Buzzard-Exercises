import Mathlib.Tactic

/-
LOGIC 03
Negations (¬)
Introducing tactics change, by_contra & by_cases
-/

example : ¬True → False := by
  trivial

example : False → ¬True := by
  trivial

example : ¬False → True := by
  trivial

example : True → ¬False := by
  trivial

example : False → ¬P := by
  intro h
  by_contra
  exact h

example : P → ¬P → False := by
  intro hP
  intro hNP
  -- Note: ¬ P is equivalent to P → False
  apply hNP
  exact hP

example : P → ¬¬P := by
  intro hP
  by_contra hNP
  apply hNP
  exact hP

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hNQ
  by_contra hP
  apply hNQ
  apply hPQ
  exact hP

example : ¬¬False → False := by
  trivial

example : ¬¬P → P := by
  intro hNNP
  by_contra hNP
  apply hNNP
  exact hNP

example : (¬Q → ¬P) → P → Q := by
  intro h1
  intro h2
  by_contra h3
  apply h1
  exact h3
  exact h2
