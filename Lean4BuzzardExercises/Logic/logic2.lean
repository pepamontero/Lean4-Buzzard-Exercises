import Mathlib.Tactic

/-
LOGIC 02
Introducing tactics triv & exfalso
-/

example : True := by
  trivial

example : True → True := by
  intro
  trivial

example : False → True := by
  intro
  trivial

example : False → False := by
  intro h
  exact h

example : (True → False) → False := by
  intro h
  apply h
  trivial

example : False → P := by
  intro h
  exfalso
  apply h

example : True → False → True → False → True → False := by
  intros _ h2 _ _ _
  exact h2

example : P → (P → False) → False := by
  intros hP hF
  apply hF
  exact hP

example : (P → False) → P → Q := by
  intros h1 h2
  exfalso
  apply h1
  exact h2

example : (True → False) → P := by
  intro h1
  exfalso
  apply h1
  trivial
