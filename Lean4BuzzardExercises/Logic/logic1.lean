import Mathlib.Tactic

/-
LOGIC 01
Introduction to tactics intro, exact & apply
-/

theorem L1_1 (P : Prop) : P → P := by
  intro h
  exact h

-- from now on, P, Q and R are propositions
variable (P Q R : Prop)

example : P → Q → P := by
  intro h
  intro
  exact h

example : (P → Q → R) → (P → Q) → P → R := by
  intro h1
  intro h2
  intro hP
  apply h1
  exact hP
  apply h2
  exact hP

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  intro h1
  intro h2
  intro
  apply h2
  intro hQ
  apply h1
  intro
  exact hQ

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  intro h1
  intro h2
  intro h3
  apply h1
  intro hQ
  apply h3
  apply h2
  exact hQ

example : (((P → Q) → Q) → Q) → P → Q := by
  intro h1
  intro hP
  apply h1
  intro h2
  apply h2
  exact hP

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  intro
  intro h2
  intro
  apply h2
  intro h4
  intro
  intro
  apply h4
  intro hP
  exact hP
