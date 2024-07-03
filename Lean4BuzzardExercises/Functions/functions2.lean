/-
FUNCTIONS 02
NOTE: no exercises on this section
Introduction to inductive types in Lean
-/

import Mathlib.Tactic

-- A type with three terms
inductive X : Type
  | a : X
  | b : X
  | c : X

open X

#check a

example (x : X) : x = a ∨ x = b ∨ x = c := by
  cases x with
  | a => left; rfl
  | b => right; left; rfl
  | c => right; right; rfl

-- terms in type X are distinct
example : a ≠ b :=
  by
  intro h
  cases h

-- defining a function on X
def f : X → ℕ
  | a => 37
  | b => 42
  | c => 0

example : f a = 37 := by-- true by definition
  rfl

-- f is injective
example : Function.Injective f := by
  intro x y h
  -- x can be a b or c, then in each case
  -- y can be a b or c
  cases x <;> cases y -- produces 9 goals
  all_goals try rfl -- use rfl in all goals possible
  -- 6 goals left
  all_goals cases h
