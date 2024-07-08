import Mathlib.Tactic

/-
ORDERINGS 01
Partial orders in Lean
Introduction to tactic trans
-/


variable (X : Type) [PartialOrder X]
/- A PartialOrder type has the following properties:
- `le_refl a : a ≤ a`
- `le_antisymm : a ≤ b → b ≤ a → a = b`
- `le_trans : a ≤ b → b ≤ c → a ≤ c`
-/

example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc

example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  trans b
  exact hab
  exact hbc


variable (a b c d : X)

example : a ≤ a := by
  exact le_refl a

example (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  trans b
  exact hab
  trans c
  exact hbc
  exact hcd

example (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = b := by
  apply le_antisymm
  exact hab
  exact le_trans hbc hca
