import Mathlib.Tactic

/-
ORDERINGS 02
Lattices in Lean
-/

variable (L : Type) [Lattice L] (a b c : L)

/- A Lattice type has the following properties:
- `a ⊔ b` := least upper bound of `a` and `b`:
- `le_sup_left : a ≤ a ⊔ b`
- `le_sup_right : b ≤ a ⊔ b`
- `sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c`

- `a ⊓ b` := greatest lower bound of `a` and `b`:
- `inf_le_left : a ⊓ b ≤ a`
- `inf_le_right : a ⊓ b ≤ b` -- `a ⊓ b`
- `le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c`

Note that Lattices are Patial orders, so they have
the three properties from Partial orders as well
-/

example : a ⊔ b = b ⊔ a := by
  -- Can be solved with `exact sup_comm a b`
  apply le_antisymm
  all_goals apply sup_le
  all_goals try exact le_sup_right
  all_goals try exact le_sup_left

example : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  -- Can be solved with `exact sup_assoc a b c`
  apply le_antisymm
  apply sup_le

  -- a ⊔ b ≤ a ⊔ (b ⊔ c)
  apply sup_le
  -- a ≤ a ⊔ (b ⊔ c)
  exact le_sup_left
  -- b ≤ a ⊔ (b ⊔ c)
  trans b ⊔ c
  exact le_sup_left
  exact le_sup_right
  -- c ≤ a ⊔ (b ⊔ c)
  trans b ⊔ c
  exact le_sup_right
  exact le_sup_right

  -- a ⊔ (b ⊔ c) ≤ a ⊔ b ⊔ c
  apply sup_le
  -- a ≤ a ⊔ b ⊔ c
  trans a ⊔ b
  exact le_sup_left
  exact le_sup_left
  apply sup_le
  -- b ≤ a ⊔ b ⊔ c
  trans a ⊔ b
  exact le_sup_right
  exact le_sup_left
  -- c ≤ a ⊔ b ⊔ c
  exact le_sup_right


example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := by
  -- Can be solved with `exact inf_le_inf_left a h`
  apply le_inf
  exact inf_le_left
  trans b
  exact inf_le_right
  exact h


-- `inf_le_inf_left`, proved above, is helpful here.
example : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by
  apply sup_le

-- use `sup_le_sup_left` for this one.
example : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry
