import Mathlib.Tactic -- imports all the Lean tactics

/-
GROUPS 01
Introduction to groups in Lean
-/

variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
  inv_mul_self g

example (a b c : G) : a * b * c = a * (b * c) := by
  -- Note: can be solved by `group`
  exact mul_assoc a b c

example (a : G) : a * 1 = a := by
  -- Note: can be solved by `group`
  exact LeftCancelMonoid.mul_one a

example (a : G) : 1 * a = a := by
  -- Note: can be solved by `group`
  exact LeftCancelMonoid.one_mul a

example (a : G) : a * a⁻¹ = 1 := by
  -- Note: can be solved by `group`
  exact mul_inv_self a

variable (a b c : G)

example : a⁻¹ * (a * b) = b := by
  -- Note: can be solved by `exact inv_mul_cancel_left a b`
  -- Note: can be solved by `group`
  rw [← mul_assoc]
  rw [inv_mul_self]
  exact LeftCancelMonoid.one_mul b

example : a * (a⁻¹ * b) = b := by
  -- Note: can be solved by `exact mul_inv_cancel_left a b`
  -- Note: can be solved by `group`
  rw [← mul_assoc]
  rw [mul_inv_self]
  exact LeftCancelMonoid.one_mul b

example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  rw [← LeftCancelMonoid.mul_one (b * a)] at h1
  rw [← mul_inv_self c] at h1
  rw [mul_assoc] at h1
  rw [← mul_assoc a c (c⁻¹)] at h1
  rw [h2] at h1
  rw [LeftCancelMonoid.one_mul] at h1

  have h : b * c⁻¹ * c = c * c⁻¹ * c
  exact mul_right_cancel_iff.mpr h1

  rw [mul_assoc] at h
  rw [inv_mul_self c] at h
  rw [LeftCancelMonoid.mul_one] at h
  rw [mul_inv_self c] at h
  rw [LeftCancelMonoid.one_mul] at h

  exact h


example : a * b = 1 ↔ a⁻¹ = b := by
  -- Note: can be solved by `exact mul_eq_one_iff_inv_eq`
  constructor <;> intro h

  rw [← LeftCancelMonoid.mul_one (a⁻¹)]
  rw [← h]
  rw [← mul_assoc]
  rw [inv_mul_self]
  exact LeftCancelMonoid.one_mul b

  rw [← h]
  exact mul_inv_self a


example : (1 : G)⁻¹ = 1 := by
  -- Note: can be solved by `exact inv_one`
  -- Note: can be solved by `group`
  rw [← LeftCancelMonoid.mul_one (1⁻¹)]
  exact inv_mul_self 1

example : a⁻¹⁻¹ = a := by
  -- Note: can be solved by `exact DivisionMonoid.inv_inv a`
  -- Note: can be solved by `group`
  rw [← LeftCancelMonoid.mul_one (a⁻¹⁻¹)]
  rw [← inv_mul_self a]
  rw [← mul_assoc]
  rw [inv_mul_self]
  exact LeftCancelMonoid.one_mul a


example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- Note: can be solved by `group`
  exact DivisionMonoid.mul_inv_rev a b


example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by
  group

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  intro e g

  rw [← LeftCancelMonoid.mul_one (e * g)]
  rw []
