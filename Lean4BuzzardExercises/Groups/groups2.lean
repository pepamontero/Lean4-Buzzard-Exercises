import Mathlib.Tactic

/-
GROUPS 02
-/

/-
We consider the class WeakGroup with the following properties
It lacks two properties compared to Groups (1 * a = a, a * a⁻¹ = 1)
-/
class WeakGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

namespace WeakGroup

variable {G : Type} [WeakGroup G] (a b c : G)

theorem mul_left_cancel (h : a * b = a * c) : b = c := by
  rw [← one_mul b]
  rw [← inv_mul_self a]
  rw [mul_assoc]
  rw [h]
  rw [← mul_assoc]
  rw [inv_mul_self]
  rw [one_mul]

theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by
  apply mul_left_cancel (a⁻¹)
  rw [← mul_assoc]
  rw [inv_mul_self]
  rw [one_mul]
  exact h

theorem mul_one (a : G) : a * 1 = a := by
  apply mul_left_cancel (a⁻¹)
  rw [← mul_assoc]
  rw [inv_mul_self]
  rw [one_mul]

theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  apply mul_left_cancel (a⁻¹)
  rw [← mul_assoc]
  rw [inv_mul_self]
  rw [one_mul]
  rw [mul_one]

end WeakGroup


-- new definition Bad Group. We want to prove that not all bad groups are groups
class BadGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1


instance : One Bool :=
  ⟨Bool.true⟩

instance : Mul Bool :=
  ⟨fun x _ ↦ x⟩

instance : Inv Bool :=
  ⟨fun _ ↦ Bool.true⟩

instance : BadGroup Bool where
  mul_assoc := by
    -- `decide`, or:
    intro a b c
    cases' a <;> cases' b <;> cases' c
    all_goals trivial
  mul_one := by
    -- `decide`, or:
    intro a
    cases' a
    all_goals trivial
  inv_mul_self := by
    -- `decide`, or:
    intro a
    cases' a
    all_goals trivial

example : ¬∀ a : Bool, 1 * a = a := by
  -- `decide`, or:
  by_contra h
  specialize h Bool.false
  exact (Bool.eq_not_self (1 * false)).mp h
