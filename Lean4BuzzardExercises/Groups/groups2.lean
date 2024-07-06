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


/-

If you want to take this further: prove that if we make
a new class `BadGroup` by replacing
`one_mul` by `mul_one` in the definition of `weak_group`
then it is no longer true that you can prove `mul_inv_self`;
there are structures which satisfy `mul_assoc`, `mul_one`
and `inv_mul_self` but which really are not groups.
Can you find an example? Try it on paper first.

-/
-- claim: not a group in general
class BadGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

-- `Bool` is a type with two terms, `Bool.true` and `Bool.false`. See if you can make it into
-- a bad group which isn't a group!
instance : One Bool :=
  ⟨sorry⟩

instance : Mul Bool :=
  ⟨sorry⟩

instance : Inv Bool :=
  ⟨sorry⟩

instance : BadGroup Bool where
  mul_assoc := sorry
  -- `decide`, might be able to do this
  mul_one := sorry
  -- decide
  inv_mul_self := sorry
  -- decide

example : ¬∀ a : Bool, 1 * a = a := by sorry
-- decide
