import Mathlib.Tactic -- imports all the Lean tactics

/-
GROUPS 01
Introduction to groups in Lean
-/

variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
  inv_mul_self g

example (a b c : G) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

example (a : G) : a * 1 = a := by
  exact LeftCancelMonoid.mul_one a

example (a : G) : 1 * a = a := by
  exact LeftCancelMonoid.one_mul a

example (a : G) : a * a⁻¹ = 1 := by
  exact mul_inv_self a

variable (a b c : G)

example : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc]
  rw [inv_mul_self]
  exact LeftCancelMonoid.one_mul b

example : a * (a⁻¹ * b) = b := by
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
  constructor <;> intro h

  rw [← LeftCancelMonoid.mul_one (a⁻¹)]
  rw [← h]
  rw [← mul_assoc]
  rw [inv_mul_self]
  exact LeftCancelMonoid.one_mul b

  rw [← h]
  exact mul_inv_self a


example : (1 : G)⁻¹ = 1 := by
  rw [← LeftCancelMonoid.mul_one (1⁻¹)]
  exact inv_mul_self 1

example : a⁻¹⁻¹ = a := by
  rw [← LeftCancelMonoid.mul_one (a⁻¹⁻¹)]
  rw [← inv_mul_self a]
  rw [← mul_assoc]
  rw [inv_mul_self]
  exact LeftCancelMonoid.one_mul a

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry


/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above; a theorem of Knuth and Bendix
says that these examples and the axioms of a group give a "confluent rewrite system"
which can solve any identity in group theory. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `exact?` or by
educated guessing).

-/
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by group

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  sorry
