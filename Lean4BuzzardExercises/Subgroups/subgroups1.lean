import Mathlib.Tactic

/-
SUBGROUPS 01
Introduction to subgroups in Lean
Complete lattices
Conjugate subgroup
-/


variable (G : Type) [Group G] (a b : G) (H K : Subgroup G)

-- Basic properties for Subgroup H
example : (1 : G) ∈ H :=
  one_mem H

example (ha : a ∈ H) : a⁻¹ ∈ H :=
  inv_mem ha

example (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  mul_mem ha hb


example (ha : a ∈ H) (hb : b ∈ H) : a * b⁻¹ ∈ H := by
  exact mul_mem ha (by exact inv_mem hb)


example : a⁻¹ ∈ H ↔ a ∈ H := by
  -- Can be solved by `exact inv_mem_iff`
  constructor <;> intro h
  rw [← inv_inv a]
  all_goals exact inv_mem h


example (ha : a ∈ H) : a * b ∈ H ↔ b ∈ H := by
  -- Can be solved by `exact H.mul_mem_cancel_left ha`
  constructor <;> intro h

  have hb : a⁻¹ * (a * b) ∈ H
  exact mul_mem (by exact inv_mem ha) h
  group at hb
  exact hb

  exact mul_mem ha h


/-
Subgroups form a complete lattice.
-/
example : CompleteLattice (Subgroup G) := by
  infer_instance -- means "find this construction in the database"

/-
Main properties of smallest and largest soubgroups of G
-/
example : a ∈ (⊥ : Subgroup G) ↔ a = 1 :=
  Subgroup.mem_bot

example : a ∈ (⊤ : Subgroup G) :=
  Subgroup.mem_top a


/-
CONJUGATE SUBGROUP
We want to show that the conjugate `xHx⁻¹ = {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}`
is a subgroup of G
-/

variable {G H} {x : G}

variable {y z : G}

theorem conjugate.one_mem : (1 : G) ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  use 1
  constructor
  exact H.one_mem
  group

theorem conjugate.inv_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
    y⁻¹ ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  cases' hy with h hh
  use h⁻¹
  constructor
  exact H.inv_mem hh.left
  rw [← inv_inv x]
  rw [← mul_inv_rev h x⁻¹]
  rw [inv_inv x]
  rw [← mul_inv_rev]
  rw [← mul_assoc]
  rw [inv_inj]
  exact hh.right


theorem conjugate.mul_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹})
    (hz : z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
    y * z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  cases' hy with h1 hh1
  cases' hz with h2 hh2
  use h1 * h2
  constructor
  exact H.mul_mem hh1.left hh2.left
  rw [hh1.right, hh2.right]
  group


def conjugate (H : Subgroup G) (x : G) : Subgroup G
    where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := conjugate.one_mem
  inv_mem' := conjugate.inv_mem
  mul_mem' := conjugate.mul_mem

-- RESULTS ABOUT CONJUGATES

theorem mem_conjugate_iff : a ∈ conjugate H x ↔ ∃ h, h ∈ H ∧ a = x * h * x⁻¹ := by
  rfl

theorem conjugate_mono (H K : Subgroup G) (h : H ≤ K) : conjugate H x ≤ conjugate K x := by
  intro y hy
  rw [mem_conjugate_iff] at *
  cases' hy with g hg
  use g
  constructor
  apply h
  exact hg.left
  exact hg.right

theorem conjugate_bot : conjugate ⊥ x = ⊥ := by
  ext y
  constructor
  <;> rw [mem_conjugate_iff]
  <;> intro h

  cases' h with g hg
  rw [Subgroup.mem_bot] at *
  rw [hg.right]
  rw [hg.left]
  group

  rw [Subgroup.mem_bot] at h
  use 1
  constructor
  rw [Subgroup.mem_bot]
  group
  exact h


theorem conjugate_top : conjugate ⊤ x = ⊤ := by
  ext y
  constructor
  <;> rw [mem_conjugate_iff]
  <;> intro

  apply Subgroup.mem_top

  use x⁻¹ * y * x
  constructor
  apply Subgroup.mem_top
  group

theorem conjugate_eq_of_abelian (habelian : ∀ a b : G, a * b = b * a) : conjugate H x = H := by
  ext y
  constructor
  <;> rw [mem_conjugate_iff]
  <;> intro h

  cases' h with g hg
  rw [hg.right, habelian]
  group
  exact hg.left

  use y
  constructor
  exact h
  rw [habelian]
  group
