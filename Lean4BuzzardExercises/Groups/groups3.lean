import Mathlib.Tactic

/-
GROUPS 03
Subgroups and group homomorphisms
-/

-- SUBGROUPS --

variable (G : Type) [Group G]

variable (H : Subgroup G)


example (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  exact H.mul_mem ha hb

example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * b⁻¹ * 1 * (a * c) ∈ H := by
  apply H.mul_mem
  all_goals apply H.mul_mem
  apply H.mul_mem
  exact ha
  rw [H.inv_mem_iff]
  exact hb
  exact H.one_mem
  exact ha
  exact hc

example (H K : Subgroup G) : Subgroup G :=
  H ⊓ K

example (H K : Subgroup G) (a : G) : a ∈ H ⊓ K ↔ a ∈ H ∧ a ∈ K := by
  rfl

-- Note that `a ∈ H ⊔ K ↔ a ∈ H ∨ a ∈ K` is not true; only `←` is true.
-- Take apart the `Or` and use `exact?` to find the relevant lemmas.
example (H K : Subgroup G) (a : G) : a ∈ H ∨ a ∈ K → a ∈ H ⊔ K := by
  intro h
  cases' h with h h
  exact Subgroup.mem_sup_left h
  exact Subgroup.mem_sup_right h



-- GROUP HOMOMORPHISMS --

variable (G H : Type) [Group G] [Group H]

variable (φ : G →* H)

example (a b : G) : φ (a * b) = φ a * φ b := φ.map_mul a b

example (a : G) : φ (a⁻¹) = (φ a)⁻¹ := φ.map_inv a

example : φ 1 = 1 := φ.map_one

example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  rw [φ.map_mul, φ.map_mul, φ.map_inv, φ.map_one]

example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  ext x
  apply h
