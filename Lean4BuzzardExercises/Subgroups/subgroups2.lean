import Mathlib.Tactic

/-
SUBGROUPS 02
Introduction to group homomorphisms
Kernel, Image, Image of a subgroup, Preimage of a subgroup
-/


variable {G H : Type} [Group G] [Group H]

-- Notation for group homomorphism : →*
variable (φ : G →* H)

variable (a : G)

example : H :=
  φ a

-- Main properties of group homomorphisms
example (a b : G) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b

example : φ 1 = 1 :=
  φ.map_one

example (a : G) : φ a⁻¹ = (φ a)⁻¹ :=
  φ.map_inv a

-- The identity group homomorphism from `G` to `G` is called `monoid_hom.id G`
example : MonoidHom.id G a = a := by rfl

variable (K : Type) [Group K]
variable (ψ : H →* K)

-- The composite of ψ and φ can't be written `ψ ∘ φ` in Lean
-- we use dot notation instead
example : G →* K :=
  ψ.comp φ

theorem comp_id : φ.comp (MonoidHom.id G) = φ := by
  rfl

theorem id_comp : (MonoidHom.id H).comp φ = φ := by
  rfl

theorem comp_assoc {L : Type} [Group L] (ρ : K →* L) :
    (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) := by
  rfl

/-
KERNEL OF A GROUP HOMOM
`φ.ker = {x | φ x = 1}`
-/

example (φ : G →* H) : Subgroup G :=
  φ.ker

example (φ : G →* H) (x : G) : x ∈ φ.ker ↔ φ x = 1 := by
  rfl

/-
IMGAGE (RANGE) OF A GROUP HOMOM
`φ.range = {y : H | ∃ x : G, φ x = y}`
-/
example (φ : G →* H) : Subgroup H :=
  φ.range

example (φ : G →* H) (y : H) : y ∈ φ.range ↔ ∃ x : G, φ x = y := by
  rfl

/-
IMAGE OR A SUBGROUP BY A HOMOM
`S.map φ = φ(S) = {y : H | ∃ x : G, x ∈ S ∧ φ x = y} `
-/
example (φ : G →* H) (S : Subgroup G) : Subgroup H :=
  S.map φ

example (φ : G →* H) (S : Subgroup G) (y : H) : y ∈ S.map φ ↔ ∃ x, x ∈ S ∧ φ x = y := by
  rfl

/-
PREIMAGE OF A SUBGROUP BY A HOMOM
`T.comap φ = φ⁻¹(T) = {x : G | φ x ∈ T}`
-/
example (φ : G →* H) (S : Subgroup H) : Subgroup G :=
  S.comap φ

example (φ : G →* H) (T : Subgroup H) (x : G) : x ∈ T.comap φ ↔ φ x ∈ T := by
  rfl


-- RESULTS ABOUT THESE DEFINITIONS

example (S : Subgroup G) : S.comap (MonoidHom.id G) = S := by
  rfl


example (S : Subgroup G) : S.map (MonoidHom.id G) = S := by
  ext x
  constructor <;> intro h

  cases' h with y hy
  simp at hy
  rw [← hy.right]
  exact hy.left

  use x
  constructor
  exact h
  rfl


example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : S.comap φ ≤ T.comap φ := by
  intro x h
  apply hST
  exact h


example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : S.map φ ≤ T.map φ := by
  intro x h
  cases' h with y hy
  use y
  constructor
  apply hST
  exact hy.left
  exact hy.right


example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : U.comap (ψ.comp φ) = (U.comap ψ).comap φ := by
  ext x
  constructor
  <;> intro h
  <;> exact h


example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : S.map (ψ.comp φ) = (S.map φ).map ψ := by
  ext x
  constructor
  <;> intro h

  cases' h with y hy
  simp
  use y
  exact hy

  cases' h with y hy
  simp
  cases' hy with hy1 hy2
  cases' hy1 with z hz
  use z
  constructor
  exact hz.left
  rw [hz.right]
  exact hy2
