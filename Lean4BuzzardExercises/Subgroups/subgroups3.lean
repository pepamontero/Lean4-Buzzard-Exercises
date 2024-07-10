import Mathlib.Tactic

/-
SUBGROUPS 03
Quotient groups
-/


variable (G : Type) [Group G] (N : Subgroup G) [Subgroup.Normal N]

example : Type :=
  G ⧸ N

-- The quotient has a group structure
example : Group (G ⧸ N) := by
  infer_instance

example : G →* G ⧸ N :=
  QuotientGroup.mk' N -- without ' it's a function, not group homom.

-- Properties of the `QuotientGroup.mk'`

open QuotientGroup

example : Function.Surjective (mk' N) :=
  mk'_surjective N


example (x y : G) : mk' N x = mk' N y ↔ ∃ n ∈ N, x * n = y :=
  mk'_eq_mk' N


-- Exercise

example : (mk' N).ker = N := by
  -- Can be solved by `exact ker_mk' N`
  ext x
  constructor <;> intro h

  simp at h
  exact h

  simp
  exact h

/-
UNIVERSAL PROPERTY: let
- `φ : G →* H` group homom.
- `N ⊆ ker φ`
Then
`∃ ψ : G ⧸ N →* H` such that `ψ ∘ (QuotientGroup.mk' N)` = `φ`

This is `QuotientGroup.lift N φ h`, where `h` is a proof of `∀ x, x ∈ N → φ x = 1`
-/

variable (H : Type) [Group H] (φ : G →* H) (h : ∀ x, x ∈ N → φ x = 1)

example : G ⧸ N →* H :=
  lift N φ h

example (x : G) : (lift N φ h) ((mk' N) x) = φ x := by
  rfl


variable {G H φ N}
variable {P : Subgroup H} [P.Normal]

def ρ (h : N.map φ ≤ P) : G ⧸ N →* H ⧸ P :=
  lift N ((mk' P).comp φ) (by
    intro n hn

    have h1 : (mk' P).comp φ n = 1
    simp
    apply h
    simp
    use n

    exact h1
  )

example (h : N.map φ ≤ P) (x : G) : ρ h (mk' N x) = mk' P (φ x) := by
  rfl
