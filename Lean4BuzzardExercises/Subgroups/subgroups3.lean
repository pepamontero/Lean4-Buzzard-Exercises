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

/-
Technical remark: this would not be the case if quotient groups were *defined* to
be cosets. In Lean quotient groups are an *opaque definition*. What do I mean by this?
You probably learnt in algebra that if G is a group and H is a normal subgroup then the
quotient G⧸H has elements which are *equal* to cosets of H. In Lean this is not true.
A term of the quotient type G⧸H cannot be taken apart with `cases` because it is not *equal* to
a coset. But the universal property `QuotientGroup.lift` is all we need; we don't
need to worry about the underlying definition of the quotient.
Example. Let's use `QuotientGroup.lift` to define the following map. Say `φ : G →* H` is a
group hom and we have normal subgroups `N : Subgroup G` and `P : Subgroup H` such that `φ N ≤ P`.
Then the induced map `G →* H ⧸ P` has `N` in the kernel, so it "lifts" to a group hom
`ρ : G ⧸ N →* H ⧸ P` with the property that for all `x : G`,
`ρ (QuotientGroup.mk' N x) = QuotientGroup.mk' P (φ x)`. Let's define `ρ` and prove
this equality.
-/
variable {G H φ N}
variable {P : Subgroup H} [P.Normal]

def ρ (h : N.map φ ≤ P) : G ⧸ N →* H ⧸ P :=
  lift N ((mk' P).comp φ) (by
    -- we are using `lift` so we need to supply the proof that `(mk' P).comp φ` kills `N`
    intro n hn

  )

-- Now let's prove that `ρ ∘ mk' N = mk' P ∘ φ`
/-
    G ----φ----> H
    |            |
    |            |
   mk'           mk'
    |            |
    \/           \/
  G ⧸ N --ρ--> H ⧸ P
-/

example (h : N.map φ ≤ P) (x : G) : ρ h (mk' N x) = mk' P (φ x) := by
  -- this proof does my head in
  rfl
