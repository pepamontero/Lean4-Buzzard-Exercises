import Mathlib.Tactic

/-
BIJECTIONS 03
Bijection as an equivalence relation
-/

-- `Equiv.refl`
example (X : Type) : X ≃ X :=
  { toFun := fun x ↦ x
    invFun := fun y ↦ y
    left_inv := by
      intro x
      simp
    right_inv := by
      intro y
      simp
      }

-- `Equiv.symm`
example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.invFun
    invFun := e.toFun
    left_inv := by
      exact e.right_inv
    right_inv := by
      exact e.left_inv
      }
-- =
-- `Equiv.symm` (this is more correct)
example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.symm
    invFun := e
    left_inv := e.right_inv
    right_inv := e.left_inv }
-- =
example (X Y : Type) (e : X ≃ Y) : Y ≃ X := Equiv.symm e

-- `Equiv.trans`
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  { toFun := fun x => eYZ (eXY x)
    invFun := fun z => eXY.symm (eYZ.symm z)
    left_inv := by
      intro x
      simp
    right_inv := by
      intro y
      simp
  }
-- =
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  Equiv.trans eXY eYZ
-- =
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  eXY.trans eYZ


-- Exercises

example (A B X : Type) (eAX : A ≃ X) (eBX : B ≃ X) : A ≃ B :=
  eAX.trans (id eBX.symm)


def R (X Y : Type) : Prop :=
  ∃ _ : X ≃ Y, True

example : Equivalence R := by
  constructor
  · intro X
    use Equiv.refl X

  · intro X Y h
    cases' h with eXY _
    use Equiv.symm eXY

  · intro X Y Z hXY hYZ
    cases' hXY with eXY _
    cases' hYZ with eYZ _
    use Equiv.trans eXY eYZ
