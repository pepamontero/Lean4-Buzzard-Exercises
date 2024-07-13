import Mathlib.Tactic

/-
TOPOLOGICAL SPACES 01
-/

/-
A topological space in Lean is a structure with 4 elements:
- `IsOpen : Set X → Prop`
& Proofs that IsOpen acually defines a topology
- `isOpen_univ`
- `isOpen_inter`
- `isOpen_sUnion`
-/

open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false

-- Discrete topology on any set X
example : TopologicalSpace X where
  IsOpen (s : Set X) := True
  isOpen_univ := by
    trivial
  isOpen_inter := by
    intro s t hs ht
    trivial
  isOpen_sUnion := by
    intro F hF
    trivial


-- Discrete topology on any set X
example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ

  isOpen_univ := by
    dsimp
    right
    rfl

  isOpen_inter := by
    intro s t hs ht
    cases' hs with hs hs
    · rw [hs]
      simp
    · cases' ht with ht ht
      · rw [ht]
        simp
      · rw [hs, ht]
        simp

  isOpen_sUnion := by
    intro F h
    -- do cases on whether Set.univ ∈ F
    have hF : Set.univ ∈ F ∨ Set.univ ∉ F
    exact Classical.em (Set.univ ∈ F)
    cases' hF with hF hF
    · right
      ext x
      constructor <;> intro hx
      · trivial
      · simp
        use Set.univ
    · left
      simp
      intro s hs
      specialize h s hs
      cases' h with h h
      · exact h
      · by_contra h1
        rw [h] at hs
        exact hF hs




-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  -- `exact isOpen_empty`


-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  sorry

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  sorry

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  sorry

-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
