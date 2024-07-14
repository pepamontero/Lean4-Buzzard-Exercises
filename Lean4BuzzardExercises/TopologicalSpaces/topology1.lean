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



example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  -- `exact isOpen_empty`
  have h1 : ∅ = ⋃₀ ∅
  simp
  rw [h1]
  apply isOpen_sUnion
  intro t ht
  by_contra
  exact ht


-- Topological space of ℝ
#synth TopologicalSpace ℝ


def Real.IsOpen (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s


lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  intro x hx
  use 1
  constructor
  norm_num
  intro y hy
  trivial

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  specialize hs x hx.left
  specialize ht x hx.right
  cases' hs with δ1 hδ1
  cases' ht with δ2 hδ2
  use min δ1 δ2
  constructor
  · exact lt_min hδ1.left hδ2.left
  · intro y hy
    cases' hy with hy1 hy2
    constructor
    · apply hδ1.right
      have h1 : min δ1 δ2 ≤ δ1
      exact min_le_left δ1 δ2
      constructor
      <;> linarith
    · apply hδ2.right
      have h2 : min δ1 δ2 ≤ δ2
      exact min_le_right δ1 δ2
      constructor
      <;> linarith


lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  cases' hx with s hs

  have hs' : IsOpen s
  apply hF
  exact hs.left

  specialize hs' x hs.right
  cases' hs' with δ hδ
  cases' hδ with h1 h2
  use δ
  constructor
  · exact h1
  · intro y hy
    specialize h2 y hy
    simp
    use s
    constructor
    exact hs.left
    exact h2


example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
