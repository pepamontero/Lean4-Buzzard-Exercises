import Mathlib.Tactic

/-
ORDERINGS 04
Complete lattices
-/

variable (L : Type) [CompleteLattice L] (a : L)

/- We use the following properties of CompleteLattice L:
- `le_sSup : a ∈ S → a ≤ Sup S`
- `sSup_le : (∀ (b : L), b ∈ S → b ≤ a) → sSup S ≤ a`
And the definition
- `sSup_empty : Sup ∅ = ⊥` (bot)

The equivalent properties for Inf are:
- `sInf_le : a ∈ S → Inf S ≤ a`
- `le_sInf : (∀ (b : L), b ∈ S → a ≤ b) → a ≤ Inf S`
- `sInf_empty : Inf ∅ = ⊤` (top)
-/

example : ⊥ ≤ a := by
  -- Can be solved by `exact bot_le`
  rw [← sSup_empty]
  apply sSup_le
  intro b hb
  by_contra
  exact hb


example : a ≤ ⊥ ↔ a = ⊥ := by
  -- Can be solved by `exact le_bot_iff`
  constructor <;> intro h
  apply le_antisymm h (by exact bot_le)

  rw [← sSup_empty] at *
  exact le_of_eq h


example (S T : Set L) : S ⊆ T → sSup S ≤ sSup T := by
  -- Can be solved by `exact sSup_le_sSup`
  intro h
  apply sSup_le
  intro b hb
  apply le_sSup
  apply h
  exact hb
