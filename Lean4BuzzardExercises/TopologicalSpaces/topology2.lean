import Mathlib.Tactic

/-
TOPOLOGY 02
Continuous functions in topological spaces
-/

example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  exact continuous_def


example (X Y : Type) [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x' : X, dist x' x < δ → dist (f x') (f x) < ε := by
  exact Metric.continuous_iff

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- can be solved by `continuity`
  -- can be solved by `exact Continuous.comp hg hf`

  rw [continuous_def] at *
  intro s hs
  specialize hg s hs
  specialize hf (g ⁻¹' s) (by exact hg)

  have h : (g ∘ f ⁻¹' s) = (f ⁻¹' (g ⁻¹' s))
  rfl

  rw [h]
  exact hf
