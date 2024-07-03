import Mathlib.Tactic

/-
LOGIC 06
Working with "or"
Introducing tactic cases
-/

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intros h1 h2 h3
  cases' h1 with hP hQ
  apply h2
  exact hP
  apply h3
  exact hQ

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases' h with hP hQ
  right
  exact hP
  left
  exact hQ

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor

  -- =>
  intro h
  cases' h with hPQ hR
  cases' hPQ with hP hQ
  left
  exact hP
  right
  left
  exact hQ
  right
  right
  exact hR

  -- <=
  intro h
  cases' h with hP hQR
  left
  left
  exact hP
  cases' hQR with hQ hR
  left
  right
  exact hQ
  right
  exact hR

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intros h1 h2 h3
  cases' h3 with hP hQ
  left
  apply h1
  exact hP
  right
  apply h2
  exact hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  intros h1 h2
  cases' h2 with hP hR
  left
  apply h1
  exact hP
  right
  exact hR

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intros h1 h2
  constructor

  intro h3
  cases' h3 with hP hQ
  rw [← h1]
  left
  exact hP
  rw [← h2]
  right
  exact hQ

  intro h3
  cases' h3 with hR hS
  rw [h1]
  left
  exact hR
  rw [h2]
  right
  exact hS

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h
  constructor
  by_contra hP
  apply h
  left
  exact hP
  by_contra hQ
  apply h
  right
  exact hQ

  intro h
  by_contra hPQ
  cases' hPQ with hP hQ
  apply h.left
  exact hP
  apply h.right
  exact hQ

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor

  intro h
  by_contra h1
  apply h
  constructor
  by_contra hNP
  apply h1
  left
  exact hNP
  by_contra hNQ
  apply h1
  right
  exact hNQ

  intro h
  by_contra h1
  cases' h with hNP hNQ
  apply hNP
  exact h1.left
  apply hNQ
  exact h1.right
