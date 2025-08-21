import AP.AP.Defense

namespace AP

class Edge (ps : Set PointZ) : Prop where
  h : ∃ (a₁ a₂ : Bool) (i : ℤ), ∀ p, p ∈ ps ↔ (a₂ ↔ ite a₁ p.x p.y ≤ i)

theorem Edge.def {ps} : Edge ps ↔ ∃ (a₁ a₂ : Bool) (i : ℤ),
∀ p, p ∈ ps ↔ (a₂ ↔ ite a₁ p.x p.y ≤ i) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

instance {y} : Edge {p | y ≤ p.y} := by
  constructor; use false, false, y - 1; simp [Int.sub_one_lt_iff]

instance {x} : Edge {p | x ≤ p.x} := by
  constructor; use true, false, x - 1; simp [Int.sub_one_lt_iff]

instance {y} : Edge {p | p.y < y} := by
  constructor; use false, true, y - 1; simp [Int.le_sub_one_iff]

instance {x} : Edge {p | p.x < x} := by
  constructor; use true, true, x - 1; simp [Int.le_sub_one_iff]

instance {y} : Edge {p | y < p.y} := by
  constructor; use false, false, y; simp

instance {x} : Edge {p | x < p.x} := by
  constructor; use true, false, x; simp

instance {y} : Edge {p | p.y ≤ y} := by
  constructor; use false, true, y; simp

instance {x} : Edge {p | p.x ≤ x} := by
  constructor; use true, true, x; simp