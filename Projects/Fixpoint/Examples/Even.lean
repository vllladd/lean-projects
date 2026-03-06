import Projects.Fixpoint.Induction
import Projects.Fixpoint.Coinduction

namespace Fixpoint.Examples

@[simp, scoped grind =]
def EvenAux (p : ℕ → Prop) (n : ℕ) : Prop :=
  n = 0 ∨ ∃ k, p k ∧ k + 2 = n

@[scoped grind =]
def Even' : ℕ → Prop :=
  IndPred EvenAux

@[simp, scoped grind ·]
theorem monotone_evenAux : Monotone EvenAux := by
  intro p₁ p₂ h n; simp; tauto

@[simp, scoped grind ·]
theorem even'_zero : Even' 0 := by
  apply IndPred.ctor <;> simp

@[scoped grind →]
theorem even'_add_two {n} (h : Even' n) : Even' (n + 2) := by
  apply IndPred.ctor <;> simp; exact h

@[scoped grind →]
theorem even'_cases {n} (h : Even' n) : n = 0 ∨ ∃ k, Even' k ∧ k + 2 = n :=
  h.cases' # by simp

theorem even'_ind {p : ℕ → Prop} {n} (h₁ : Even' n)
(h₂ : p 0) (h₃ : ∀ n, Even' n → p n → p (n + 2)) : p n := by
  apply h₁.ind (by simp); simp [IndPredAndFn]; rw [←Even']; grind

theorem even'_eq_even : Even' = Even := by
  ext n; constructor <;> intro h; apply even'_ind h <;> grind
  rw [Nat.even_iff_exi] at h; obtain ⟨n, rfl⟩ := h; induction n <;> grind