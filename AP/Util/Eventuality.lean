import AP.Util.Nat

def eventually (p : ℕ → Prop) : Prop :=
  ∃ N, ∀ n, N ≤ n → p n

theorem eventually_and {p q : ℕ → Prop} :
eventually (λ n => p n ∧ q n) ↔ eventually p ∧ eventually q := by
  constructor
  · refine λ ⟨N, h⟩ => ⟨⟨N, ?_⟩, N, ?_⟩ <;> intros <;> simp_all only
  · rintro ⟨⟨N₁, h₁⟩, N₂, h₂⟩; use max N₁ N₂
    intro n hn; constructor <;> simp_all only [sup_le_iff]

@[simp]
theorem not_eventually_even : ¬eventually Even := by
  unfold eventually; push_neg; simp
  intro N; use N * 2 + 1; simp; linarith

@[simp]
theorem not_eventually_odd : ¬eventually Odd := by
  unfold eventually; push_neg; simp
  intro N; use N * 2; simp

theorem eventually_or_of {p q : ℕ → Prop}
(h : eventually p ∨ eventually q) : eventually (λ n => p n ∨ q n) := by
  rcases h with ⟨N, h⟩ | ⟨N, h⟩ <;> use N <;> intro n hn <;> simp_all

@[simp]
theorem eventually_const {P : Prop} : eventually (λ _ => P) ↔ P :=
  ⟨λ ⟨N, h⟩ => h N # le_refl _, λ h => ⟨0, λ _ _ => h⟩⟩