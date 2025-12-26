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

theorem exi_of_eventually {p : ℕ → Prop} (h : eventually p) : ∃ n, p n := by
  obtain ⟨n, h⟩ := h; use n, h _ # by rfl

theorem eventually_iff_exi_least {p : ℕ → Prop} : eventually p ↔
(∀ n, p n) ∨ ∃ N, ¬p N ∧ ∀ n, N < n → p n := by
  by_cases h₀ : ∀ n, p n
  · simp [h₀]; use 0; simpa
  simp [h₀]
  push_neg at h₀
  obtain ⟨n₀, h₀⟩ := h₀
  constructor
  · intro h
    use Nat.find! (λ N => ∀ n, N ≤ n → p n) - 1
    obtain ⟨h₁, h₂⟩ := Nat.find!_spec' h; clear h
    generalize Nat.find! (λ N => ∀ n, N ≤ n → p n) = m at h₁ h₂ ⊢
    constructor
    · cases m
      · simp
        specialize h₁ n₀
        simp [h₀] at h₁
      nm m
      simp
      intro h₃
      specialize h₂ m _
      · intro n hn
        rw [le_iff_eq_or_lt] at hn
        rcases hn with rfl | hn
        · exact h₃
        rw [←Nat.add_one_le_iff] at hn
        exact h₁ n hn
      linarith
    · intro n hn
      apply h₁
      omega
  · rintro ⟨N, h₁, h₂⟩
    use N + 1
    intro n hn
    apply h₂
    omega