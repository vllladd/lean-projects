import AP.Analysis.Limit

namespace RealAnalysis

def continuousAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ y, |y - x| < δ → |f y - f x| < ε

def continuous (f : ℝ → ℝ) : Prop :=
  ∀ x, continuousAt f x

theorem tendsTo_apply_of_continuousAt {a f L}
(h₁ : tendsTo a L) (h₂ : continuousAt f L) : tendsTo (f # a ·) (f L) := by
  intro e he; specialize h₂ e he; obtain ⟨d, hd, h₂⟩ := h₂
  specialize h₁ d hd; obtain ⟨N, h₁⟩ := h₁; have h₄ := h₁ N # by rfl
  have h₃ := h₂ _ h₄; use N; intro n hn; exact h₂ _ # h₁ n hn

noncomputable
def log' (b x : ℝ) : ℝ :=
  x.log / b.log

theorem continuousAt_log {x : ℝ} (hx : 0 < x) : continuousAt (·.log) x := by
  intro e he
  dsimp
  use min e x, by positivity
  intro y h₁
  have hy : 0 < y
  · contrapose! h₁; calc
    _ ≤ x := by simp
    _ ≤ |x - y| := by rw [abs_of_pos] <;> linarith
    _ = _ := by apply abs_sub_comm
  -- rw [←Real.log_div] <;> try positivity
  -- rw [abs_lt] at hy ⊢
  -- rcases hy with ⟨h₂, h₃⟩
  sorry