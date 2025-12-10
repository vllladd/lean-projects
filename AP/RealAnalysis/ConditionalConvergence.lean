import AP.RealAnalysis.Subsequence

namespace RealAnalysis

def CondConv (a : ℕ → ℝ) : Prop :=
  converges (series a) ∧ ¬AbsConv a

-----

theorem condConv_drop_of {a N} (h : CondConv a) : CondConv (a # N + ·) := by
  unfold CondConv at h ⊢; rwa [converges_series_drop_iff, absConv_drop_iff]

theorem condConv_drop_iff {a N} : CondConv (a # N + ·) ↔ CondConv a := by
  unfold CondConv; rw [converges_series_drop_iff, absConv_drop_iff]

theorem condConv_neg {a} : CondConv (-a) ↔ CondConv a := by
  unfold CondConv; rw [←neg_series', converges_neg, absConv_neg]

namespace CondConv

variable {a : ℕ → ℝ} (H : CondConv a)
include H

theorem converges_series : converges (series a) := H.1
theorem not_absConv : ¬AbsConv a := H.2

theorem infp_pos : Infp a (0 < ·) := by
  intro N
  by_contra! h₃
  generalize hb : (a # N + ·) = b
  have h₄ : CondConv b; rwa [←hb, condConv_drop_iff]
  have h₅ : |b| = -b
  · subst hb
    rw [abs_of_nonpos]
    intro n
    apply h₃
    simp
  have h₆ := h₄.1
  have h₇ : ¬converges (series b)
  · rw [←converges_neg, neg_series', ←h₅]; exact h₄.2
  contradiction

theorem infp_neg : Infp a (· < 0) := by
  intro N; rw [←condConv_neg] at H
  have h₁ := infp_pos H N
  simp at h₁; exact h₁

theorem infp_nonneg : Infp a (0 ≤ ·) := by
  apply infp_of_imp (infp_pos H); intro n; apply le_of_lt

theorem infp_nonpos : Infp a (· ≤ 0) := by
  apply infp_of_imp (infp_neg H); intro n; apply le_of_lt