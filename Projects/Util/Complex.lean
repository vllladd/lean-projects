import Projects.Util.Real

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Complex

noncomputable
def sqrt (x : ℂ) : ℂ :=
  x ^ (2⁻¹ : ℂ)

scoped prefix:max (priority := high) "√" => Complex.sqrt

def nnr (x : ℂ) : Prop :=
  0 ≤ x.re ∧ x.im = 0

@[simp]
theorem norm_mk {a b : ℝ} : ‖(⟨a, b⟩ : ℂ)‖ = (a ^ 2 + b ^ 2).sqrt := by
  simp [norm]; ring_nf

theorem sqrt_eq_iff_eq_sq_of_nnr {a b : ℂ} (h₁ : a.nnr) (h₂ : b.nnr) :
√a = b ↔ a = b ^ 2 := by
  rw [sqrt]
  rcases a, b with ⟨⟨a, x⟩, ⟨b, y⟩⟩
  rcases h₁, h₂ with ⟨⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩
  rw [pow_two]
  simp [Complex.ext_iff, cpow_inv_two_re, cpow_inv_two_im_eq_sqrt, Real.sqrt_sq h₁]
  rw [Real.sqrt_eq_iff_eq_sq h₁ h₂]
  ring_nf

theorem sqrt_re_of_nnr {a : ℂ} (h : a.nnr) : (√a).re = |a.re|.sqrt := by
  rcases a with ⟨a, b⟩; rcases h with ⟨h, rfl⟩
  simp only [sqrt, cpow_inv_two_re, norm_mk, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_sq h, add_self_div_two, abs_of_nonneg h]

theorem sqrt_im_of_nnr {a : ℂ} (h : a.nnr) : (√a).im = 0 := by
  rcases a with ⟨a, b⟩; rcases h with ⟨h, rfl⟩
  rw [sqrt, cpow_inv_two_im_eq_sqrt # by rfl]; simp [Real.sqrt_sq h]

theorem ofNat_eq {n : ℕ} : (OfNat.ofNat n : ℂ) = n := by
  iterate 2 cases n; simp; nm n; simp [Complex.ext_iff]; rw [Real.ofNat_eq]; simp

@[simp]
theorem nnr_nat {n : ℕ} : nnr ofNat(n) := by
  convert_to nnr n <;> simp [nnr, ofNat_eq]

@[simp]
theorem nnr_natCast {n : ℕ} : nnr n := by
  simp [nnr]

@[simp]
theorem sqrt_nat_re {n : ℕ} : (√ofNat(n)).re = Real.sqrt ofNat(n) := by
  rw [ofNat_eq, Real.ofNat_eq, sqrt_re_of_nnr # by simp]; simp

@[simp]
theorem sqrt_nat_im {n : ℕ} : (√ofNat(n)).im = 0 := by
  simp [ofNat_eq, sqrt_im_of_nnr]

theorem eq_of_re_eq_re {a b : ℂ} (h₁ : a.im = 0) (h₂ : b.im = 0) (h₃ : a.re = b.re) : a = b := by
  simp [Complex.ext_iff, h₁, h₂, h₃]

@[simp]
theorem sq_sqrt {a : ℂ} : √a ^ 2 = a := by
  simp [sqrt]

theorem nnr_of_sqrt_im_eq_zero {x : ℂ} (h : (√x).im = 0) : x.nnr := by
  rw [nnr]
  rw [sqrt] at h
  rw [cpow_def] at h
  split_ifs at h with h₁ h₂
  · simp at h₂
  · simp [h₁]
  rw [exp_im] at h
  simp at h
  rw [log_im] at h
  rw [←div_eq_mul_inv] at h
  by_cases h₂ : 0 ≤ x.arg
  · rw [Real.sin_half_eq_sqrt h₂ # by linarith [x.arg_le_pi]] at h
    simp at h
    rw [cos_arg h₁] at h
    simp at h₂
    by_cases h₃ : x.re / ‖x‖ ≤ 1
    · rw [Real.sqrt_eq_zero # by linarith] at h
      rw [sub_eq_zero] at h
      symm at h
      clear h₃
      field_simp at h
      simp at h
      simp [le_def] at h
      rcases h with ⟨h₃, h₄⟩
      use h₃, h₄.symm
    · push_neg at h₃
      clear h
      field_simp at h₃
      split_ands
      · apply le_of_lt h₃ |>.trans'
        simp
      by_contra h₄
      replace h₂ : 0 < x.im
      · exact lt_of_le_of_ne h₂ # λ h => h₄ h.symm
      clear h₄
      clear h₁
      rcases x with ⟨a, b⟩
      simp at h₂ h₃
      contrapose! h₃; clear h₃
      by_cases h₁ : a < 0
      · apply le_of_lt h₁ |>.trans
        simp
      push_neg at h₁
      rw [Real.le_sqrt] <;> try positivity
      simp
  · exfalso
    push_neg at h₂
    rw [Real.sin_half_eq_neg_sqrt _ # by linarith] at h
    rotate_left
    · linarith [x.neg_pi_lt_arg, Real.pi_pos]
    simp at h
    rw [cos_arg h₁] at h
    simp at h₂
    by_cases h₃ : x.re / ‖x‖ ≤ 1
    · rw [Real.sqrt_eq_zero # by linarith] at h
      field_simp at h₃
      field_simp at h
      simp [sub_eq_iff_eq_add] at h
      symm at h
      simp at h
      simp [le_def] at h
      linarith
    · push_neg at h₃
      field_simp at h₃
      clear h
      contrapose! h₃
      exact re_le_norm x

theorem sqrt_im_eq_zero_iff {x : ℂ} : (√x).im = 0 ↔ x.nnr :=
  ⟨λ h => nnr_of_sqrt_im_eq_zero h, λ h => sqrt_im_of_nnr h⟩

theorem nnr_add {a b : ℂ} (ha : a.nnr) (hb : b.nnr) : (a + b).nnr := by
  simp [nnr] at ha hb ⊢; constructor <;> linarith

theorem nnr_mul {a b : ℂ} (ha : a.nnr) (hb : b.nnr) : (a * b).nnr := by
  simp [nnr] at ha hb ⊢; constructor <;> nlinarith

theorem sqrt_mul_of_nnr {a b : ℂ} (ha : a.nnr) (hb : b.nnr) : √(a * b) = √a * √b := by
  apply eq_of_re_eq_re
  · rw [sqrt_im_eq_zero_iff]
    exact nnr_mul ha hb
  · simp [sqrt_re_of_nnr ha, sqrt_im_of_nnr ha, sqrt_re_of_nnr hb, sqrt_im_of_nnr hb]
  simp [sqrt_re_of_nnr ha, sqrt_im_of_nnr ha, sqrt_re_of_nnr hb, sqrt_im_of_nnr hb]
  rw [sqrt_re_of_nnr # nnr_mul ha hb]
  simp
  rcases a, b with ⟨⟨a, x⟩, ⟨b, y⟩⟩
  rcases ha, hb with ⟨⟨ha, rfl⟩, ⟨hb, rfl⟩⟩
  simp

theorem sqrt_sq_of_nnr {a : ℂ} (h : a.nnr) : √(a ^ 2) = a := by
  rw [pow_two, sqrt_mul_of_nnr h h]
  apply eq_of_re_eq_re _ h.2 <;> simp [sqrt_re_of_nnr h, sqrt_im_of_nnr h, h.1]

@[simp]
theorem sqrt_sq_nat {n : ℕ} : √(ofNat(n) ^ 2) = ofNat(n) := by
  simp_rw [ofNat_eq]
  apply sqrt_sq_of_nnr
  simp

attribute [simp] log_neg_one

@[simp]
theorem sqrt_neg_one : √(-1) = I := by
  simp [sqrt, cpow_def]; convert_to cexp (Real.pi / 2 * I) = _; ring_nf; simp