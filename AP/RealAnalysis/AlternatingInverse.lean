import AP.RealAnalysis.ConditionalConvergence

namespace RealAnalysis

noncomputable
def altInv (n : ℕ) : ℝ :=
  (-1) ^ n * (n + 1 : ℝ)⁻¹

-----

@[simp]
theorem altInv_zero : altInv 0 = 1 := by
  simp [altInv]

@[simp]
theorem altInv_one : altInv 1 = -2⁻¹ := by
  simp [altInv]; norm_num

theorem tendsTo_zero_iff_abs_tendsTo {a} : tendsTo a 0 ↔ tendsTo |a| 0 := by
  constructor
  · nth_rw 2 [←abs_zero]; exact tendsTo_abs
  · exact tendsTo_zero_of_abs_tendsTo

@[simp]
theorem abs_altInv {n} : |altInv n| = (n + 1 : ℝ)⁻¹ := by
  simp [altInv]; norm_cast; simp

@[simp]
theorem altInv_tendsTo_zero : tendsTo altInv 0 := by
  apply tendsTo_zero_of_abs_tendsTo; simp

@[simp]
theorem converges_altInv : converges altInv :=
  ⟨_, altInv_tendsTo_zero⟩

@[simp]
theorem converges_series_altInv : converges (series altInv) := by
  apply converges_series_alternating_of_monoGe _ # by simp
  intro i j h; simp; field_simp; norm_cast; omega

@[simp]
theorem not_converges_series_inv : ¬converges (series (λ n => (n + 1 : ℝ)⁻¹)) := by
  rintro ⟨L, h⟩
  sorry

-- #check 0 #exit

@[simp]
theorem not_absConv_altInv : ¬AbsConv altInv := by
  simp [AbsConv]

@[simp]
theorem condConv_altInv : CondConv altInv :=
  ⟨converges_series_altInv, not_absConv_altInv⟩