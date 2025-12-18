import AP.RealAnalysis.ConditionalConvergence

namespace RealAnalysis

noncomputable
def altInv (n : ℕ) : ℝ :=
  (-1) ^ n * (n + 1 : ℝ)⁻¹

@[simp]
theorem altInv_zero : altInv 0 = 1 := by
  simp [altInv]

@[simp]
theorem altInv_one : altInv 1 = -2⁻¹ := by
  simp [altInv]; norm_num

-- #check 0 #exit

-- @[simp]
-- 
-- @[simp]
-- theorem converges_series_altInv : converges (series altInv) := by
--   
-- 
-- #check 0 #exit
-- 
-- @[simp]
-- theorem not_absConv_altInv : ¬AbsConv altInv := by
--   sorry
-- 
-- #check 0 #exit
-- 
-- @[simp]
-- theorem condConv_altInv : CondConv altInv :=
--   ⟨converges_series_altInv, not_absConv_altInv⟩