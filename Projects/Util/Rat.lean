import Projects.Util.Real

namespace Rat

theorem inv_lt_self_of_one_lt {x : ℚ} (h : 1 < x) : x⁻¹ < x := by
  replace h : (1 : ℝ) < x; exact_mod_cast h
  exact_mod_cast Real.inv_lt_self_of_one_lt h

theorem inv_le_self_of_one_le {x : ℚ} (h : 1 ≤ x) : x⁻¹ ≤ x := by
  replace h : (1 : ℝ) ≤ x; exact_mod_cast h
  exact_mod_cast Real.inv_le_self_of_one_le h

theorem lt_inv_self_of {x : ℚ} (h₁ : 0 < x) (h₂ : x < 1) : x < x⁻¹ := by
  replace h₁ : (0 : ℝ) < x; exact_mod_cast h₁
  replace h₂ : (x : ℝ) < 1; exact_mod_cast h₂
  exact_mod_cast Real.lt_inv_self_of h₁ h₂

theorem le_inv_self_of {x : ℚ} (h₁ : 0 < x) (h₂ : x ≤ 1) : x ≤ x⁻¹ := by
  replace h₁ : (0 : ℝ) < x; exact_mod_cast h₁
  replace h₂ : (x : ℝ) ≤ 1; exact_mod_cast h₂
  exact_mod_cast Real.le_inv_self_of h₁ h₂