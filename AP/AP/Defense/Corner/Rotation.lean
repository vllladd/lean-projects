import AP.AP.Defense.Corner.Basic

namespace AP.Corner

variable {c c₁ c₂ : Corner}

protected def rotRight (c : Corner) : Corner where
  dir := c.dir.rotRight
  offset := rotRight.ft c.offset

protected def rotLeft (c : Corner) : Corner where
  dir := c.dir.rotLeft
  offset := rotLeft.ft c.offset

protected def rot180 (c : Corner) : Corner where
  dir := c.dir⁻¹
  offset := rot180.ft c.offset

@[simp]
theorem rotRight_mk {dir offset} :
Corner.rotRight ⟨dir, offset⟩ = ⟨dir.rotRight, rotRight.ft offset⟩ := rfl

@[simp]
theorem rotLeft_mk {dir offset} :
Corner.rotLeft ⟨dir, offset⟩ = ⟨dir.rotLeft, rotLeft.ft offset⟩ := rfl

@[simp]
theorem rot180_mk {dir offset} :
Corner.rot180 ⟨dir, offset⟩ = ⟨dir⁻¹, rot180.ft offset⟩ := rfl

-- @[simp]
-- theorem rotRight_edge₁ : c.rotRight.edge₁ = c.edge₂ := by
--   rcases c with ⟨dir, offset⟩
--   cases dir <;> simp [edge₁, edge₂]
-- 
-- #check 0 #exit
-- 
-- @[simp]
-- theorem rotLeft_edge₂ : c.rotLeft.edge₂ = c.edge₁ := by
--   simp [rotLeft, edge₁, edge₂]
-- 
-- theorem false_of_f_edge₂_rotLeft_rotRight_eq_some {s p₁ p₂}
-- (H₁ : 6 ≤ c.offset.x) (H₂ : 6 ≤ c.offset.y)
-- (h₁ : c.rotLeft.edge₂.defense.f s = some p₁)
-- (h₂ : c.rotRight.edge₂.defense.f s = some p₂) : false := by
--   rcases c with ⟨dir, offset⟩; simp at h
--   simp [rotLeft, rotRight, edge₂] at h₁ h₂
--   replace h₁ := Edge.of_f_eq_some h₁
--   replace h₂ := Edge.of_f_eq_some h₂
--   simp at h₁ h₂; cases dir <;> simp [Edge.dist] at h₁ h₂ <;> omega
-- 
-- theorem compatible_rotRight (H₁ : 6 ≤ c.offset.x) (H₂ : 6 ≤ c.offset.y) :
-- c.defense.Compatible c.rotRight.defense := by
--   intro s₀ hs₀ s p₁ p₂ h₁ h₂ h₃ h₄ h₅
--   replace h₄ := of_f_eq_some h₄
--   replace h₅ := of_f_eq_some h₅
--   simp at h₅
--   have hs := sys.wf_of_reachable h₃
--   have H₁ := h₁.2.2
--   have H₂ := h₂.2.2
--   have H₃ := cnd'_of_reachable h₃ H₁
--   have H₄ := cnd'_of_reachable h₃ H₂
--   rcases h₄, h₅ with ⟨h₄ | h₄, h₅ | h₅⟩
--   · simp [f_edge₂_eq_none_of_f_edge₁_eq_some H₃ h₄] at h₅
--   · rw [←edge₂_rotLeft] at h₄
--     cases false_of_f_edge₂_rotLeft_rotRight_eq_some h h₄ h₅
--   · simp [h₄] at h₅; exact h₅
--   · rw [←edge₁_rotRight] at h₄
--     simp [f_edge₂_eq_none_of_f_edge₁_eq_some H₄ h₄] at h₅
-- 
-- @[simp]
-- theorem rotRight_rotRight : c.rotRight.rotRight = c.rot180 := by
--   simp [rotRight, rot180]
-- 
-- @[simp]
-- theorem rotLeft_rotLeft : c.rotLeft.rotLeft = c.rot180 := by
--   simp [rotLeft, rot180]; rfl
-- 
-- @[simp]
-- theorem edge₁_rot180 : c.rot180.edge₁ = c.edge₁.rot180 := by
--   simp [rot180, Edge.rot180, edge₁]
-- 
-- #check 0 #exit
-- 
-- theorem compatible_rot180 (H₁ : 6 ≤ c.offset.x) (H₂ : 6 ≤ c.offset.y) :
-- c.defense.Compatible c.rot180.defense := by
--   intro s₀ hs₀ s p₁ p₂ h₁ h₂ h₃ h₄ h₅
--   replace h₄ := of_f_eq_some h₄
--   replace h₅ := of_f_eq_some h₅
--   simp at h₅
--   have hs := sys.wf_of_reachable h₃
--   have H₁ := h₁.2.2
--   have H₂ := h₂.2.2
--   have H₃ := cnd'_of_reachable h₃ H₁
--   have H₄ := cnd'_of_reachable h₃ H₂
--   rcases h₄, h₅ with ⟨h₄ | h₄, h₅ | h₅⟩
--   ·
--     
--   · rw [←edge₂_rotLeft] at h₄
--     cases false_of_f_edge₂_rotLeft_rotRight_eq_some h h₄ h₅
--   ·
--     sorry
--   ·
--     sorry