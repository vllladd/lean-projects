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

@[simp]
theorem edge₁_rotRight [h : c.Square] : c.rotRight.edge₁ = c.edge₂ := by
  simp [edge₁, edge₂]; rcases c with ⟨dir, ⟨x, y⟩⟩
  simp at h ⊢; cases dir <;> simp [square_iff_offset_x_eq] at h ⊢ <;> omega

@[simp]
theorem edge₂_rotLeft [h : c.Square] : c.rotLeft.edge₂ = c.edge₁ := by
  simp [edge₁, edge₂]; rcases c with ⟨dir, ⟨x, y⟩⟩
  simp at h ⊢; cases dir <;> simp [square_iff_offset_x_eq] at h ⊢ <;> omega

theorem false_of_f_edge₁_rotLeft_rotRight_eq_some {s p₁ p₂} [h : c.SquareGe 6]
(h₁ : c.rotLeft.edge₁.defense.f s = some p₁)
(h₂ : c.rotRight.edge₁.defense.f s = some p₂) : False := by
  rcases c with ⟨dir, offset⟩
  cases h; nm h₃ h₄
  simp [square_iff, rotLeft, rotRight, edge₁, edge₂, Point.zero_def] at h₁ h₂ h₃ h₄
  replace h₁ := Edge.of_f_eq_some h₁
  replace h₂ := Edge.of_f_eq_some h₂
  simp at h₁ h₂ h₃ h₄; cases dir <;> simp [Edge.dist] at h₁ h₂ h₃ h₄ <;> omega

theorem false_of_f_edge₂_rotLeft_rotRight_eq_some {s p₁ p₂} [h : c.SquareGe 6]
(h₁ : c.rotLeft.edge₂.defense.f s = some p₁)
(h₂ : c.rotRight.edge₂.defense.f s = some p₂) : False := by
  rcases c with ⟨dir, offset⟩
  cases h; nm h₃ h₄
  simp [square_iff, rotLeft, rotRight, edge₁, edge₂, Point.zero_def] at h₁ h₂ h₃ h₄
  replace h₁ := Edge.of_f_eq_some h₁
  replace h₂ := Edge.of_f_eq_some h₂
  simp at h₁ h₂ h₃ h₄; cases dir <;> simp [Edge.dist] at h₁ h₂ h₃ h₄ <;> omega

theorem compatible_rotRight [h : c.SquareGe 6] : c.defense.Compatible c.rotRight.defense := by
  intro s₀ hs₀ s p₁ p₂ h₀ h₁ h₂ h₃ h₄ h₅
  replace h₄ := of_f_eq_some h₄
  replace h₅ := of_f_eq_some h₅
  simp at h₅
  have hs := sys.wf_of_reachable h₃
  have H₁ := h₁.2.2
  have H₂ := h₂.2.2
  have H₃ := cnd'_of_reachable h₃ H₁
  have H₄ := cnd'_of_reachable h₃ H₂
  rcases h₄, h₅ with ⟨h₄ | h₄, h₅ | h₅⟩
  · simp [f_edge₂_eq_none_of_f_edge₁_eq_some H₃ h₄] at h₅
  · rw [←edge₂_rotLeft] at h₄
    cases false_of_f_edge₂_rotLeft_rotRight_eq_some h₄ h₅
  · simp [h₄] at h₅; exact h₅
  · rw [←edge₁_rotRight] at h₄
    simp [f_edge₂_eq_none_of_f_edge₁_eq_some H₄ h₄] at h₅

@[simp]
theorem rotRight_rotRight : c.rotRight.rotRight = c.rot180 := by
  simp [Corner.rotRight, Corner.rot180]; rfl

@[simp]
theorem rotLeft_rotLeft : c.rotLeft.rotLeft = c.rot180 := by
  simp [Corner.rotLeft, Corner.rot180, Dir.inv_def]; rfl

@[simp]
theorem rotLeft_rotRight : c.rotRight.rotLeft = c := by
  simp [Corner.rotLeft, Corner.rotRight, rotRight]

@[simp]
theorem rotRight_rotLeft : c.rotLeft.rotRight = c := by
  simp [Corner.rotLeft, Corner.rotRight, rotRight]

@[simp]
theorem edge₁_rot180 : c.rot180.edge₁ = c.edge₁.rot180 := by
  simp [Corner.rot180, Edge.rot180, edge₁]
  rw [rot180, pow_two]
  simp [-rotRight_mul_rotRight, rotRight]
  cases c.dir <;> simp

@[simp]
theorem edge₂_rot180 : c.rot180.edge₂ = c.edge₂.rot180 := by
  simp [Corner.rot180, Edge.rot180, edge₂]
  rw [rot180, pow_two]
  simp [-rotRight_mul_rotRight, rotRight]
  cases c.dir <;> simp

@[simp]
instance [h : c.Square] : c.rotRight.Square := by
  simp [square_iff]
  simp [edge₂, Edge.dist, Corner.rotRight, Point.zero_def]
  cases c.dir <;> simp

@[simp]
instance [h : c.Square] : c.rotLeft.Square := by
  simp [square_iff]
  simp [edge₁, Edge.dist, Corner.rotLeft, Point.zero_def]
  cases c.dir <;> simp

@[simp]
instance [h : c.Square] : c.rot180.Square := by
  simp [square_iff]
  simp [edge₁, edge₂, Edge.dist, Edge.rot180, Point.zero_def]
  have h₁ := square_iff_offset_x_eq.mp h
  revert h₁; cases c.dir <;> simp <;> omega

@[simp]
instance {d} [h : c.SquareGe d] : c.rotRight.SquareGe d := by
  cases h; nm h₁ h₂; constructor; revert h₂
  simp [edge₁, Edge.dist, Corner.rotRight, Point.zero_def]
  cases c.dir <;> simp

@[simp]
instance {d} [h : c.SquareGe d] : c.rotLeft.SquareGe d := by
  cases h; nm h₁ h₂; constructor; revert h₂
  simp [edge₁, Edge.dist, Corner.rotLeft, Point.zero_def]
  cases c.dir <;> simp

@[simp]
instance {d} [h : c.SquareGe d] : c.rot180.SquareGe d := by
  cases h; nm h₁ h₂; constructor; revert h₂
  simp [edge₁, Edge.dist, Corner.rot180, Point.zero_def]
  cases c.dir <;> simp

theorem compatible_rotLeft [h : c.SquareGe 6] : c.defense.Compatible c.rotLeft.defense := by
  conv_lhs => rw [←c.rotRight_rotLeft];; symm; apply compatible_rotRight

@[simp]
theorem edge₁_rotLeft : c.rotLeft.edge₁ = c.edge₁.rotLeft := by
  simp [edge₁, Corner.rotLeft, Edge.rotLeft]; cases c.dir <;> simp

@[simp]
theorem edge₂_rotRight : c.rotRight.edge₂ = c.edge₂.rotRight := by
  simp [edge₂, Corner.rotRight, Edge.rotRight]; cases c.dir <;> simp

-- #check 0 #exit

-- theorem compatible_rot180 [h : c.SquareGe 6] :
-- c.defense.Compatible c.rot180.defense := by
--   intro s₀ hs₀ s p₁ p₂ h₀ h₁ h₂ h₃ h₄ h₅
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
--     sorry
--   ·
--     exfalso
--     rw [←edge₂_rotLeft] at h₄
--     rw [←Edge.rotLeft_rotLeft, rotLeft_edge₂, ←edge₁_rotLeft] at h₅
--     apply false_of_edge₁_edge₂_eq_some _ h₅ h₄
--     sorry
--   ·
--     rw [←edge₁_rotRight] at h₄
--     sorry
--   ·
--     sorry