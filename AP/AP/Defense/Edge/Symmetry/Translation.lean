import AP.AP.Defense.Edge.Symmetry.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def translate (e : Edge) (offset : PointZ) : Edge where
  dir := e.dir
  offset := e.offset + if e.hor then offset.y else offset.x

@[simp]
theorem points_translate {offset} :
(e.translate offset).points = (translate offset).ft '' e.points := by
  ext p
  simp [translate, Edge.translate, points, memPoints, Dir.vert]
  by_contra h
  cases hd : e.dir
  all_goals revert h; simp [hd]

@[simp] theorem dir_translate {offset} : (e.translate offset).dir = e.dir := rfl

@[simp]
theorem offset_translate {offset} :
(e.translate offset).offset = e.offset + if e.hor then offset.y else offset.x := rfl

@[simp]
theorem dist_translate {offset p} :
(e.translate offset).dist p = e.dist (translate offset |>.ft' p) := by
  simp [translate, Edge.translate, dist]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd] <;> ring_nf

-- @[simp]
-- theorem getBorderPoint_translate_of_down {offset p d} [H : Fact # e.dir = .down] :
-- (e.translate offset).getBorderPoint p d = e.getBorderPoint p d + ⟨0, offset.y⟩ := by
--   simp [getBorderPoint]
-- 
-- @[simp]
-- theorem getBorderPoint₀_translate_of_down {offset p} [H : Fact # e.dir = .down] :
-- (e.translate offset).getBorderPoint₀ p = e.getBorderPoint₀ p + ⟨0, offset.y⟩ := by
--   simp [getBorderPoint₀]
-- 
-- @[simp]
-- theorem getBorderPoints_translate_of_down {offset p d} [H : Fact # e.dir = .down] :
-- (e.translate offset).getBorderPoints p d = (e.getBorderPoints p d).map (· + ⟨0, offset.y⟩) := by
--   simp [getBorderPoints]