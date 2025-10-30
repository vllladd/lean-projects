import AP.AP.Defense.Edge.Symmetry.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def translate (e : Edge) (offset : PointZ) : Edge where
  dir := e.dir
  offset := e.offset + if e.hor then offset.y else offset.x