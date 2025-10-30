import AP.AP.Defense.Edge.Symmetry.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def flipV (e : Edge) : Edge where
  dir := if e.hor then e.dir⁻¹ else e.dir
  offset := if e.hor then -e.offset else e.offset