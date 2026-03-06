import Projects.AP.Determinacy

namespace AP

def mkSymFsAux (f : PointZ → PointZ) (s : State) : State where
  pw := s.pw
  taken := s.taken.map f
  aPos := f s.aPos
  aTurn := s.aTurn
  hist := s.hist.map f

def mkSymFs (ft : PointZ ≃ PointZ) : State ≃ State where
  toFun := mkSymFsAux ft
  invFun := mkSymFsAux ft.symm
  left_inv := by intro s; simp [mkSymFsAux]
  right_inv := by intro s; simp [mkSymFsAux]

def mkSym (ft : PointZ ≃ PointZ) : sys.Symmetry where
  ft := ft
  fs := mkSymFs ft

class BasicSym (sym : sys.Symmetry) extends System.Symmetry.WF sym where
  exi_mkSym : ∃ ft, mkSym ft = sym