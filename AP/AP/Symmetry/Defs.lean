import AP.AP.Determinacy

namespace AP

def symFnState (f : PointZ → PointZ) (s : State) : State where
  pw := s.pw
  taken := s.taken.map f
  aPos := f s.aPos
  aTurn := s.aTurn
  hist := s.hist.map f

#check 0 #exit

def mkSym (f f' : PointZ → PointZ) (h₁ : Inverse f f') : sys.Symmetry where
  fs := symFnState f
  fs' := symFnState f'
  ft := f
  ft' := f'
  wf :=
    { h_fs := by
        simp
    }