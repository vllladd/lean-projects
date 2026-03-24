import Projects.AP.FreshA
import Projects.AP.Alts.Alt1.Defs

namespace AP.Alt₁

def Point.toAlt : Point → PointZ
| ⟨x, y⟩ => ⟨x, y⟩

def Point.ofAlt : PointZ → Point
| ⟨x, y⟩ => ⟨x, y⟩

def Board.ofAlt (s : AP.State) : Board where
  squares := Set.univ \ s.taken.toSet.image .ofAlt
  A := .ofAlt s.aPos

noncomputable
def State.toAlt (s : State) (pw : ℕ) (hist : List PointZ) : AP.State where
  pw := pw
  taken := Set'.ofSet # Set.univ \ s.board.squares |>.image (·.toAlt)
  aPos := s.board.A.toAlt
  aTurn := Odd s.history.length
  hist := hist

def State.ofAlt (s : AP.State) (act : Prop) (hist : List Board) : State where
  board := Board.ofAlt s
  history := hist
  act := act

def State.setHist (s : State) (hist : List Board) : State :=
  {s with history := hist}

def State.finSq (s : State) : Prop :=
  Set.univ \ s.board.squares |>.Finite