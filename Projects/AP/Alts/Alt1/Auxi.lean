import Projects.AP.Util
import Projects.AP.Alts.Alt1.Defs

namespace AP.Alt₁

def Point.toAlt : Point → PointZ
| ⟨x, y⟩ => ⟨x, y⟩

def Point.ofAlt : PointZ → Point
| ⟨x, y⟩ => ⟨x, y⟩

def State.aTurn (s : State) : Bool :=
  Odd # s.history.length

def Board.ofAlt (s : AP.State) : Board where
  squares := Set.univ \ s.taken.toSet.image .ofAlt
  A := .ofAlt s.aPos

open Classical in noncomputable
def Board.toAlt (b : Board) (pw : ℕ) (aTurn : Bool) (hist : List PointZ) : AP.State where
  pw := pw
  taken := Set'.ofSet # Set.univ \ b.squares |>.image (·.toAlt)
  aPos := b.A.toAlt
  aTurn := aTurn
  hist := hist

open Classical in noncomputable
def State.toAlt (s : State) (pw : ℕ) (hist : List PointZ) : AP.State :=
  s.board.toAlt pw s.aTurn hist

def State.ofAlt (s : AP.State) (act : Prop) (hist : List Board) : State where
  board := Board.ofAlt s
  history := hist
  act := act

open Classical in noncomputable
def Board.toAltH? (b : Board) (pw : ℕ) (aTurn : Bool) : Option AP.State :=
  choose? λ s' => sys.WF s' ∧ b.toAlt pw aTurn s'.hist = s'

open Classical in noncomputable
def State.toAltH? (s : State) (pw : ℕ) : Option AP.State :=
  s.board.toAltH? pw s.aTurn

open Classical in noncomputable
def Board.toAltH (b : Board) (pw : ℕ) (aTurn : Bool) : AP.State :=
  b.toAltH? pw aTurn |>.getd

open Classical in noncomputable
def State.toAltH (s : State) (pw : ℕ) : AP.State :=
  s.toAltH? pw |>.getd

def State.setHist (s : State) (hist : List Board) : State :=
  {s with history := hist}

def State.FinSq (s : State) : Prop :=
  Set.univ \ s.board.squares |>.Finite

def ASeekCnd (pw : ℕ) (r : State → State → Prop)
(s : State) (m : ValidAMove pw s.board) : Prop :=
  r s # applyAMove s m.m

def DSeekCnd (r : State → State → Prop)
(s : State) (m : ValidDMove s.board) : Prop :=
  r s # applyDMove s m.m

open Classical in noncomputable
def aSeek (pw : ℕ) (r : State → State → Prop) : Option (A pw) :=
  choose? λ a => ∀ s h₁ h₂, (∃ m, ASeekCnd pw r s m) → ASeekCnd pw r s (a.f s h₁ h₂)

open Classical in noncomputable
def dSeek (r : State → State → Prop) : Option D :=
  choose? λ d => ∀ s h₁, (∃ m, DSeekCnd r s m) → DSeekCnd r s (d.f s h₁)

def Board.aHws (b : Board) (pw : ℕ) (aTurn : Bool) : Prop :=
  b.toAltH pw aTurn |>.aHws

def Board.dHws (b : Board) (pw : ℕ) (aTurn : Bool) : Prop :=
  b.toAltH pw aTurn |>.dHws

def State.aHws (s : State) (pw : ℕ) : Prop :=
  s.board.aHws pw s.aTurn

def State.dHws (s : State) (pw : ℕ) : Prop :=
  s.board.dHws pw s.aTurn

open Classical in noncomputable
def Board.dwn (b : Board) (pw : ℕ) (aTurn : Bool) : ℕ :=
  b.toAltH pw aTurn |>.dwn

open Classical in noncomputable
def State.dwn (s : State) (pw : ℕ) : ℕ :=
  s.board.dwn pw s.aTurn

open Classical in noncomputable
def aOptimal (pw : ℕ) : Option (A pw) :=
  aSeek pw λ _ s' => s'.aHws pw

open Classical in noncomputable
def dOptimal (pw : ℕ) : Option D :=
  dSeek λ s s' => s'.dHws pw ∧ s'.dwn pw < s.dwn pw

class State.WF (s : State) (pw : ℕ) : Prop where
  h : ∃ a d n g, (initGame a d state₀ : Game pw).play n = g ∧
    (g.s = s ∨ ∃ h, (playDMoveAt g h).s = s)

open Classical in noncomputable
def A.set {pw} (a : A pw) (s : State) (ref : A pw) : A pw where
  f s₁ h₁ h₂ := if s₁ = s then ref.f s₁ h₁ h₂ else a.f s₁ h₁ h₂

open Classical in noncomputable
def D.set (d : D) (s : State) (ref : D) : D where
  f s₁ h := if s₁ = s then ref.f s₁ h else d.f s₁ h