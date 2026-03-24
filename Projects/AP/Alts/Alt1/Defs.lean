import Projects.AP.FreshA

namespace AP.Alt₁

@[ext]
structure Point : Type where
  x : ℤ
  y : ℤ
deriving Nonempty

def center : Point := ⟨0, 0⟩

def dist (p₁ p₂ : Point) : ℕ :=
  max |p₁.x - p₂.x| |p₁.y - p₂.y| |>.toNat

@[ext]
structure Board : Type where
  squares : Set Point
  A : Point

def board₀ : Board :=
  ⟨Set.univ, center⟩

abbrev AMove : Type := Point
abbrev DMove : Type := Option Point

def AMoveValid (pw : ℕ) (b : Board) (p : AMove) : Prop :=
  p ≠ b.A ∧ dist p b.A ≤ pw ∧ p ∈ b.squares

def DMoveValid (b : Board) : DMove → Prop
  | .none => true
  | .some p => p ≠ b.A ∧ p ∈ b.squares

structure ValidAMove (pw : ℕ) (b : Board) : Type where
  m : AMove
  h : AMoveValid pw b m

structure ValidDMove (b : Board) : Type where
  m : DMove
  h : DMoveValid b m

def AHasValidMove (pw : ℕ) (b : Board) : Prop :=
  ∃ (m : AMove), AMoveValid pw b m

@[ext]
structure State : Type where
  board : Board
  history : List Board
  act : Prop

def initState (b : Board) : State where
  board := b
  history := []
  act := True

def state₀ : State :=
  initState board₀

def State.finish (s : State) : State :=
  {s with act := False}

structure A (pw : ℕ) : Type where
  f : Π (s : State), s.act → AHasValidMove pw s.board → ValidAMove pw s.board

structure D : Type where
  f : Π (s : State), s.act → ValidDMove s.board

def applyMove (s : State) (b : Board) : State :=
  {s with board := b, history := s.history ++ [s.board]}

def applyAMoveB (b : Board) (m : AMove) : Board :=
  {b with A := m}

def applyDMoveB (b : Board) : DMove → Board
| .none => b
| .some p => {b with squares := b.squares \ {p}}

def applyAMove (s : State) (m : AMove) : State :=
  applyMove s # applyAMoveB s.board m

def applyDMove (s : State) (m : DMove) : State :=
  applyMove s # applyDMoveB s.board m

@[ext]
structure Game (pw : ℕ) : Type where
  a : A pw
  d : D
  s : State

def init_game {pw : ℕ} (a : A pw) (d : D) (s : State) : Game pw where
  a := a
  d := d
  s := s

def Game.act {pw : ℕ} (g : Game pw) : Prop :=
  g.s.act

def Game.setState {pw : ℕ} (g : Game pw) (s₁ : State) : Game pw :=
  {g with s := s₁}

def Game.finish {pw : ℕ} (g : Game pw) : Game pw :=
  g.setState g.s.finish

def playAMoveAt' {pw pw₁ : ℕ} (a₁ : A pw₁) (g : Game pw)
(hs : g.s.act) (h : AHasValidMove pw₁ g.s.board) : Game pw :=
  g.setState # applyAMove g.s # a₁.f g.s hs h |>.m

open Classical in noncomputable
def playAMoveAt {pw : ℕ} (g : Game pw) : Game pw :=
  if h : g.act ∧ AHasValidMove pw g.s.board
  then playAMoveAt' g.a g h.1 h.2
  else g.finish

def playDMoveAt {pw : ℕ} (g : Game pw) (hs : g.s.act) : Game pw :=
  g.setState # applyDMove g.s # g.d.f g.s hs |>.m

open Classical in noncomputable
def Game.playMove {pw : ℕ} (g : Game pw) : Game pw :=
  if hs : g.act
  then playAMoveAt # playDMoveAt g hs
  else g

noncomputable
def Game.play {pw : ℕ} (g : Game pw) (n : ℕ) : Game pw :=
  Game.playMove^[n] g

def Game.AWins {pw : ℕ} (g : Game pw) : Prop :=
  ∀ (n : ℕ), (g.play n).act

def AHwsAt (pw : ℕ) (s : State) : Prop :=
  ∃ (a : A pw), ∀ (d : D), init_game a d s |>.AWins

def AHws (pw : ℕ) : Prop :=
  AHwsAt pw state₀