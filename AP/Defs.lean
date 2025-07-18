import AP.Game.Main
import AP.Point

open Util.Data

namespace AP

inductive Player where
| A : Player
| D : Player

open Player

@[ext]
structure State where
  pw : ℕ
  taken : Util.Data.Set Point
  a_pos : Point
  hist : List Point
  turn : Player

def init_state (pw : ℕ) : State :=
  { pw := pw
  , taken := ∅
  , a_pos := ⟨0, 0⟩
  , hist := []
  , turn := D
  }

@[simp]
abbrev State.a_valid_move (s : State) (p : Point) : Prop :=
  p ∉ s.taken ∧ p ≠ s.a_pos ∧ p.dist s.a_pos ≤ s.pw

@[simp]
abbrev State.d_valid_move (s : State) (p : Point) : Prop :=
  p ∉ s.taken ∧ p ≠ s.a_pos

def State.a_move (s : State) (p : Point) : Option State :=
  if s.a_valid_move p
  then some {s with a_pos := p, hist := p :: s.hist, turn := D}
  else none

def State.d_move (s : State) (p : Point) : Option State :=
  if s.d_valid_move p
  then some {s with taken := insert p s.taken, hist := p :: s.hist, turn := A}
  else none

def State.tr_fn (s : State) (p : Point) : Option State :=
match s.turn with
| A => s.a_move p
| D => s.d_move p

def Rules : System State Point :=
  { initial := Set.range init_state
  , tr := State.tr_fn
  }

def State.a_has_move (s : State) : Prop :=
  ∃ p, s.a_valid_move p

structure AStrat where
  fa : State → Point
  ha : ∀ (s : State), s.turn = A → s.a_has_move → Rules.validTr s (fa s)

structure DStrat where
  fd : State → Point
  hd : ∀ (s : State), s.turn = D → Rules.validTr s (fd s)

structure Game extends AStrat, DStrat

def Game.fn (g : Game) (s : State) : Point :=
match s.turn with
| A => g.fa s
| D => g.fd s

def Game.play (g : Game) (s : State) (n : ℕ) : State × ℕ :=
  Rules.simulate g.fn s n

noncomputable
def Game.winner_at (g : Game) (s : State) : Player :=
  by classical exact
  if ∀ n, (g.play s n).2 = 0 then A else D

def State.a_hws (s : State) : Prop :=
  ∃ a, ∀ d, (Game.mk a d).winner_at s = A

def State.d_hws (s : State) : Prop :=
  ∃ d, ∀ a, (Game.mk a d).winner_at s = D

def a_hws (pw : ℕ) : Prop :=
  (init_state pw).a_hws