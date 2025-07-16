import AP.System.Main

universe u

structure GameParams : Type (u + 1) where
  Player : Type u
  State : Type u
  Move : Player → Type u
  PState : Player → Type u
  PMove : Player → Player → Type u
  Outcome : Type u

  h_inh_move : ∀ p, Inhabited # Move p
  h_pl_fin : Fintype Player  
  h_pl_lin : LinearOrder Player
  h_out_lin : LinearOrder Outcome
  h_move_rfl : ∀ p, PMove p p = Move p

instance {T : GameParams} : Fintype T.Player :=
  T.h_pl_fin

instance {T : GameParams} : LinearOrder T.Player :=
  T.h_pl_lin

instance {T : GameParams} : LinearOrder T.Outcome :=
  T.h_out_lin

def GameParams.Trans (T : GameParams) : Type u :=
  Σ (p : T.Player), T.Move p

def GameParams.PTrans (T : GameParams) (p : T.Player) : Type u :=
  Σ (p' : T.Player), T.PMove p p'

def GameParams.GRules (T : GameParams) : Type u :=
  (p : T.Player) → T.State → T.Move p → Option (T.Player × T.State)

abbrev GameParams.Hist (T : GameParams) : Type u :=
  DMap T.Player # λ p => List (T.PTrans p)

@[ext]
structure GameParams.GState (T : GameParams) : Type u where
  player : T.Player
  state : T.State
  hist : T.Hist

def GameParams.initState (T : GameParams)
(p : T.Player) (s : T.State) : T.GState :=
  { player := p
  , state := s
  , hist := DMap.range # λ _ => []
  }

def GameParams.GPMove (T : GameParams) : Type u :=
  (p : T.Player) → T.GState → T.Trans → T.PTrans p

def GameParams.updateHist (T : GameParams) (pmove : T.GPMove)
(s : T.GState) (t : T.Move s.player) : T.Hist :=
  s.hist.map # @λ p ts => pmove p s ⟨s.player, t⟩ :: ts

def GameParams.sys_tr (T : GameParams) (rules : T.GRules) (pmove : T.GPMove)
(s : T.GState) (t : T.Trans) : Option T.GState :=
  if h : s.player = t.1 then do
    let (p₁, s₁) ← rules t.1 s.state t.2
    some #
      { player := p₁
      , state := s₁
      , hist := T.updateHist pmove s # h ▸ t.2
      }
  else none

@[ext]
structure Game (T : GameParams) : Type u where
  sys : System T.GState T.Trans
  
  rules : T.GRules
  pstate : (p : T.Player) → T.State → T.PState p
  pmove : T.GPMove
  outcome : T.GState ⊕ (ℕ → T.GState) → T.Player → T.Outcome
  
  h_sys_init_nemp : sys.initial ≠ ∅
  h_sys_init_valid : ∀ s ∈ sys.initial, ∃ p s', s = T.initState p s'
  h_sys_tr : sys.tr = T.sys_tr rules pmove

namespace Game

variable {T : GameParams.{u}} (game : Game T)

def updateHist (s : T.GState) (t : T.Trans) : T.Hist :=
  if h : s.player = t.1
  then T.updateHist game.pmove s # h ▸ t.2
  else s.hist

structure Strat (s₀ : T.GState) (p : T.Player) : Type u where
  f : T.PState p → List (T.PTrans p) → T.Move p
  h : ∀ (s : T.GState), s.player = p → game.sys.has_tr s → game.sys.valid_tr s
    ⟨p, f (game.pstate p s.state) (s.hist.get! p)⟩