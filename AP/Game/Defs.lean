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
  h_pl_lin : LinearOrder Player
  h_out_lin : LinearOrder Outcome
  h_move_rfl : ∀ p, PMove p p = Move p

def GameParams.Trans (T : GameParams) : Type u :=
  Σ (p : T.Player), T.Move p

def GameParams.PTrans (T : GameParams) (p : T.Player) : Type u :=
  Σ (p' : T.Player), T.PMove p p'

def GameParams.Rules (T : GameParams) : Type u :=
  (p : T.Player) → T.State → T.Move p → Option (T.Player × T.State)

@[ext]
structure GameParams.GState (T : GameParams) : Type u where
  player : T.Player
  state : T.State
  hist : List T.Trans

def GameParams.initState (T : GameParams)
(p : T.Player) (s : T.State) : T.GState :=
  { player := p
  , state := s
  , hist := []
  }

def GameParams.sys_tr (T : GameParams) (rules : T.Rules)
(s : T.GState) (t : T.Trans) : Option T.GState := by
  haveI := T.h_pl_lin
  exact if h : s.player ≠ t.1 then none else do
  let (p₁, s₁) ← rules t.1 s.state t.2
  some #
    { player := p₁
    , state := s₁
    , hist := t :: s.hist
    }

@[ext]
structure Game (T : GameParams) : Type u where
  sys : System T.GState T.Trans
  
  rules : T.Rules
  pstate : (p : T.Player) → T.State → T.PState p
  pmove : (p : T.Player) → T.GState → (t : T.Trans) → List T.Trans → T.PTrans p
  outcome : T.GState ⊕ (ℕ → T.GState) → T.Player → T.Outcome
  
  h_sys_initial : sys.initial ≠ ∅
  h_sys_tr : sys.tr = T.sys_tr rules

namespace Game

variable {T : GameParams.{u}} (game : Game T)

def getPMoves' (game : Game T) (s₀ : T.GState) (p : T.Player)
(acc : List (T.PTrans p)) : List T.Trans → List (T.PTrans p)
| [] => acc
| (t :: ts) => game.getPMoves' s₀ p (game.pmove p s₀ t ts :: acc) ts

def getPMoves (s₀ : T.GState) (p : T.Player)
(ts : List T.Trans) : List (T.PTrans p) :=
  (game.getPMoves' s₀ p [] ts).reverse

structure Strat (s₀ : T.GState) (p : T.Player) : Type u where
  f : T.PState p → List (T.PTrans p) → T.Move p
  h : ∀ (s : T.GState), s.player = p → game.sys.has_tr s → game.sys.valid_tr s
    ⟨p, f (game.pstate p s.state) (game.getPMoves s₀ p s.hist)⟩