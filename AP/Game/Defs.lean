import AP.System.Main

def Game.Tr (Pl : Type) (Tr : Pl → Type) : Type :=
  Σ (p : Pl), Tr p

@[ext]
structure Game.State (St Pl : Type) (Tr : Pl → Type) : Type where
  player : Pl
  state : St
  hist : List # Game.Tr Pl Tr

@[ext]
structure Game (Pl St Re : Type) (Sv Tr : Pl → Type)
(Tv : Pl → Pl → Type) [hd₁ : DecidableEq Pl] : Type where
  sys : System (Game.State St Pl Tr) (Game.Tr Pl Tr)
  
  fvs : (p : Pl) → St → Sv p
  fvt : (p : Pl) → Game.Tr Pl Tr → List (Game.Tr Pl Tr) → Tr p
  rules : (p : Pl) → St → Tr p → Option (Pl × St)
  
  h_tv_rfl : ∀ p, Tv p p = Tr p
  
  h_sys_tr : sys.tr = λ (s : Game.State St Pl Tr) (t : Game.Tr Pl Tr) =>
    if h : s.player ≠ t.1 then none else do
    let (p₁, s₁) ← rules s.player s.state # by simp at h; rw [h]; exact t.2
    some #
      { s with
        player := p₁
      , state := s₁
      , hist := t :: s.hist
      }

namespace Game

variable {Pl St Re Sv Tr Tv} [hd₁ : DecidableEq Pl] (game : Game Pl St Re Sv Tr Tv)