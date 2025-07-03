import AP.System.Main

structure GameParams.{u} : Type (u + 1) where
  Pl : Type u
  St : Type u
  Re : Type u
  Sv : Pl → Type u
  Tr : Pl → Type u
  Tv : Pl → Pl → Type u
  
  h_pl : LinearOrder Pl
  h_re : LinearOrder Re
  h_tv_rfl : ∀ p, Tv p p = Tr p

def GameTr.{u} (T : GameParams.{u}) : Type u :=
  Σ (p : T.Pl), T.Tr p

@[ext]
structure GameState.{u} (T : GameParams.{u}) : Type u where
  player : T.Pl
  state : T.St
  hist : List # GameTr T

@[ext]
structure Game.{u} (T : GameParams.{u}) : Type u where
  sys : System (GameState T) (GameTr T)
  
  fvs : (p : T.Pl) → T.St → T.Sv p
  fvt : (p : T.Pl) → GameTr T → List (GameTr T) → T.Tr p
  rules : (p : T.Pl) → T.St → T.Tr p → Option (T.Pl × T.St)
  
  h_sys_tr : sys.tr = λ (s : GameState T) (t : GameTr T) => by
    haveI := T.h_pl
    exact if h : s.player ≠ t.1 then none else do
    let (p₁, s₁) ← rules s.player s.state # by simp at h; rw [h]; exact t.2
    some #
      { s with
        player := p₁
      , state := s₁
      , hist := t :: s.hist
      }

namespace Game

universe u
variable {T : GameParams.{u}} (game : Game T)