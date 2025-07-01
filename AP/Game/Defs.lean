import AP.System.Main

def Game.Tr (Pl : Type) (Tr : Pl → Type) : Type :=
  Σ (p : Pl), Tr p

structure Game.State (St Pl : Type) (Tr : Pl → Type) : Type where
  s : St
  hist : List # Game.Tr Pl Tr
  turn : Pl

structure Game (St Pl Re : Type) (Sv Tr : Pl → Type)
(Tv : Pl → Pl → Type) : Type where
  sys : System (Game.State St Pl Tr) (Game.Tr Pl Tr)
  fvs : (p : Pl) → St → Sv p
  fvt : (p : Pl) → Tr p
  -- rules : (p : Pl) ()
  h_tv_rfl : ∀ p, Tv p p = Tr p

namespace Game

variable {St Pl Re Sv Tr Tv} (game : Game St Pl Re Sv Tr Tv)