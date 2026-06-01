import Projects.Util

namespace VerifiedIO

variable {α β γ : Type}

@[ext]
structure Prog where
  run : List Bit → Bit

abbrev ProgM : Type → Type :=
  StateT (List Bit) (Sum Bit)

def ioBit (b : Bit) : ProgM Bit := do
  match ←get with
  | [] => .lift # .inl b
  | b₀ :: bs => set bs; pure b₀

def ProgM.toProg (m : ProgM Unit) : Prog where
  run bs := match m.run bs with
  | .inl b => b
  | .inr _ => 0

def Prog.toProgM₂ (p : Prog) (bs : List Bit) (n : ℕ) : ProgM Unit := do
  match n with
  | 0 => pure ()
  | n + 1 =>
    let b ← ioBit # p.run bs
    p.toProgM₂ (bs ++ [b]) n

def Prog.toProgM₁ (p : Prog) (bs : List Bit) : ProgM Unit := do
  let n ← gets List.length
  p.toProgM₂ bs # n + 1

def Prog.toProgM (p : Prog) : ProgM Unit :=
  p.toProgM₁ []

@[class]
inductive ProgM.WF : {α : Type} → ProgM α → Prop where
| toProgM {p : Prog} : WF p.toProgM
| pure {α : Type} {x : α} : WF (pure x)
| bind {α β : Type} {m : ProgM α} {f : α → ProgM β} :
  WF m → (∀ x, WF (f x)) → WF (m >>= f)
| bit {b} : WF (ioBit b)