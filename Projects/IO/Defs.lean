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

@[class]
structure ProgM.WF {α : Type} (prog : ProgM α) : Prop where
  inr {xs zs r} : prog.run xs = .inr (r, zs) → zs <:+ xs ∧ ∀ ⦃ys⦄,
    prog.run (xs ++ ys) = .inr (r, zs ++ ys)
  inl {xs ys b} : prog.run xs = .inl b → ∀ ⦃r zs⦄,
    prog.run (xs ++ ys) = .inr (r, zs) → zs <:+ ys ∧ zs ≠ ys