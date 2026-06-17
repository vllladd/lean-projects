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

@[class]
structure ProgM.WF {α : Type} (m : ProgM α) : Prop where
  inr ⦃xs zs r⦄ : m.run xs = .inr (r, zs) → zs <:+ xs ∧ ∀ ⦃ys⦄,
    m.run (xs ++ ys) = .inr (r, zs ++ ys)
  inl ⦃xs b⦄ : m.run xs = .inl b → ∀ ⦃ys zs r⦄,
    m.run (xs ++ ys) = .inr (r, zs) → zs <:+ ys ∧ zs ≠ ys

def ProgM.toProg (m : ProgM Unit) : Prog where
  run bs := match m.run bs with
  | .inl b => b
  | .inr _ => 0

def Prog.toProgM (p : Prog) : ProgM Unit := do
  let bs ← get
  .lift # .inl # p.run bs

def readBit : ProgM Bit := do
  ioBit 0

def writeBit (b : Bit) : ProgM Unit := do
  _ ← ioBit b

def readBitsUntil (p : List Bit → Bool) : ProgM (List Bit) := do
  let bs ← get
  match bs.inits.find? p with
  | some bs₁ =>
    .set # bs.drop bs₁.length
    pure bs₁
  | none => .lift # .inl 0

def readNat : ProgM ℕ := do
  let bs ← readBitsUntil (0 ∈ ·)
  pure # bs.length - 1

def writeNat (n : ℕ) : ProgM Unit := do
  replicateM' n (writeBit 1)
  writeBit 0