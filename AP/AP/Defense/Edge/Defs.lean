import AP.Dir
import AP.AP.Symmetry
import AP.AP.Defense.Basic

namespace AP

@[ext]
structure Edge : Type where
  dir : Dir
  offset : ℤ
deriving Inhabited, DecidableEq

namespace Edge

variable {e e₁ e₂ : Edge}

@[simp] def hor (e : Edge) : Prop := e.dir.vert
@[simp] def vert (e : Edge) : Prop := e.dir.hor

instance : Decidable e.hor := by unfold hor; infer_instance
instance : Decidable e.vert := by unfold vert; infer_instance

def memPoints (e : Edge) (p : PointZ) : Bool :=
  match e.dir with
  | .up => p.y ≤ e.offset
  | .right => e.offset ≤ p.x
  | .down => e.offset ≤ p.y
  | .left => p.x ≤ e.offset

def points (e : Edge) : Set PointZ :=
  {p | e.memPoints p}

def dist (e : Edge) (p : PointZ) : ℤ :=
  match e.dir with
  | .up => p.y - e.offset
  | .down => e.offset - p.y
  | .left => p.x - e.offset
  | .right => e.offset - p.x

def getBorderPoint (e : Edge) (p : PointZ) (d : ℤ) : PointZ :=
  match e.dir with
  | .up => ⟨p.x - d, e.offset⟩
  | .down => ⟨p.x + d, e.offset⟩
  | .left => ⟨e.offset, p.y + d⟩
  | .right => ⟨e.offset, p.y - d⟩

def getBorderPoint₀ (e : Edge) (p : PointZ) : PointZ :=
  e.getBorderPoint p 0

def getBorderPoints (e : Edge) (p : PointZ) (d : ℕ) : List PointZ :=
  [e.getBorderPoint p (-d : ℤ), e.getBorderPoint p d]

def ptsArr (e : Edge) (s : State) (start : ℤ) (len : ℕ) : Array Bool :=
  ⟨List.range len |>.map # λ i => e.getBorderPoint s.aPos (start + i) ∈ s.taken⟩

def cndMp : Map ℤ # List # Array Bool := Map.ofList #
  [ (1, ["0011100"])
  , (2, ["0101100", "0011010"])
  , (3, ["1010010", "1001100", "0110010", "0100110", "0100101", "0011001"])
  , (4, ["0100100", "0100010", "0011000", "0010010", "0001100"])
  , (5, ["0010000", "0001000", "0000100"])
  ].map # λ (d, xs) => (d, ·) #
  xs.map # λ ⟨s⟩ => ⟨s.map ('0' == ·)⟩

def cnd (d : ℤ) (f : ℕ → Bool) : Bool :=
  match cndMp.get? d with
  | none => true
  | some xs => xs.any # λ arr => ∀ (i : Fin 7), arr[i]? = some true → f i

def f₄ (d : ℤ) (f : ℕ → Bool) : ℕ :=
  List.range 7 |>.find? (λ i => cnd d # λ k => if k == i then true else f k) |>.getD 0

def f₃ (d : ℤ) (f : ℕ → Bool) : Option ℕ :=
  if cnd d f then none else some # f₄ d f

def f₂ (d : ℤ) (arr : Array Bool) (offset : ℕ) : Option ℕ :=
  f₃ d # λ i => arr[offset + i]?.getD false

def f₁ (e : Edge) (s : State) : Option PointZ := do
  let i ← f₂ (e.dist s.aPos) (e.ptsArr s (-3) 7) 0
  return e.getBorderPoint s.aPos (i - 3)

def f (e : Edge) (s : State) : Option PointZ := do
  let p ← e.f₁ s
  guard # p ≠ s.aPos
  guard # p ∉ s.taken
  return p

def defense (e : Edge) : Defense where
  cnd := λ s => s.pw = 1 ∧ 6 ≤ e.dist s.aPos
  ps := e.points
  f := e.f

def edge₀ : Edge where
  dir := .down
  offset := 0