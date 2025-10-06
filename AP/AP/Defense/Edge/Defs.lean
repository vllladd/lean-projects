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
  if e.hor then ⟨p.x + d, e.offset⟩ else ⟨e.offset, p.y + d⟩

def getBorderPoint₀ (e : Edge) (p : PointZ) : PointZ :=
  e.getBorderPoint p 0

def getBorderPoints (e : Edge) (p : PointZ) (d : ℕ) : List PointZ :=
  [e.getBorderPoint p (-d : ℤ), e.getBorderPoint p d]

def f' (e : Edge) (s : State) : Option PointZ :=
  let pa := s.aPos
  let p₀ := e.getBorderPoint₀ pa
  let pick := λ (xs : List PointZ) => xs.find? (· ∉ s.taken)
  let get := e.getBorderPoints pa
  match e.dist pa with
  | 5 => some p₀
  | 4 => pick # p₀ :: get 1
  | 3 => pick # get 1 ++ [p₀]
  | 2 => if p₀ ∉ s.taken then some p₀ else
    let ps₁ := get 1
    let ps₂ := get 2
    let f := λ (ps₁ ps₂ : List PointZ) => do
      let p ← ps₁ |>.find? (· ∈ s.taken)
      ps₂ |>.find? # λ p' => p' ∉ s.taken ∧ p'.dist p ≠ 1
    f ps₁ ps₂ |>.elim (f ps₂ ps₁) some
  | 1 => pick # p₀ :: get 1
  | _ => none

def f (e : Edge) (s : State) : Option PointZ := do
  let p ← e.f' s
  guard # p ≠ s.aPos
  guard # p ∉ s.taken
  return p

def defense (e : Edge) : Defense :=
  { cnd := λ s => 6 ≤ e.dist s.aPos
  , ps := e.points
  , f := e.f
  }