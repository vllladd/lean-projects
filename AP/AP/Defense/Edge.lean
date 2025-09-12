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

@[simp] def hor (e : Edge) : Prop := e.dir.vert
@[simp] def vert (e : Edge) : Prop := e.dir.hor

instance {e : Edge} : Decidable e.hor := by unfold hor; infer_instance
instance {e : Edge} : Decidable e.vert := by unfold vert; infer_instance

def memPoints (e : Edge) (p : PointZ) : Bool :=
  match e.dir with
  | .up => p.y ≤ e.offset
  | .right => e.offset ≤ p.x
  | .down => e.offset ≤ p.y
  | .left => p.x ≤ e.offset

def points (e : Edge) : Set PointZ :=
  {p | e.memPoints p}

theorem mem_points_iff_memPoints {e : Edge} {p} :
p ∈ e.points ↔ e.memPoints p := by rfl

instance {e : Edge} {p} : Decidable # p ∈ e.points :=
  match h : e.memPoints p with
  | true => .isTrue # by simp [mem_points_iff_memPoints, h]
  | false => .isFalse # by simp [mem_points_iff_memPoints, h]

theorem memPoints_eq {e : Edge} {p} : e.memPoints p = decide (p ∈ e.points) := by
  simp [mem_points_iff_memPoints]

theorem points_inj {e₁ e₂ : Edge} (h : e₁.points = e₂.points) : e₁ = e₂ := by
  rw [Set.ext_iff] at h; rcases e₁, e₂ with ⟨⟨d₁, n₁⟩, ⟨d₂, n₂⟩⟩; simp
  cases d₁ <;> cases d₂ <;> simp <;> simp [points, memPoints] at h <;> exact h

@[simp]
theorem points_eq_points_iff {e₁ e₂ : Edge} : e₁.points = e₂.points ↔ e₁ = e₂ :=
  ⟨points_inj, λ h => by rw [h]⟩

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

theorem sorted_lt_getBorderPoints {e : Edge} {p d} (h : d ≠ 0) :
(e.getBorderPoints p d).Sorted (· < ·) := by
  simp [getBorderPoints, getBorderPoint]
  split_ifs with h₁ <;> simp [h, Nat.zero_lt_of_ne_zero h]

def defenseFn (e : Edge) (s : State) : Option PointZ :=
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

def defense (e : Edge) : Defense :=
  { cnd := λ s => 6 ≤ e.dist s.aPos
  , ps := e.points
  , f := e.defenseFn
  }

def cnd (e : Edge) (s : State) : Prop :=
  let pa := s.aPos
  let p₀ := e.getBorderPoint₀ pa
  let get := e.getBorderPoints pa
  match e.dist pa with
  | 5 => p₀ ∈ s.taken
  | 4 => p₀ ∈ s.taken ∧ (get 1).any (· ∈ s.taken)
  | 3 => 2 ≤ (p₀ :: get 1).countP (· ∈ s.taken)
  | 2 => sorry
  | 1 => (p₀ :: get 1).all (· ∈ s.taken)
  | d => 0 < d

-- #check 0 #exit