import AP.Dir
import AP.AP.Defense

namespace AP

@[ext]
structure Edge : Type where
  dir : Dir
  offset : ℤ
deriving Inhabited, DecidableEq

def Edge.memPoints (e : Edge) (p : PointZ) : Bool :=
  match e.dir with
  | .up => p.y ≤ e.offset
  | .down => e.offset ≤ p.y
  | .left => p.x ≤ e.offset
  | .right => e.offset ≤ p.x

def Edge.points (e : Edge) : Set PointZ :=
  {p | e.memPoints p}

theorem Edge.mem_points_iff_memPoints {e : Edge} {p} :
p ∈ e.points ↔ e.memPoints p := by rfl

instance {e : Edge} {p} : Decidable # p ∈ e.points :=
  match h : e.memPoints p with
  | true => .isTrue # by simp [Edge.mem_points_iff_memPoints, h]
  | false => .isFalse # by simp [Edge.mem_points_iff_memPoints, h]

theorem Edge.memPoints_eq {e : Edge} {p} : e.memPoints p = decide (p ∈ e.points) := by
  simp [mem_points_iff_memPoints]

theorem Edge.points_inj {e₁ e₂ : Edge} (h : e₁.points = e₂.points) : e₁ = e₂ := by
  rw [Set.ext_iff] at h; rcases e₁, e₂ with ⟨⟨d₁, n₁⟩, ⟨d₂, n₂⟩⟩; simp
  cases d₁ <;> cases d₂ <;> simp <;> simp [points, memPoints] at h <;> exact h

@[simp]
theorem Edge.points_eq_points_iff {e₁ e₂ : Edge} : e₁.points = e₂.points ↔ e₁ = e₂ :=
  ⟨points_inj, λ h => by rw [h]⟩

def Edge.dist (e : Edge) (p : PointZ) : ℤ :=
  match e.dir with
  | .up => p.y - e.offset
  | .down => e.offset - p.y
  | .left => p.x - e.offset
  | .right => e.offset - p.x

-- def Edge.defenseFn {edge : Set PointZ} (s : State) : Option State := do
--   none

-- #check 0 #exit