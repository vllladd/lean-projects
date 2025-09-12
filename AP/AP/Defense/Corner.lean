import AP.AP.Defense.Edge

namespace AP

@[ext]
structure Corner : Type where
  dir : Dir
  offset : PointZ
deriving Inhabited, DecidableEq

namespace Corner

@[simp]
def edge (dir : Dir) (offset : PointZ) : Edge where
  dir := dir
  offset := offset.coord dir

def edge₁ (cor : Corner) : Edge :=
  edge cor.dir cor.offset

def edge₂ (cor : Corner) : Edge :=
  edge cor.dir.rotRight cor.offset

def points (cor : Corner) : Set PointZ :=
  cor.edge₁.points ∪ cor.edge₂.points

def memPoints (cor : Corner) (p : PointZ) : Bool :=
  let ⟨x, y⟩ := p
  let ⟨cx, cy⟩ := cor.offset
  match cor.dir with
  | .up => y ≤ cy ∨ cx ≤ x
  | .right => cx ≤ x ∨ cy ≤ y
  | .down => cy ≤ y ∨ x ≤ cx
  | .left => x ≤ cx ∨ y ≤ cy

theorem mem_points_iff_memPoints {cor : Corner} {p} :
p ∈ cor.points ↔ cor.memPoints p := by
  simp [points, edge₁, edge₂, memPoints, Edge.points]
  cases cor.dir <;> simp [Edge.memPoints]

instance {cor : Corner} {p} : Decidable # p ∈ cor.points :=
  match h : cor.memPoints p with
  | true => .isTrue # by simp [mem_points_iff_memPoints, h]
  | false => .isFalse # by simp [mem_points_iff_memPoints, h]

@[simp]
theorem memPoints_eq {cor : Corner} {p} : cor.memPoints p = decide (p ∈ cor.points) := by
  simp [mem_points_iff_memPoints]

-- theorem points_inj {c₁ c₂ : Corner} (h : c₁.points = c₂.points) : c₁ = c₂ := by
--   sorry

-- @[simp]
-- theorem points_eq_points_iff {e₁ e₂ : Corner} : e₁.points = e₂.points ↔ e₁ = e₂ :=
--   ⟨points_inj, λ h => by rw [h]⟩

def dist (cor : Corner) (p : PointZ) : ℤ :=
  min (cor.edge₁.dist p) (cor.edge₂.dist p)

def defenseCnd (cor : Corner) (s : State) : Prop :=
  6 ≤ cor.dist s.aPos ∧ ∀ (p : PointZ), cor.dist p = 0 →
  7 ≤ p.dist cor.offset → p ∈ s.taken

def defenseFn (cor : Corner) (s : State) : Option PointZ :=
  cor.edge₁.defense.f s <|> cor.edge₂.defense.f s

def defense (cor : Corner) : Defense :=
  { cnd := λ s => 6 ≤ cor.dist s.aPos
  , ps := cor.points
  , f := cor.defenseFn
  }