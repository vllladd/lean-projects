import AP.AP.Defense.Edge

namespace AP

@[ext]
structure Corner : Type where
  dir : Dir
  offset : PointZ
deriving Inhabited, DecidableEq

namespace Corner

variable {c c₁ c₂ : Corner}

@[simp]
def edge (dir : Dir) (offset : PointZ) : Edge where
  dir := dir
  offset := offset.coord dir

def edge₁ (c : Corner) : Edge :=
  edge c.dir c.offset

def edge₂ (c : Corner) : Edge :=
  edge c.dir.rotRight c.offset

def points (c : Corner) : Set PointZ :=
  c.edge₁.points ∪ c.edge₂.points

def memPoints (c : Corner) (p : PointZ) : Bool :=
  let ⟨x, y⟩ := p
  let ⟨cx, cy⟩ := c.offset
  match c.dir with
  | .up => y ≤ cy ∨ cx ≤ x
  | .right => cx ≤ x ∨ cy ≤ y
  | .down => cy ≤ y ∨ x ≤ cx
  | .left => x ≤ cx ∨ y ≤ cy

theorem mem_points_iff_memPoints {p} :
p ∈ c.points ↔ c.memPoints p := by
  simp [points, edge₁, edge₂, memPoints, Edge.points]
  cases c.dir <;> simp [Edge.memPoints]

instance {p} : Decidable # p ∈ c.points :=
  match h : c.memPoints p with
  | true => .isTrue # by simp [mem_points_iff_memPoints, h]
  | false => .isFalse # by simp [mem_points_iff_memPoints, h]

@[simp]
theorem memPoints_eq {p} : c.memPoints p = decide (p ∈ c.points) := by
  simp [mem_points_iff_memPoints]

-- theorem points_inj (h : c₁.points = c₂.points) : c₁ = c₂ := by
--   sorry

-- @[simp]
-- theorem points_eq_points_iff : c₁.points = c₂.points ↔ c₁ = c₂ :=
--   ⟨points_inj, λ h => by rw [h]⟩

def dist (c : Corner) (p : PointZ) : ℤ :=
  min (c.edge₁.dist p) (c.edge₂.dist p)

def defenseCnd (c : Corner) (s : State) : Prop :=
  6 ≤ c.dist s.aPos ∧ ∀ (p : PointZ), c.dist p = 0 →
  7 ≤ p.dist c.offset → p ∈ s.taken

def defenseFn (c : Corner) (s : State) : Option PointZ :=
  c.edge₁.defense.f s <|> c.edge₂.defense.f s

def defense (c : Corner) : Defense :=
  { cnd := c.defenseCnd
  , ps := c.points
  , f := c.defenseFn
  }

section min

variable {α : Type*} [ha₁ : LinearOrder α]

theorem _root_.le_of_le_min_left {a b c : α} (h : a ≤ min b c) : a ≤ b := by
  rw [le_inf_iff] at h; exact h.1

theorem _root_.le_of_le_min_right {a b c : α} (h : a ≤ min b c) : a ≤ c := by
  rw [le_inf_iff] at h; exact h.2

end min

theorem cnd_defense_edge₁ {s} (h : c.defenseCnd s) : c.edge₁.defense.cnd s :=
  le_of_le_min_left h.1

theorem cnd_defense_edge₂ {s} (h : c.defenseCnd s) : c.edge₂.defense.cnd s :=
  le_of_le_min_right h.1

@[simp] theorem ps_defense : c.defense.ps = c.points := rfl
@[simp] theorem f_defense : c.defense.f = c.defenseFn := rfl

-- #check 0 #exit

theorem validTr_defense : c.defense.ValidTr := by
  constructor
  sorry

theorem wf_defense : c.defense.WF := by
  have H := c.validTr_defense
  constructor; intro s hs h a Ha d Hd n
  have h₁ := cnd_defense_edge₁ h
  have h₂ := cnd_defense_edge₂ h
  have He₁ : c.edge₁.defense.WF; infer_instance
  have He₂ : c.edge₂.defense.WF; infer_instance
  generalize he₁ : c.edge₁.defense = e₁ at h₁ He₁
  generalize he₂ : c.edge₂.defense = e₂ at h₂ He₂
  have H₁ := He₁.2 h₁ a (e₂.st d) n
  have H₂ := He₂.2 h₂ a (e₁.st d) n
  
  generalize hr : sys.simulate (Strat.f ⟨a, e₁.st # e₂.st d⟩) s n = r at H₁
  
  have h₃ : sys.simulate (Strat.f ⟨a, e₂.st # e₁.st d⟩) s n = r
  · rw [←hr]
    -- apply simulate_congr <;> intro k hk b hb h₃ h₄ h₅ <;> simp
    sorry
  
  rw [h₃] at H₂; clear h₃
  
  have h₄ : sys.simulate (Strat.f ⟨a, c.defense.st d⟩) s n = r
  · rw [←hr]
    apply simulate_congr <;> intro k hk b hb h₃ h₄ h₅ <;> simp
    sorry
  
  rw [h₄]
  subst he₁ he₂
  simp at H₁ H₂
  simp [points, H₁, H₂]

-- #check 0 #exit

@[simp]
instance : c.defense.WF := wf_defense