import AP.AP.Defense.Edge

section min

variable {α : Type*} [ha₁ : LinearOrder α]

theorem le_of_le_min_left {a b c : α} (h : a ≤ min b c) : a ≤ b := by
  rw [le_inf_iff] at h; exact h.1

theorem le_of_le_min_right {a b c : α} (h : a ≤ min b c) : a ≤ c := by
  rw [le_inf_iff] at h; exact h.2

end min

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

def cnd' (c : Corner) (s : State) : Prop :=
  ∀ (p : PointZ), c.dist p = 0 → 7 ≤ p.dist c.offset → p ∈ s.taken

def cnd (c : Corner) (s : State) : Prop :=
  6 ≤ c.dist s.aPos ∧ c.cnd' s

def f (c : Corner) (s : State) : Option PointZ :=
  c.edge₁.defense.f s <|> c.edge₂.defense.f s

def defense (c : Corner) : Defense :=
  { cnd := c.cnd
  , ps := c.points
  , f := c.f
  }

theorem cnd_defense_edge₁ {s} (h : c.cnd s) : c.edge₁.defense.cnd s :=
  le_of_le_min_left h.1

theorem cnd_defense_edge₂ {s} (h : c.cnd s) : c.edge₂.defense.cnd s :=
  le_of_le_min_right h.1

@[simp] theorem ps_defense : c.defense.ps = c.points := rfl
@[simp] theorem f_defense : c.defense.f = c.f := rfl

theorem edge₁_hor_iff : c.edge₁.dir.hor ↔ c.edge₂.dir.vert := by
  simp [edge₁, edge₂]; split <;> simp_all

theorem edge₂_hor_iff : c.edge₂.dir.hor ↔ c.edge₁.dir.vert := by
  simp [edge₁, edge₂]; split <;> simp_all

theorem edge₁_vert_iff : c.edge₁.dir.vert ↔ c.edge₂.dir.hor := by
  simp [edge₁, edge₂]; split <;> simp_all

theorem edge₂_vert_iff : c.edge₂.dir.vert ↔ c.edge₁.dir.hor := by
  simp [edge₁, edge₂]; split <;> simp_all

theorem cnd'_of_reachable {s s'} [hs : sys.WF s]
(h₁ : sys.Reachable s s') (h₂ : c.cnd' s) : c.cnd' s' :=
  λ p hp h => s.mem_taken_of_reachable h₁ # h₂ p hp h

-- #check 0 #exit

theorem edge₂_eq_none_of_edge₁_eq_some {s p} (H : c.cnd' s)
(h : c.edge₁.defense.f s = some p) : c.edge₂.defense.f s = none := by
  rename' h => h₁, p => p₁
  by_contra h₂
  replace h₂ := Option.exists_eq_some_of_ne_none h₂
  obtain ⟨p₂, h₂⟩ := h₂
  
  replace h₁ := Edge.of_eq_some h₁
  replace h₂ := Edge.of_eq_some h₂
  
  rcases h₁ with ⟨h₁, h₃, z₁, h₄, h₅⟩
  rcases h₂ with ⟨h₂, h₆, z₂, h₇, h₈⟩
  
  simp [cnd'] at H
  simp [Edge.getBorderPoint] at h₅ h₈
  subst h₅ h₈
  
  cases h₉ : c.dir
  all_goals simp_all [dist, Edge.dist, Point.dist, edge₁, edge₂, abs_le]; clear h₉
  · rcases h₄ with ⟨h₄, H₄⟩
    rcases h₇ with ⟨h₇, H₇⟩
    apply h₃
    clear h₃
    apply H
    · simp
      by_contra! h₈
      apply h₆
      clear h₆
      apply H
      · simp
        by_contra! h₉
        sorry
      sorry
    sorry
  · sorry
  · sorry
  · sorry

-- #check 0 #exit

theorem validTr_defense : c.defense.ValidTr := by
  constructor; intro s hs p h; simp [f] at h; rcases h with h | ⟨h₁, h₂⟩
  exact Defense.valid_tr h; exact Defense.valid_tr h₂

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
  · rw [←hr, ←Defense.simulate_st_comm]; subst he₁ he₂
    intro s' h₃ p₁ p₂ h₄; have h₅ := c.cnd'_of_reachable h₃ h.2
    simp [edge₂_eq_none_of_edge₁_eq_some h₅ h₄]
  rw [h₃] at H₂; clear h₃
  have h₄ : sys.simulate (Strat.f ⟨a, c.defense.st d⟩) s n = r
  · convert hr using 2; ext1 s
    unfold Strat.f; split_ifs with ht <;> simp
    simp [defense, f, Defense.st, he₁, he₂]
  rw [h₄]; subst he₁ he₂; simp at H₁ H₂; simp [points, H₁, H₂]

@[simp]
instance : c.defense.WF := wf_defense