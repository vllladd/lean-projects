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

theorem mem_points_iff_memPoints {p} : p ∈ e.points ↔ e.memPoints p := by rfl

instance {p} : Decidable # p ∈ e.points :=
  match h : e.memPoints p with
  | true => .isTrue # by simp [mem_points_iff_memPoints, h]
  | false => .isFalse # by simp [mem_points_iff_memPoints, h]

theorem memPoints_eq {p} : e.memPoints p = decide (p ∈ e.points) := by
  simp [mem_points_iff_memPoints]

theorem points_inj (h : e₁.points = e₂.points) : e₁ = e₂ := by
  rw [Set.ext_iff] at h; rcases e₁, e₂ with ⟨⟨d₁, n₁⟩, ⟨d₂, n₂⟩⟩; simp
  cases d₁ <;> cases d₂ <;> simp <;> simp [points, memPoints] at h <;> exact h

@[simp]
theorem points_eq_points_iff : e₁.points = e₂.points ↔ e₁ = e₂ :=
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

theorem sorted_lt_getBorderPoints {p d} (h : d ≠ 0) :
(e.getBorderPoints p d).Sorted (· < ·) := by
  simp [getBorderPoints, getBorderPoint]
  split_ifs with h₁ <;> simp [h, Nat.zero_lt_of_ne_zero h]

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

@[simp] theorem ps_defense : e.defense.ps = e.points := rfl

set_option maxHeartbeats 1000000 in
theorem of_eq_some {s p} (h : e.defense.f s = some p) :
0 < e.dist s.aPos ∧ e.dist s.aPos ≤ 5 ∧ p ∉ s.taken ∧
∃ (z : ℤ), |z| ≤ 2 ∧ e.getBorderPoint s.aPos z = p := by
  simp [defense, f, f', getBorderPoints, getBorderPoint₀, List.find?_cons] at h
  split at h <;> aesop'

theorem dist_eq_zero_of_eq_some {s p} (h : e.defense.f s = some p) : e.dist p = 0 := by
  obtain ⟨-, h₁, h₂, z, h₃, rfl⟩ := of_eq_some h; simp [getBorderPoint]; split_ifs with h₄
  · rw [Dir.vert_iff] at h₄; rcases h₄ with h₄ | h₄ <;> simp [dist, h₄]
  · simp [Dir.hor_iff] at h₄; rcases h₄ with h₄ | h₄ <;> simp [dist, h₄]

theorem not_mem_taken_of_eq_some {s p} (h : e.defense.f s = some p) : p ∉ s.taken := by
  obtain ⟨-, h₁, h₂, z, h₃, h₄⟩ := of_eq_some h; exact h₂

theorem validTr_defense : e.defense.ValidTr := by
  constructor; intro s hs p h
  replace h := of_eq_some h
  simp [getBorderPoint, dist] at h
  cases hd : e.dir
  all_goals
    obtain ⟨h₁, h₂, h₃, z, h₄, rfl⟩ := h
    simp [hd] at h₁ h₂ h₃ ⊢
    simp [DState.validTr_iff]
    refine ⟨?_, h₃⟩
    simp [Point.ext_iff]
    aesop'

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

theorem wf_defense : e.defense.WF := by
  have H := e.validTr_defense
  constructor; intro s hs h a Ha d Hd n
  sorry

-- #check 0 #exit

@[simp]
instance : e.defense.WF := wf_defense