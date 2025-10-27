import AP.AP.Defense.Edge.Basic

section order

variable {α : Type*} [ha : LinearOrder α]

theorem le_congr {a b c d : α} (h₁ : a = c) (h₂ : b = d) : a ≤ b ↔ c ≤ d := by rw [h₁, h₂]

-- #check 0 #exit

end order

namespace Set'

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable [hb₁ : DecidableEq β] [hb₂ : Hashable β]
variable [hc₁ : DecidableEq γ] [hc₂ : Hashable γ]
variable {s s' s₁ s₂ s₃ : Set' α}

@[simp]
theorem forall_ne_iff_not_mem {x} : (∀ y ∈ s, y ≠ x) ↔ x ∉ s := by
  simp_all only [ne_eq]
  apply Iff.intro
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    apply a
    on_goal 2 => rfl
    · simp_all only
  · intro a y a_1
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    subst a_2
    simp_all only

-- #check 0 #exit

end Set'

namespace AP.Edge

variable {e e₁ e₂ : Edge}

protected def rotRight (e : Edge) : Edge where
  dir := e.dir.rotRight
  offset := if e.hor then -e.offset else e.offset

@[simp]
theorem points_rotRight : e.rotRight.points = rotRight.ft '' e.points := by
  ext p
  simp [rotRight, Edge.rotRight, points, memPoints, Dir.vert]
  by_contra h
  cases hd : e.dir
  all_goals
    revert h
    simp [hd, Point.ext_iff]
    constructor
    · intro h
      use ⟨p.y, -p.x⟩
      simp
      linarith
    · rintro ⟨⟨x₁, y₁⟩, h₁, h₂, h₃⟩
      linarith

@[simp]
theorem dist_rotRight {p} : e.rotRight.dist p = e.dist (rotRight.ft' p) := by
  simp [rotRight, Edge.rotRight, dist]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd] <;> ring_nf

@[simp]
theorem rotRight_getBorderPoint₀ {p} :
e.rotRight.getBorderPoint₀ p = rotRight.ft (e.getBorderPoint₀ # rotRight.ft' p) := by
  simp [Edge.rotRight, rotRight, getBorderPoint₀, getBorderPoint]
  by_contra h; cases hd : e.dir <;> revert h <;> simp [hd]

@[simp]
theorem rotRight_getBorderPoint_of_hor [H : Fact e.hor] {p d} :
e.rotRight.getBorderPoint p d = rotRight.ft (e.getBorderPoint (rotRight.ft' p) d) := by
  rcases H with ⟨H⟩; unfold hor at H; simp [Edge.rotRight, getBorderPoint]
  by_contra h; cases hd : e.dir <;> simp [hd] at H <;> revert h <;> simp [hd, rotRight]

@[simp]
theorem rotRight_getBorderPoints_of_hor [H : Fact e.hor] {p d} :
e.rotRight.getBorderPoints p d = (e.getBorderPoints (rotRight.ft' p) d).map rotRight.ft := by
  rcases H with ⟨H⟩; unfold hor at H; simp [Edge.rotRight, getBorderPoints, getBorderPoint]
  by_contra h; cases hd : e.dir <;> simp [hd] at H <;> revert h <;> simp [hd, rotRight]

-- #check 0 #exit

theorem rotRight_defense_of_hor [H : Fact e.hor] :
e.rotRight.defense = e.defense.sym rotRight := by
  have hv : e.dir.vert := H.1
  
  simp [defense, Defense.sym]
  ext s p :2
  simp
  have h : ∀ p₁, rotRight.ft p₁ = p ↔ rotRight.ft' p = p₁
  · rcases p with ⟨x, y⟩; rintro ⟨x₁, y₁⟩
    simp [rotRight, Point.ext_iff]; constructor <;> intro h <;> constructor <;> linarith
  simp [h]; clear h
  simp [f, f']
  intro h₁ h₂
  split <;> nm x h₃ <;> clear x <;> try simp
  · simp [ft_eq_iff]
  · simp [ft'_eq_iff, ft_eq_iff]
  · simp [ft'_eq_iff, ft_eq_iff]
  ·
    simp [ft'_eq_iff]
    split_ifs with h₄
    ·
      simp [getBorderPoints, getBorderPoint, hv]
      simp [List.find?, rotRight]
      sorry
    · sorry
  · simp [ft'_eq_iff, ft_eq_iff]