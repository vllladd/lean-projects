import Projects.Util
import Projects.Point

namespace RatRect

structure Rect : Type where
  pos : PointR
  size : PointR

structure Tiling : Type where
  rs : Finset Rect

def Rect.width (r : Rect) : ℝ := r.size.x
def Rect.height (r : Rect) : ℝ := r.size.y
def Rect.x₁ (r : Rect) : ℝ := r.pos.x
def Rect.y₁ (r : Rect) : ℝ := r.pos.y
def Rect.x₂ (r : Rect) : ℝ := r.x₁ + r.width
def Rect.y₂ (r : Rect) : ℝ := r.y₁ + r.height

class Rect.WF (r : Rect) : Prop where
  width_pos : 0 < r.width
  height_pos : 0 < r.height

def Rect.surface (r : Rect) : Set PointR :=
  Point.ofProd '' .Icc r.x₁ r.x₂ ×ˢ .Icc r.y₁ r.y₂

def Rect.interior (r : Rect) : Set PointR :=
  Point.ofProd '' .Ioo r.x₁ r.x₂ ×ˢ .Ioo r.y₁ r.y₂

def Rect.boundary (r : Rect) : Set PointR :=
  r.surface \ r.interior

def Rect.tiledBy (r : Rect) (t : Tiling) : Prop :=
  ⋃ r' ∈ t.rs, r'.surface = r.surface

class Tiling.WF (t : Tiling) : Prop where
  r_wf : ∀ r ∈ t.rs, r.WF
  rect_eq_of_mem_interior : ∀ r₁ ∈ t.rs, ∀ r₂ ∈ t.rs, ∀ p,
    p ∈ r₁.interior → p ∈ r₂.interior → r₁ = r₂
  exi_rect : ∃ (r : Rect), r.WF ∧ r.tiledBy t

def Rect.trivTiling (r : Rect) : Tiling := ⟨{r}⟩

def Rect.rat (r : Rect) : Prop :=
  ¬Irrational r.width ∨ ¬Irrational r.height

def Tiling.rat (t : Tiling) : Prop :=
  ∀ r ∈ t.rs, r.rat

-----

variable {r : Rect} {t : Tiling}

theorem Rect.wf_def : r.WF ↔ 0 < r.width ∧ 0 < r.height :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[simp]
theorem x₁_lt_x₂ [wf : r.WF] : r.x₁ < r.x₂ := by
  dsimp [Rect.x₁, Rect.x₂]; linarith [wf.width_pos]

@[simp]
theorem y₁_lt_y₂ [wf : r.WF] : r.y₁ < r.y₂ := by
  dsimp [Rect.y₁, Rect.y₂]; linarith [wf.height_pos]

@[simp] theorem pos_x_eq_x₁ : r.pos.x = r.x₁ := rfl
@[simp] theorem pos_y_eq_y₁ : r.pos.y = r.y₁ := rfl

@[simp] theorem x₁_le_x₂ [wf : r.WF] : r.x₁ ≤ r.x₂ := le_of_lt x₁_lt_x₂
@[simp] theorem y₁_le_y₂ [wf : r.WF] : r.y₁ ≤ r.y₂ := le_of_lt y₁_lt_y₂
@[simp] theorem x₁_ne_x₂ [wf : r.WF] : r.x₁ ≠ r.x₂ := ne_of_lt x₁_lt_x₂
@[simp] theorem y₁_ne_y₂ [wf : r.WF] : r.y₁ ≠ r.y₂ := ne_of_lt y₁_lt_y₂

@[simp]
theorem mem_surface {p} : p ∈ r.surface ↔
r.x₁ ≤ p.x ∧ p.x ≤ r.x₂ ∧ r.y₁ ≤ p.y ∧ p.y ≤ r.y₂ := by
  rcases p with ⟨x, y⟩; simp [Rect.surface]; tauto

@[simp]
theorem mem_interior {p} : p ∈ r.interior ↔
r.x₁ < p.x ∧ p.x < r.x₂ ∧ r.y₁ < p.y ∧ p.y < r.y₂ := by
  rcases p with ⟨x, y⟩; simp [Rect.interior]; tauto

@[simp]
theorem mem_boundary [wf : r.WF] {p} : p ∈ r.boundary ↔
((p.x = r.x₁ ∨ p.x = r.x₂) ∧ r.y₁ ≤ p.y ∧ p.y ≤ r.y₂) ∨
((p.y = r.y₁ ∨ p.y = r.y₂) ∧ r.x₁ ≤ p.x ∧ p.x ≤ r.x₂) := by
  rcases p with ⟨x, y⟩; simp [Rect.boundary]
  have h₁ := @le_iff_eq_or_lt ℝ _
  aesop (config := {warnOnNonterminal := false})
  linarith

@[simp] theorem pos_mem_surface [wf : r.WF] : r.pos ∈ r.surface := by simp
@[simp] theorem not_pos_mem_interior : r.pos ∉ r.interior := by simp
@[simp] theorem pos_mem_boundary [wf : r.WF] : r.pos ∈ r.boundary := by simp

@[simp]
theorem surface_ne_empty [wf : r.WF] : r.surface ≠ ∅ := by
  apply Set.ne_empty_of r.pos; simp

@[simp]
theorem boundary_ne_empty [wf : r.WF] : r.boundary ≠ ∅ := by
  apply Set.ne_empty_of r.pos; simp

@[simp]
theorem interior_ne_empty [wf : r.WF] : r.interior ≠ ∅ := by
  apply Set.ne_empty_of # r.pos + r.size / 2
  rcases r with ⟨⟨x, y⟩, ⟨width, height⟩⟩
  simp [Rect.x₁, Rect.y₁, Rect.x₂, Rect.y₂, Rect.width, Rect.height,
    Point.add_def, Point.div_def, Point.ofNat_def]
  use wf.width_pos, wf.height_pos

@[simp]
theorem disjoint_interior_boundary [wf : r.WF] : Disjoint r.interior r.boundary := by
  rw [Set.disjoint_left]; rintro ⟨x, y⟩; aesop

@[simp]
theorem disjoint_boundary_interior [wf : r.WF] : Disjoint r.boundary r.interior := by
  symm; simp

@[simp]
theorem interior_inter_boundary [wf : r.WF] : r.interior ∩ r.boundary = ∅ := by
  simp [←Set.disjoint_iff_inter_eq_empty]

@[simp]
theorem boundary_inter_interior [wf : r.WF] : r.boundary ∩ r.interior = ∅ := by
  simp [←Set.disjoint_iff_inter_eq_empty]

@[simp]
theorem interior_union_boundary_eq_surface [wf : r.WF] :
r.interior ∪ r.boundary = r.surface := by
  ext p; rcases p with ⟨x, y⟩
  have h₁ := @le_iff_eq_or_lt ℝ _
  aesop

@[simp]
theorem boundary_union_interior_eq_surface [wf : r.WF] :
r.boundary ∪ r.interior = r.surface := by
  rw [Set.union_comm]; simp

@[simp]
theorem surface_diff_interior_eq_boundary : r.surface \ r.interior = r.boundary := rfl

@[simp]
theorem surface_diff_boundary_eq_interior [wf : r.WF] :
r.surface \ r.boundary = r.interior := by
  rw [←interior_union_boundary_eq_surface]
  apply Set.union_sdiff_cancel_right; simp

instance [wf : r.WF] : r.trivTiling.WF := by
  simp [Rect.trivTiling]; constructor; simpa; simp; use r, wf; simp [Rect.tiledBy]

@[simp]
theorem tiledBy_trivTiling : r.tiledBy r.trivTiling := by
  simp [Rect.tiledBy, Rect.trivTiling]

@[simp]
theorem Tiling.rat_mk {rs} : (⟨rs⟩ : Tiling).rat ↔ ∀ r ∈ rs, r.rat := by rfl

@[simp]
theorem trivTiling_rat_iff : r.trivTiling.rat ↔ r.rat := by
  simp [Rect.trivTiling]

@[simp]
theorem rs_ne_empty [wf : t.WF] : t.rs ≠ ∅ := by
  have ⟨r, r_wf, h⟩ := wf.exi_rect
  intro h₁; simp [h₁, Rect.tiledBy] at h
  symm at h; simp at h