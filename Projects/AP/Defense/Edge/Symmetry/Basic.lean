import Projects.AP.Defense.Edge.Basic

namespace AP.Edge

variable {e e₁ e₂ : Edge}

@[simp] theorem vert_dir_of_hor [H : Fact e.hor] : e.dir.vert := H.1
@[simp] theorem not_hor_dir_of_hor [H : Fact e.hor] : ¬e.dir.hor := by simp
@[simp] theorem hor_dir_of_vert [H : Fact e.vert] : e.dir.hor := H.1
@[simp] theorem not_vert_dir_of_vert [H : Fact e.vert] : ¬e.dir.vert := by simp
@[simp] theorem dir_eq_of_up [H : Fact # e.dir = .up] : e.dir = .up := H.1
@[simp] theorem dir_eq_of_down [H : Fact # e.dir = .down] : e.dir = .down := H.1
@[simp] theorem hor_of_up [H : Fact # e.dir = .up] : e.hor := by simp
@[simp] theorem not_vert_of_up [H : Fact # e.dir = .up] : ¬e.vert := by simp
@[simp] theorem hor_of_down [H : Fact # e.dir = .down] : e.hor := by simp

@[simp] instance [H : Fact # e.dir = .up] : Fact # e.hor := by simp

@[simp] theorem dir_eq_or_eq_of_hor [H : Fact e.hor] : e.dir = .up ∨ e.dir = .down := by
  cases hd : e.dir <;> simp [hd] at H ⊢