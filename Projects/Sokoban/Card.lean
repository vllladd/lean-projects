import Projects.Sokoban.Basic

namespace Sokoban

theorem point_eq_of_fin {s : State} [hs : s.WF] {p : PointZ}
(h : p ∈ s.grid) : p = ⟨(p.x.toFin : Fin s.width), (p.y.toFin : Fin s.height)⟩ := by
  rcases p with ⟨x, y⟩
  simp
  simp [hs.mem_grid_iff_bounds] at h
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  rw [eq_comm]; nth_rw 2 [eq_comm]
  simp [Int.toFin, Nat.toFin]
  rw [max_eq_left h₁, max_eq_left h₂]
  exact ⟨Int.emod_eq_of_lt h₁ h₃, Int.emod_eq_of_lt h₂ h₄⟩

theorem x_toFin_width_eq_iff' {s : State} [hs : s.WF] {p₁ p₂ : PointZ}
(h₁ : p₁ ∈ s.grid) (h₂ : p₂ ∈ s.grid) :
(p₁.x.toFin : Fin s.width) = p₂.x.toFin ↔ p₁.x = p₂.x := by
  nth_rw 2 [point_eq_of_fin h₁, point_eq_of_fin h₂]; simp

theorem y_toFin_width_eq_iff' {s : State} [hs : s.WF] {p₁ p₂ : PointZ}
(h₁ : p₁ ∈ s.grid) (h₂ : p₂ ∈ s.grid) :
(p₁.y.toFin : Fin s.height) = p₂.y.toFin ↔ p₁.y = p₂.y := by
  nth_rw 2 [point_eq_of_fin h₁, point_eq_of_fin h₂]; simp

theorem x_toFin_width_eq_iff {n} [hn : NeZero n] {s₁ s₂ : State}
[hs₁ : s₁.WF] [hs₂ : s₂.WF] {p₁ p₂}
(hw₁ : s₁.width = n) (hw₂ : s₂.width = n) (h₁ : p₁ ∈ s₁.grid) (h₂ : p₂ ∈ s₂.grid) :
(p₁.x.toFin : Fin n) = p₂.x.toFin ↔ p₁.x = p₂.x := by
  nth_rw 2 [point_eq_of_fin h₁, point_eq_of_fin h₂];
  simp [Fin.ext_iff, -Fin.val_eq_val_iff]
  congr!; exact hw₁.symm; exact hw₂.symm

theorem y_toFin_width_eq_iff {n} [hn : NeZero n] {s₁ s₂ : State}
[hs₁ : s₁.WF] [hs₂ : s₂.WF] {p₁ p₂}
(hw₁ : s₁.height = n) (hw₂ : s₂.height = n) (h₁ : p₁ ∈ s₁.grid) (h₂ : p₂ ∈ s₂.grid) :
(p₁.y.toFin : Fin n) = p₂.y.toFin ↔ p₁.y = p₂.y := by
  nth_rw 2 [point_eq_of_fin h₁, point_eq_of_fin h₂];
  simp [Fin.ext_iff, -Fin.val_eq_val_iff]
  congr!; exact hw₁.symm; exact hw₂.symm

structure Card.FinState (w h : ℕ) [NeZero w] [NeZero h] where
  grid : Map (Fin w × Fin h) Tile
  player : Fin w × Fin h
deriving Fintype

def Card.fn (s₀ : State) [hs : s₀.WF] (s : State) :
FinState s₀.width s₀.height :=
  { grid := Map.range # λ p => s.grid.get! ⟨p.1, p.2⟩
    player := (s.player.x.toFin, s.player.y.toFin)
  }

theorem nonneg_x_of_get {s : State} {x y d}
[hs : s.WF] [h : s.Get ⟨x, y⟩ d] : 0 ≤ x := by
  replace h := Map.mem_of_get?_eq_some h.1; rw [hs.mem_grid_iff_bounds] at h; grind

theorem nonneg_y_of_get {s : State} {x y d}
[hs : s.WF] [h : s.Get ⟨x, y⟩ d] : 0 ≤ y := by
  replace h := Map.mem_of_get?_eq_some h.1; rw [hs.mem_grid_iff_bounds] at h; grind

theorem x_lt_width_of_get {s : State} {x y d}
[hs : s.WF] [h : s.Get ⟨x, y⟩ d] : x < s.width := by
  replace h := Map.mem_of_get?_eq_some h.1; rw [hs.mem_grid_iff_bounds] at h; grind

theorem y_lt_height_of_get {s : State} {x y d}
[hs : s.WF] [h : s.Get ⟨x, y⟩ d] : y < s.height := by
  replace h := Map.mem_of_get?_eq_some h.1; rw [hs.mem_grid_iff_bounds] at h; grind

theorem toFin_eq_of_get? {s s' : State} {p d} [hs : s.WF] [hs' : s'.WF]
(h₁ : sys.Reachable s s') (h₂ : s'.grid.get? p = some d) :
⟨(p.1.toFin : Fin s.width), (p.2.toFin : Fin s.height)⟩ = p := by
  rcases p with ⟨x, y⟩; simp; replace h₂ : s'.Get _ _ := ⟨h₂⟩; split_ands
  · apply Int.toFin_eq_self_of # nonneg_x_of_get (h := h₂)
    rw [←width_eq_of_reachable h₁]; exact x_lt_width_of_get (h := h₂)
  · apply Int.toFin_eq_self_of # nonneg_y_of_get (h := h₂)
    rw [←height_eq_of_reachable h₁]; exact y_lt_height_of_get (h := h₂)

theorem finite_reachable {s : State} [hs : s.WF] :
{s' | sys.Reachable s s'}.Finite := by
  rename' s => s₀
  unfold Set.Finite
  simp
  apply Finite.of_injective # λ ⟨s, _⟩ => Card.fn s₀ s
  rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ h
  simp [Card.fn] at h
  rcases h with ⟨h₁, h₂, h₃⟩
  simp
  have h₄ : s₁.WF := wf_of_reachable hs₁
  have h₅ : s₂.WF := wf_of_reachable hs₂
  ext:1
  · rw [width_eq_of_reachable hs₁, width_eq_of_reachable hs₂]
  · rw [height_eq_of_reachable hs₁, height_eq_of_reachable hs₂]
  · clear h₂ h₃
    ext p d
    specialize h₁ p.x.toFin p.y.toFin
    simp only [Map.get!_eq_get?_get!] at h₁
    by_cases hp : p ∉ s₀.grid
    · constructor <;> intro h₂ <;> replace h₂ := Map.mem_of_get?_eq_some h₂
      · rw [mem_grid_iff_of_reachable hs₁] at h₂; contradiction
      · rw [mem_grid_iff_of_reachable hs₂] at h₂; contradiction
    simp at hp
    have hp₁ := mem_grid_iff_of_reachable hs₁ |>.mpr hp
    have hp₂ := mem_grid_iff_of_reachable hs₂ |>.mpr hp
    have H₁ : (↑(p.x.toFin : Fin s₀.width) : ℕ) = p.x
    · nth_rw 2 [point_eq_of_fin hp₁]; simp
      apply Int.toFin_congr; symm; exact width_eq_of_reachable hs₁; rfl
    have H₂ : (↑(p.y.toFin : Fin s₀.height) : ℕ) = p.y
    · nth_rw 2 [point_eq_of_fin hp₁]; simp
      apply Int.toFin_congr; symm; exact height_eq_of_reachable hs₁; rfl
    rw [H₁, H₂] at h₁; clear H₁ H₂ hp hp₁ hp₂
    rcases p with ⟨x, y⟩
    simp at h₁ ⊢
    constructor <;> intro h₂
    · simp [h₂] at h₁
      subst h₁
      simp
      rw [mem_grid_iff_of_reachable hs₂]
      rw [←mem_grid_iff_of_reachable hs₁]
      apply Map.mem_of_get?_eq_some h₂
    · simp [h₂] at h₁
      subst h₁
      simp
      rw [mem_grid_iff_of_reachable hs₁]
      rw [←mem_grid_iff_of_reachable hs₂]
      apply Map.mem_of_get?_eq_some h₂
  · rw [x_toFin_width_eq_iff (width_eq_of_reachable hs₁)
      (width_eq_of_reachable hs₂) player_mem player_mem] at h₂
    rw [y_toFin_width_eq_iff (height_eq_of_reachable hs₁)
      (height_eq_of_reachable hs₂) player_mem player_mem] at h₃
    ext <;> assumption
  · rw [h₄.unsolvedNum_eq, h₅.unsolvedNum_eq]
    congr 2
    ext p d
    specialize h₁ p.x.toFin p.y.toFin
    simp_rw [Map.get!_eq_get!_get?] at h₁
    constructor <;> intro h
    · have H₁ := h
      rw [←toFin_eq_of_get? hs₁ h] at H₁ ⊢
      simp [H₁] at h₁
      subst h₁
      clear H₁
      replace h := Map.mem_of_get?_eq_some h
      simp [h₄.mem_grid_iff_bounds] at h
      simp [h₅.mem_grid_iff_bounds]
      rw [width_eq_of_reachable hs₁, height_eq_of_reachable hs₁] at h
      rw [width_eq_of_reachable hs₂, height_eq_of_reachable hs₂]
      iterate 2 rw [Int.toFin_eq_toNat_of]
      all_goals omega
    · have H₁ := h
      rw [←toFin_eq_of_get? hs₂ h] at H₁ ⊢
      simp [H₁] at h₁
      subst h₁
      clear H₁
      replace h := Map.mem_of_get?_eq_some h
      simp [h₅.mem_grid_iff_bounds] at h
      simp [h₄.mem_grid_iff_bounds]
      rw [width_eq_of_reachable hs₂, height_eq_of_reachable hs₂] at h
      rw [width_eq_of_reachable hs₁, height_eq_of_reachable hs₁]
      iterate 2 rw [Int.toFin_eq_toNat_of]
      all_goals omega