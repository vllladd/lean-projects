import Projects.Sokoban.Defs

namespace Sokoban

open State

variable {s s₁ s₂ s₃ : State}

theorem get_iff {s : State} {p d} : s.Get p d ↔ s.grid.get? p = some d :=
  ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem get'_iff {s : State} {d} : s.Get' d ↔ ∃ p, s.grid.get? p = some d := by
  constructor
  · rintro ⟨h⟩; simp [get_iff] at h; exact h
  · intro h; constructor; simpa [get_iff]

theorem get?_grid_eq_some_iff {s : State} {p d} :
s.grid.get? p = some d ↔ s.Get p d := get_iff.symm

theorem State.Get.eq_of {s : State} {p d₁ d₂}
(h₁ : s.Get p d₁) (h₂ : s.Get p d₂) : d₁ = d₂ := by
  rw [get_iff] at h₁ h₂; simp [h₁] at h₂; exact h₂

theorem State.Get.get' {s : State} {p d} [hd : s.Get p d] : s.Get' d := ⟨⟨_, hd⟩⟩

theorem State.Get.wf {s : State} {p d} [hs : s.WF] [hd : s.Get p d] : d.WF :=
  hs.wf_get hd.get'

theorem State.Get'.wf {s : State} {d} [hs : s.WF] [hd : s.Get' d] : d.WF :=
  hs.wf_get hd

theorem State.Get.mem {s : State} {p d} [hd : s.Get p d] : p ∈ s.grid := by
  rw [get_iff] at hd
  rw [Map.mem_iff_get?_eq_some]
  simp [hd]

@[simp]
theorem sys_initial_iff {s} : sys.Initial s ↔ s.WF := by
  rw [System.initial_def]; rfl

theorem sys_tr_eq {s} : sys.tr s = s.move := rfl

@[simp]
theorem width_movePlayer {s : State} {p₁} :
(s.movePlayer p₁).width = s.width := rfl

@[simp]
theorem height_movePlayer {s : State} {p₁} :
(s.movePlayer p₁).height = s.height := rfl

@[simp]
theorem player_movePlayer {s : State} {p₁} :
(s.movePlayer p₁).player = p₁ := rfl

@[simp]
theorem width_moveBox {s : State} {p₁ p₂} :
(s.moveBox p₁ p₂).width = s.width := rfl

@[simp]
theorem height_moveBox {s : State} {p₁ p₂} :
(s.moveBox p₁ p₂).height = s.height := rfl

@[simp]
theorem player_moveBox {s : State} {p₁ p₂} :
(s.moveBox p₁ p₂).player = s.player := rfl

@[simp]
theorem mem_grid_movePlayer {s : State} {p₁ p} :
p ∈ (s.movePlayer p₁).grid ↔ p ∈ s.grid := by
  simp [State.movePlayer]

@[simp]
theorem mem_grid_moveBox {s : State} {p₁ p₂ p} :
p ∈ (s.moveBox p₁ p₂).grid ↔ p ∈ s.grid := by
  simp [State.moveBox]

@[simp]
theorem get?_grid_movePlayer {s : State} {p₁ p} :
(s.movePlayer p₁).grid.get? p =
(s.grid.get? p).map (λ d =>
if p₁ = p then {d with player := true}
else if s.player = p then {d with player := false}
else d) := by
  symm; simp [State.movePlayer, Map.get?_eq_ite]
  by_cases h₁ : p ∈ s.grid <;> simp [h₁]
  rw [Map.mem_iff_get?_eq_some] at h₁
  obtain ⟨d₁, h₁⟩ := h₁
  simp [Map.get!_eq_get?_get!, h₁]
  by_cases h₂ : p = p₁
  · subst h₂
    simp
    split_ifs with h₂ <;> simp
  have h₃ : p₁ ≠ p := by tauto
  simp [h₂, h₃]
  simp_rw [eq_comm (a := s.player)]
  split_ifs with h₄ <;> simp

@[simp]
theorem get?_grid_moveBox {s : State} {p₁ p₂ p} :
(s.moveBox p₁ p₂).grid.get? p =
(s.grid.get? p).map (λ d =>
if p₂ = p then {d with box := true}
else if p₁ = p then {d with box := false}
else d) := by
  symm; simp [State.moveBox, Map.get?_eq_ite]
  by_cases h₁ : p ∈ s.grid <;> simp [h₁]
  rw [Map.mem_iff_get?_eq_some] at h₁
  obtain ⟨d₁, h₁⟩ := h₁
  simp [Map.get!_eq_get?_get!, h₁]
  by_cases h₂ : p = p₂
  · subst h₂
    simp
    split_ifs with h₂ <;> simp
  have h₃ : p₂ ≠ p := by tauto
  simp [h₂, h₃]
  simp_rw [eq_comm (a := p₁)]
  split_ifs with h₄ <;> simp

@[simp]
theorem get_movePlayer {s : State} {p₁ p d} :
(s.movePlayer p₁).Get p d ↔ ∃ d', s.Get p d' ∧
(if p₁ = p then {d' with player := true}
else if s.player = p then {d' with player := false} else d') = d := by
  simp [get_iff]

@[simp]
theorem get_moveBox {s : State} {p₁ p₂ p d} :
(s.moveBox p₁ p₂).Get p d ↔ ∃ d', s.Get p d' ∧
(if p₂ = p then {d' with box := true}
else if p₁ = p then {d' with box := false} else d') = d := by
  simp [get_iff]

@[simp]
theorem unsolvedNum_move_player {s : State} {p} :
(s.movePlayer p).unsolvedNum = s.unsolvedNum := rfl

theorem moveBox_movePlayer {s : State} {p₁ p₂ p₃} :
(s.movePlayer p₁).moveBox p₂ p₃ = (s.moveBox p₂ p₃).movePlayer p₁ := by
  ext :1 <;> try simp
  · dsimp [State.movePlayer, State.moveBox]; ext; simp
    split_ifs <;> simp_all only [Option.map_map, Function.comp_def, Option.map_eq_some_iff]
  · dsimp [State.movePlayer, State.moveBox]
    split_ifs <;> simp_all [Map.get!_eq_get!_get?, Option.get!] <;> grind

theorem movePlayer_moveBox {s : State} {p₁ p₂ p₃} :
(s.moveBox p₁ p₂).movePlayer p₃ = (s.movePlayer p₃).moveBox p₁ p₂ :=
  moveBox_movePlayer.symm

theorem tr_eq_some_iff {s s' : State} (t : Move) : sys.tr s t = some s' ↔
let p_dif := t.point
let p₁ := s.player + p_dif
let p₂ := p₁ + p_dif
let s₁ := s.movePlayer p₁
∃ d₁, s.Get p₁ d₁ ∧ !d₁.wall ∧ if !d₁.box then s₁ = s'
else ∃ d₂, s.Get p₂ d₂ ∧ d₂.box = false ∧
d₂.wall = false ∧ s₁.moveBox p₁ p₂ = s' := by
  change s.move t = _ ↔ _
  simp [State.move, Map.get?_eq_ite, get_iff]
  simp only [eq_comm (b := s')]
  intro h₁ h₂
  simp [ite_eq_iff, Option.bind_ite]
  split_ifs with h₃ <;> simp [h₃]
  rotate_left; exact eq_comm
  intro h₄
  simp [and_assoc]
  intro h₅ h₆
  rw [eq_comm]
  revert s'
  simp [movePlayer_moveBox]

theorem State.Get.player_eq {s : State} {p d} [hs : s.WF] (hd : s.Get p d) :
s.player = p ↔ d.player := hs.tile_player_iff hd |>.symm

theorem State.Get.player_iff {s : State} {p d} [hs : s.WF] (hd : s.Get p d) :
d.player = decide (s.player = p) := by simp [hd.player_eq]

theorem State.Get.player_of_get_player {s : State} {d} [hs : s.WF]
(hd : s.Get s.player d) : d.player := by simp [hd.player_iff]

theorem State.Get.not_box_and_not_wall_of_get_player {s : State} {d} [hs : s.WF]
(hd : s.Get s.player d) : d.box = false ∧ d.wall = false := by
  have h₁ := hd.wf.pbw
  simp [hd.player_of_get_player] at h₁
  exact h₁

@[simp]
theorem countP_box_target_movePlayer {s : State} {p} :
List.countP (λ d => d.box && !d.target) (s.movePlayer p).grid.values =
List.countP (λ d => d.box && !d.target) s.grid.values := by
  apply Map.countP_values_modifyMany_eq_of; grind

@[simp]
theorem get?_grid_of_get {s : State} {p d} [h : s.Get p d] : s.grid.get? p = some d := h.1

@[simp]
theorem get!_grid_of_get {s : State} {p d} [h : s.Get p d] : s.grid.get! p = d := by
  simp [Map.get!_eq_get?_get!]

@[simp]
theorem mem_grid_of_get {s : State} {p d} [h : s.Get p d] : p ∈ s.grid := by
  simp [Map.mem_iff_get?_eq_some]

@[simp]
theorem points_moveBox {s : State} {p₁ p₂} : (s.moveBox p₁ p₂).points = s.points := by
  simp [moveBox, points]

@[simp]
theorem mem_points_of_get {s : State} {p d} [h : s.Get p d] : p ∈ s.points := by
  simp [points]

theorem mem_points_iff_exi_get {s : State} {p} : p ∈ s.points ↔ ∃ d, s.Get p d := by
  simp [get_iff, points, Map.mem_iff_get?_eq_some]

theorem boxes_moveBox {s : State} {p₁ p₂ d₁ d₂} [h₁ : s.Get p₁ d₁] [h₂ : s.Get p₂ d₂] :
(s.moveBox p₁ p₂).boxes = (s.boxes.erase p₁).insert p₂ := by
  ext p; simp [boxes]
  by_cases h₃ : p ∈ s.points <;> simp [h₃]
  rotate_left
  · rintro rfl; simp at h₃
  by_cases h₄ : p = p₁
  · subst h₄
    simp [moveBox, Map.get!_eq_get!_get?]
    grind
  rw [mem_points_iff_exi_get] at h₃
  choose d h₃ using h₃
  simp [ne_symm' h₄, moveBox, Map.get!_eq_get!_get?]; grind

theorem eq_of_get_and_get {s : State} {p d₁ d₂}
[h₁ : s.Get p d₁] [h₂ : s.Get p d₂] : d₁ = d₂ := by
  rw [get_iff] at h₁ h₂; simp [h₁] at h₂; exact h₂

theorem size_boxes_moveBox {s : State} {p₁ p₂ d₁ d₂} [h₁ : s.Get p₁ d₁] [h₂ : s.Get p₂ d₂]
(h₃ : d₁.box) (h₄ : d₂.box = false) : (s.moveBox p₁ p₂).boxes.size = s.boxes.size := by
  simp [boxes_moveBox]
  by_cases h₅ : p₁ = p₂
  · subst h₅
    simp
    rw[Set'.insert_eq_of_mem]
    obtain rfl := @eq_of_get_and_get s _ _ _ h₁ h₂
    simpa [boxes]
  by_cases h₆ : p₁ ∈ s.boxes
  · rw [Set'.size_insert # by simpa [h₅, boxes]]
    rw [Set'.size_erase h₆]
    rw [Nat.sub_add_cancel]
    simp [boxes]
    use p₁
    simpa
  simp [h₃, boxes] at h₆

@[simp]
theorem points_movePlayer {s : State} {p} : (s.movePlayer p).points = s.points := by
  ext; simp [points]

@[simp]
theorem box_get!_grid_movePlayer {s : State} {p p₁} :
(s.movePlayer p |>.grid.get! p₁).box = (s.grid.get! p₁).box := by
  simp [movePlayer, Map.get!_eq_get!_get?, Option.get!]; grind

@[simp]
theorem boxes_movePlayer {s : State} {p} : (s.movePlayer p).boxes = s.boxes := by
  ext; simp [boxes]

@[simp]
theorem target_get!_grid_movePlayer {s : State} {p p₁} :
(s.movePlayer p |>.grid.get! p₁).target = (s.grid.get! p₁).target := by
  simp [movePlayer, Map.get!_eq_get!_get?, Option.get!]; grind

@[simp]
theorem targets_movePlayer {s : State} {p} : (s.movePlayer p).targets = s.targets := by
  ext; simp [targets]

@[simp]
theorem target_get!_grid_moveBox {s : State} {p₁ p₂ p} :
(s.moveBox p₁ p₂ |>.grid.get! p).target = (s.grid.get! p).target := by
  simp [moveBox, Map.get!_eq_get!_get?, Option.get!]; grind

@[simp]
theorem targets_moveBox {s : State} {p₁ p₂} : (s.moveBox p₁ p₂).targets = s.targets := by
  ext; simp [targets]

theorem sys_wf_iff {s} : sys.WF s ↔ s.WF := by
  symm; constructor
  · simp [sys.wf_def]; intro h; use s
  intro h
  apply sys.invariant_wf h; simp
  clear! s
  intro s s' t hs hs' h₁ h₂
  simp [tr_eq_some_iff] at h₂
  obtain ⟨d₁, h₂, h₃, h₄⟩ := h₂
  split_ifs at h₄ with h₅
  · obtain ⟨d₂, h₄, h₆, h₇, rfl⟩ := h₄
    constructor
    · simp; exact h₁.mem_grid_iff_bounds
    · intro d ⟨p, hd⟩
      simp at hd
      obtain ⟨d₃, H₁, H₂⟩ := hd
      split_ifs at H₂
      · nm H₃ H₄; simp [←H₃] at H₄
      · nm H₃ H₄ H₅; simp [←H₃, add_assoc] at H₅
      · subst H₂
        nm H₂ H₃ H₄
        rw [H₂] at h₄
        replace H₁ := h₄.eq_of H₁; subst H₁
        rw [h₄.player_eq] at H₄
        constructor <;> simp [h₇, H₄]
      · simp at H₂; subst H₂
        nm H₂ H₃; subst H₃
        replace H₁ := h₂.eq_of H₁; subst H₁
        constructor <;> simp [h₃]
      · nm H₃ H₄ H₅
        subst H₂ H₅
        constructor <;> simp [H₁.not_box_and_not_wall_of_get_player]
      · subst H₂; exact H₁.wf
    · simp
    · simp; intro p d hp
      split_ifs
      · nm H₁ H₂; simp [←H₁] at H₂
      · nm H₁ H₂ H₃; simp [H₃, add_assoc] at H₁
      · nm H₁ H₂ H₃
        rw [H₁] at h₄
        replace hp := h₄.eq_of hp; subst hp
        simp [←H₁]
        simpa [h₄.player_iff]
      · nm H₁ H₂; clear H₁; rw [H₂] at h₂; simpa
      · nm H₁ H₂ H₃; clear H₁ H₂; simp [H₃]
      · nm H₁ H₂ H₃; simpa [H₂, hp.player_iff]
    · simp [moveBox_movePlayer]
      simp [moveBox, h₁.unsolvedNum_eq]
      rw [Map.countP_values_modify_eq_ite_of_get? # by simp; rfl]
      rw [Map.countP_values_modify_eq_ite_of_get? # by simp; rfl]
      simp [h₅, h₆]
      simp_all only [sys_initial_iff, System.instWFOfInitial]
      split
      next h =>
        simp_all only [tsub_zero]
        split
        next h_1 => simp_all only [add_tsub_cancel_right, add_zero]
        next h_1 => simp_all only [Bool.not_eq_true, tsub_zero]
      next h =>
        simp_all only [Bool.not_eq_true, add_zero]
        split
        next h_1 => simp_all only [add_zero]
        next h_1 =>
          simp_all only [Bool.not_eq_true, tsub_zero]
          rw [Nat.sub_add_cancel]
          simp; exact ⟨d₁, ⟨s.player + t.point, by simp⟩, h₅, h⟩
    · simp [moveBox_movePlayer]
      rwa [size_boxes_moveBox _ h₆, h₁.size_boxes_eq_size_targets]
  subst h₄
  constructor;
  · simp; exact h₁.mem_grid_iff_bounds
  · intro d₂ ⟨p, h₆⟩
    simp at h₆
    obtain ⟨d₃, hp, hp₁⟩ := h₆
    split_ifs at hp₁ <;> subst hp₁
    · nm H₁; subst H₁
      replace hp := h₂.eq_of hp; subst hp
      constructor <;> simp [h₃, h₅]
    · nm H₁ H₂; subst H₂
      constructor <;> simp [hp.not_box_and_not_wall_of_get_player]
    · exact hp.wf
  · simp
  · intro p d hp
    simp at hp
    obtain ⟨d₂, hp, hp₁⟩ := hp
    split_ifs at hp₁ <;> subst hp₁ <;> simp
    any_goals assumption
    nm H₁ H₂; simpa [H₁, hp.player_iff]
  · simp [h₁.unsolvedNum_eq]
  · simp [h₁.size_boxes_eq_size_targets]

theorem wf_of_reachable {s s' : State} [hs : s.WF]
(hr : sys.Reachable s s') : s'.WF := by
  rw [←sys_wf_iff, sys.wf_def] at hs ⊢
  obtain ⟨s₀, h₁, h₂⟩ := hs
  use s₀, h₁, h₂.trans hr

@[simp]
theorem player_mem {s : State} [hs : s.WF] : s.player ∈ s.grid :=
  hs.player_mem

theorem width_ne_zero {s : State} [hs : s.WF] : s.width ≠ 0 := by
  intro h₁; have h₂ := hs.player_mem; rw [hs.mem_grid_iff_bounds] at h₂; linarith

theorem height_ne_zero {s : State} [hs : s.WF] : s.height ≠ 0 := by
  intro h₁; have h₂ := hs.player_mem; rw [hs.mem_grid_iff_bounds] at h₂; linarith

instance {s : State} [hs : s.WF] : NeZero s.width := ⟨width_ne_zero⟩
instance {s : State} [hs : s.WF] : NeZero s.height := ⟨height_ne_zero⟩

theorem width_and_height_eq_of_reachable {s₀ s : State} [hs₀ : s₀.WF]
(h : sys.Reachable s₀ s) : s.width = s₀.width ∧ s.height = s₀.height := by
  rw [←Prod.mk.injEq]
  have hs₀ : sys.WF s₀; rwa [sys_wf_iff]
  apply sys.invariant_val h
  intro x y t hx hy h₁
  simp [tr_eq_some_iff] at h₁
  obtain ⟨d₁, h₁, h₂, h₃⟩ := h₁
  split_ifs at h₃ with h₄
  · obtain ⟨d₂, h₃, h₅, h₆, h₇⟩ := h₃; simp [←h₇]
  · simp [←h₃]

theorem width_eq_of_reachable {s₀ s : State} [hs₀ : s₀.WF]
(h : sys.Reachable s₀ s) : s.width = s₀.width :=
  width_and_height_eq_of_reachable h |>.1

theorem height_eq_of_reachable {s₀ s : State} [hs₀ : s₀.WF]
(h : sys.Reachable s₀ s) : s.height = s₀.height :=
  width_and_height_eq_of_reachable h |>.2

theorem mem_grid_iff_of_reachable {s₀ s : State} [hs₀ : s₀.WF] {p}
(h : sys.Reachable s₀ s) : p ∈ s.grid ↔ p ∈ s₀.grid := by
  have hs := wf_of_reachable h
  rw [hs₀.mem_grid_iff_bounds, hs.mem_grid_iff_bounds, width_eq_of_reachable h,
    height_eq_of_reachable h]

theorem targets_eq_of_tr {s s' p}
(h : sys.tr s p = some s') : s'.targets = s.targets := by
  simp [tr_eq_some_iff] at h
  choose d₁ h₁ h₂ h₃ using h
  split_ifs at h₃ with h₄
  · choose d₂ h₃ h₅ h₆ h₇ using h₃
    subst h₇
    simp
  · subst h₃
    simp

theorem targets_eq_of_reachable {s s'} [hs : sys.WF s]
(h : sys.Reachable s s') : s'.targets = s.targets :=
  sys.invariant_val h targets_eq_of_tr

theorem size_boxes_eq_of_tr {s s' p}
(h : sys.tr s p = some s') : s'.boxes.size = s.boxes.size := by
  simp [tr_eq_some_iff] at h
  choose d₁ h₁ h₂ h₃ using h
  split_ifs at h₃ with h₄
  · choose d₂ h₃ h₅ h₆ h₇ using h₃
    subst h₇
    simp [moveBox_movePlayer]
    exact size_boxes_moveBox h₄ h₅
  · subst h₃
    simp

theorem size_boxes_eq_of_reachable {s s'} [hs : sys.WF s]
(h : sys.Reachable s s') : s'.boxes.size = s.boxes.size :=
  sys.invariant_val h size_boxes_eq_of_tr

theorem mem_points_of_mem_boxes {p} (h : p ∈ s.boxes) : p ∈ s.points := by
  simp [boxes] at h; exact h.1