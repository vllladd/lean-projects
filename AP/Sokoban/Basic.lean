import AP.Sokoban.Defs

namespace Sokoban

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

theorem State.Get.get' {s : State} {p d} (hd : s.Get p d) : s.Get' d := ⟨⟨_, hd⟩⟩

theorem State.Get.valid {s : State} {p d} [hs : s.Valid] (hd : s.Get p d) : d.Valid :=
  hs.h_grid hd.get'

theorem State.Get'.valid {s : State} {d} [hs : s.Valid] (hd : s.Get' d) : d.Valid :=
  hs.h_grid hd

theorem State.Get.mem {s : State} {p d} (hd : s.Get p d) : p ∈ s.grid := by
  rw [get_iff] at hd
  rw [Map.mem_iff_get?_eq_some]
  simp [hd]

@[simp]
theorem sys_initial_iff {s} : sys.Initial s ↔ s.Valid := by
  rw [System.initial_iff]; rfl

@[simp]
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

theorem movePlayer_moveBox {s : State} {p₁ p₂ p₃} :
(s.moveBox p₁ p₂).movePlayer p₃ = (s.movePlayer p₃).moveBox p₁ p₂ := by
  ext:1 <;> try simp
  ext:1; nm p
  simp [Map.get?_eq_ite]
  split_ifs with h₁ <;> simp
  rw [Map.mem_iff_get?_eq_some] at h₁
  rcases h₁ with ⟨d, hd⟩
  simp [Map.get!_eq_get?_get!, hd]
  split_ifs <;> simp

theorem moveBox_movePlayer {s : State} {p₁ p₂ p₃} :
(s.movePlayer p₁).moveBox p₂ p₃ = (s.moveBox p₂ p₃).movePlayer p₁ := by
  ext:1 <;> try simp
  ext:1; nm p
  simp [Map.get?_eq_ite]
  split_ifs with h₁ <;> simp
  rw [Map.mem_iff_get?_eq_some] at h₁
  rcases h₁ with ⟨d, hd⟩
  simp [Map.get!_eq_get?_get!, hd]
  split_ifs <;> simp

@[simp]
theorem move_eq_some_iff {s s' : State} (t : Move) : s.move t = some s' ↔
let p_dif := t.toPoint
let p₁ := s.player + p_dif
let p₂ := p₁ + p_dif
let s₁ := s.movePlayer p₁
∃ d₁, s.Get p₁ d₁ ∧ !d₁.wall ∧ if !d₁.box then s₁ = s'
else ∃ d₂, s.Get p₂ d₂ ∧ d₂.box = false ∧
d₂.wall = false ∧ s₁.moveBox p₁ p₂ = s' := by
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

@[simp]
theorem Move.toPoint_ne_zero {t : Move} : t.toPoint ≠ 0 := by
  cases t <;> decide

theorem State.Get.player_eq {s : State} {p d} [hs : s.Valid] (hd : s.Get p d) :
s.player = p ↔ d.player := hs.h_player_iff hd |>.symm

theorem State.Get.player_iff {s : State} {p d} [hs : s.Valid] (hd : s.Get p d) :
d.player = decide (s.player = p) := by simp [hd.player_eq]

theorem State.Get.player_of_get_player {s : State} {d} [hs : s.Valid]
(hd : s.Get s.player d) : d.player := by simp [hd.player_iff]

theorem State.Get.not_box_and_not_wall_of_get_player {s : State} {d} [hs : s.Valid]
(hd : s.Get s.player d) : d.box = false ∧ d.wall = false := by
  have h₁ := hd.valid.h_pbw
  simp [hd.player_of_get_player] at h₁
  exact h₁

theorem sys_valid_iff {s} : sys.Valid s ↔ s.Valid := by
  symm; constructor
  · simp [System.valid_iff]; intro h; use s
  intro h
  apply sys.invariant_init h; simp
  clear! s; intro s s' t hs h₂
  simp at h₂
  obtain ⟨d₁, h₂, h₃, h₄⟩ := h₂
  split_ifs at h₄ with h₅
  · obtain ⟨d₂, h₄, h₆, h₇, rfl⟩ := h₄
    constructor
    · simp; exact hs.h_bounds
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
      · subst H₂; exact H₁.valid
    · simp; exact h₂.mem
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
  subst h₄
  constructor;
  · simp; exact hs.h_bounds
  · intro d₂ ⟨p, h₆⟩
    simp at h₆
    obtain ⟨d₃, hp, hp₁⟩ := h₆
    split_ifs at hp₁ <;> subst hp₁
    · nm H₁; subst H₁
      replace hp := h₂.eq_of hp; subst hp
      constructor <;> simp [h₃, h₅]
    · nm H₁ H₂; subst H₂
      constructor <;> simp [hp.not_box_and_not_wall_of_get_player]
    · exact hp.valid
  · simp; exact h₂.mem
  · intro p d hp
    simp at hp
    obtain ⟨d₂, hp, hp₁⟩ := hp
    split_ifs at hp₁ <;> subst hp₁ <;> simp
    any_goals assumption
    nm H₁ H₂; simpa [H₁, hp.player_iff]

theorem valid_of_reachable {s s' : State} [hs : s.Valid]
(hr : sys.Reachable s s') : s'.Valid := by
  rw [←sys_valid_iff, sys.valid_iff] at hs ⊢
  obtain ⟨s₀, h₁, h₂⟩ := hs
  use s₀, h₁, h₂.trans hr

theorem width_ne_zero {s : State} [hs : s.Valid] : s.width ≠ 0 := by
  intro h₁; have h₂ := hs.h_player_mem; rw [hs.h_bounds] at h₂; linarith

theorem height_ne_zero {s : State} [hs : s.Valid] : s.height ≠ 0 := by
  intro h₁; have h₂ := hs.h_player_mem; rw [hs.h_bounds] at h₂; linarith

instance {s : State} [hs : s.Valid] : NeZero s.width := ⟨width_ne_zero⟩
instance {s : State} [hs : s.Valid] : NeZero s.height := ⟨height_ne_zero⟩

theorem width_and_height_eq_of_reachable {s₀ s : State}
(h : sys.Reachable s₀ s) : s.width = s₀.width ∧ s.height = s₀.height := by
  rw [←Prod.mk.injEq]
  apply sys.invariant_val h
  intro x y t h₁
  simp at h₁
  obtain ⟨d₁, h₁, h₂, h₃⟩ := h₁
  split_ifs at h₃ with h₄
  · obtain ⟨d₂, h₃, h₅, h₆, h₇⟩ := h₃; simp [←h₇]
  · simp [←h₃]

@[simp]
theorem player_mem {s : State} [hs : s.Valid] : s.player ∈ s.grid :=
  hs.h_player_mem

theorem width_eq_of_reachable {s₀ s : State}
(h : sys.Reachable s₀ s) : s.width = s₀.width :=
  width_and_height_eq_of_reachable h |>.1

theorem height_eq_of_reachable {s₀ s : State}
(h : sys.Reachable s₀ s) : s.height = s₀.height :=
  width_and_height_eq_of_reachable h |>.2

theorem mem_grid_iff_of_reachable {s₀ s : State} [hs₀ : s₀.Valid] {p}
(h : sys.Reachable s₀ s) : p ∈ s.grid ↔ p ∈ s₀.grid := by
  have hs := valid_of_reachable h
  rw [hs₀.h_bounds, hs.h_bounds, width_eq_of_reachable h, height_eq_of_reachable h]