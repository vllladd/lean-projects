import AP.Sokoban.Defs

namespace Sokoban

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
  if p = p₁ then {d with player := true}
  else if p = s.player then {d with player := false}
  else d
) := by
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
  if p = p₂ then {d with box := true}
  else if p = p₁ then {d with box := false}
  else d
) := by
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
∃ d₁, s.grid.get? p₁ = some d₁ ∧ !d₁.wall ∧ if !d₁.box then s' = s₁
else ∃ d₂, s.grid.get? p₂ = some d₂ ∧ d₂.box = false ∧
d₂.wall = false ∧ s' = s₁.moveBox p₁ p₂ := by
  simp [State.move, Map.get?_eq_ite]
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

theorem sys_valid_iff {s} : sys.Valid s ↔ s.Valid := by
  symm; constructor
  · simp [System.valid_iff]; intro h; use s
  intro h
  apply sys.invariant_init h; simp
  clear! s; intro s s' t h₁ h₂
  simp at h₂
  obtain ⟨d₁, h₂, h₃, h₄⟩ := h₂
  split_ifs at h₄ with h₅
  · obtain ⟨d₂, h₄, h₆, h₇, rfl⟩ := h₄
    constructor
    · simp; exact h₁.1
    · intro d hd
      rw [Map.mem_values] at hd
      simp at hd
      obtain ⟨p, d₃, hd₁, hd₂⟩ := hd
      split_ifs at hd₂
      · nm hd₃ hd₄
        subst hd₃
        cases hsp : s.player
        simp [hsp] at hd₄
        cases t <;> simp [Move.toPoint] at hd₄
      · nm hd₃ hd₄ hd₅
        rw [hd₃, add_assoc] at hd₅
        cases t <;> simp [Move.toPoint] at hd₅
      · subst hd₂
        nm hd₂ hd₃ hd₄
        rw [←hd₂] at h₄
        simp [h₄] at hd₁
        subst hd₁
        have h₈ : d₂.player = false := by
          rcases h₁ with ⟨h₁, h₈, h₉⟩
          specialize h₉ p
          rw [Map.mem_iff_get?_eq_some, Map.get!_eq_get?_get!] at h₉
          rw [eq_comm] at hd₄
          simp [hd₄, h₄] at h₉
          exact h₉
        constructor <;> simp [h₇, h₈]
        cases d₂.target <;> rfl
      · nm hd₃ hd₄
        simp at hd₂
        subst hd₂
        clear hd₃
        subst hd₄
        simp [h₂] at hd₁
        subst hd₁
        constructor <;> simp [h₃]
        cases d₁.target <;> rfl
      · nm hd₃ hd₄ hd₅
        clear hd₃ hd₄
        subst hd₅
        subst hd₂
        rcases h₁ with ⟨h₁, h₈, h₉⟩
        specialize h₉ s.player
        simp [Map.mem_iff_get?_eq_some, Map.get!_eq_get?_get!, hd₁] at h₉
        specialize h₈ d₃
        simp at h₈
        specialize h₈ _ hd₁
        rcases h₈ with ⟨h₈, h₁₀⟩
        constructor <;> simp [h₁₀]
        simp [h₉] at h₈
        simp [h₈]
      · subst hd₂
        replace h₁ := h₁.2
        specialize h₁ d₃
        simp at h₁
        exact h₁ p hd₁
    · simp
      intro p hp
      simp [Map.get!_eq_get?_get!]
      split_ifs
      · nm hd₁ hd₂
        simp [hd₁] at hd₂
        cases t <;> simp [Move.toPoint] at hd₂
      · nm hd₁ hd₂ hd₃
        subst hd₃
        simp [add_assoc] at hd₁
        cases t <;> simp [Move.toPoint] at hd₁
      · nm hd₁ hd₂ hd₃
        clear hd₂ hd₃
        rw [←hd₁] at h₄
        simp [h₄]
        have hx : t.toPoint ≠ 0 :=
          by
            cases t <;> simp [Move.toPoint]
        simp at hx
        rw [imp_iff_not_or, ←not_and_iff_or] at hx
        simp [hd₁, hx]
        replace h₁ := h₁.3
        specialize h₁ p
        simp [Map.mem_iff_get?_eq_some, Map.get!_eq_get?_get!, h₄] at h₁
        by_contra h₂
        simp [h₁] at h₂
        simp [h₂, add_assoc] at hd₁
        cases t <;> simp [Move.toPoint] at hd₁
      · nm hd₁ hd₂; clear hd₁
        rw [←hd₂] at h₂
        simp [h₂]
        exact hd₂.symm
      · nm hd₁ hd₂ hd₃; clear hd₁ hd₂
        rw [Map.mem_iff_get?_eq_some] at hp
        obtain ⟨d, hp⟩ := hp
        simp [hp]
        simp [hd₃]
        cases t <;> simp [Move.toPoint]
      · nm hd₁ hd₂ hd₃
        rw [Map.mem_iff_get?_eq_some] at hp
        obtain ⟨d, hp⟩ := hp
        simp [hp]
        replace h₁ := h₁.3 p
        simp [Map.mem_iff_get?_eq_some, Map.get!_eq_get?_get!, hp] at h₁
        rw [h₁, eq_comm]
        simp [hd₃]
        rintro rfl
        simp at hd₂
  subst h₄
  constructor <;> simp; exact h₁.1
  · intro d₂ p d₃ h₆ h₇
    split_ifs at h₇
    · nm hd₁
      rw[←hd₁] at h₂
      simp [h₂] at h₆
      subst h₆
      subst h₇
      constructor <;> simp [h₃, h₅]
      cases d₁.target <;> rfl
    · nm hd₁ hd₂; subst hd₂ h₇
      have hx := h₁.2 d₃
      simp at hx
      specialize hx _ h₆
      rcases hx with ⟨hd₂, hd₃⟩
      constructor <;> simp
      rotate_left; exact hd₃
      replace h₁ := h₁.3 s.player
      simp [Map.mem_iff_get?_eq_some, Map.get!_eq_get?_get!, h₆] at h₁
      simp [h₁] at hd₂
      simp [hd₂]
    · nm hd₁ hd₂
      subst h₇
      apply h₁.2
      simp
      use p
  · intro p hp
    simp [Map.get!_eq_get?_get!]
    rw [Map.mem_iff_get?_eq_some] at hp
    obtain ⟨d, hp⟩ := hp
    simp [hp]
    split_ifs
    · nm hd₁; simp [hd₁]
    · nm hd₁ hd₂
      simp
      rwa [eq_comm]
    · nm hd₁ hd₂
      rw [eq_comm] at hd₁ hd₂
      simp [hd₁]
      replace h₁ := h₁.3 p
      simp [Map.mem_iff_get?_eq_some, Map.get!_eq_get?_get!, hp, hd₂] at h₁
      exact h₁