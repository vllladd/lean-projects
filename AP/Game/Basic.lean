import AP.Game.Defs

open Util.Data

namespace Game

universe u
variable {T : GameParams.{u}} {game : Game T}

theorem tr_eq_some_iff {a b} {t : T.Trans} :
game.sys.tr a t = some b ↔ a.player = t.1 ∧ ∃ p s',
game.rules t.1 a.state t.2 = some ⟨p, s'⟩ ∧ b =
{ player := p
, state := s'
, hist := game.updateHist a t
} := by
  simp only [game.h_sys_tr, GameParams.sys_tr, GameParams.updateHist,
    ite_not, Option.bind_eq_bind, Option.bind, Option.dite_none_right_eq_some,
    updateHist, Prod.exists]
  constructor
  · rintro ⟨h₁, h₂⟩
    use h₁
    split at h₂ <;> simp at h₂
    nm x y z h₃
    use z.1, z.2
    simp [h₁, h₂, h₃]
  · rintro ⟨h₁, p, s', h₂, rfl⟩
    use h₁
    simp [h₁, h₂]

theorem trTo_iff {a b} {t : T.Trans} :
game.sys.trTo a t b ↔ a.player = t.1 ∧ ∃ p s',
game.rules t.1 a.state t.2 = some ⟨p, s'⟩ ∧ b =
{ player := p
, state := s'
, hist := game.updateHist a t
} := tr_eq_some_iff

@[simp]
theorem mem_hist_initState {ps p s p'} :
p' ∈ (T.initState ps p s).hist ↔ p' ∈ ps := by
  simp [GameParams.initState]

@[simp]
theorem player_mem_updateHist_iff {p s t} :
p ∈ game.updateHist s t ↔ p ∈ s.hist := by
  unfold updateHist GameParams.updateHist
  split_ifs with h₁
  · simp
  rfl

theorem mem_hist_iff_of_reachable {a b p} (hv : game.sys.Reachable a b) :
p ∈ b.hist ↔ p ∈ a.hist := by
  classical
  replace hv := System.exi_trs_of_reachable hv
  obtain ⟨ts, h⟩ := hv
  induction ts using List.reverseRecOn generalizing b
  · simp at h
    rw [h]
  nm ts t ih
  simp [System.trs_append] at h
  iterate split at h
  all_goals simp at h
  nm h₁ x d h₂
  rcases h with ⟨rfl, h⟩
  clear h₁
  generalize hr : game.sys.trs a ts = r at h h₂
  rcases r with ⟨c, r⟩
  subst h
  dsimp at h₂
  specialize ih hr
  simp only [←ih]; clear ih
  rw [tr_eq_some_iff] at h₂
  obtain ⟨h₂, p, s', h₃, h₄, rfl⟩ := h₂
  simp

theorem mem_hist_of_reachable {a b p} (hv : game.sys.Reachable a b)
(h : p ∈ a.hist) : p ∈ b.hist := by
  rwa [game.mem_hist_iff_of_reachable hv]

theorem mem_hist_of_reachable' {a b p} (hv : game.sys.Reachable a b)
(h : p ∈ b.hist) : p ∈ a.hist := by
  rw [game.mem_hist_iff_of_reachable hv] at h; exact h

theorem hist_suffix_of_reachable {a} [hv : game.sys.Valid a] {b p}
(h : game.sys.Reachable a b) (hp : p ∈ b.hist) :
a.hist.get! p <:+ b.hist.get! p := by
  revert hv
  induction h using System.reachable_ind_right
  · intro hv
    rfl
  clear a b
  nm a b c t h₁ h₂ ih
  intro hv
  have hb₁ : p ∈ b.hist :=
    by
      replace h₂ := System.reachable_of_tr h₂
      exact mem_hist_of_reachable' h₂ hp
  specialize @ih hb₁
  rw [tr_eq_some_iff] at h₂
  rcases h₂ with ⟨h₂, p', c, h₃, h₄, rfl⟩
  simp [Game.updateHist, GameParams.updateHist, h₂]
  have hb := System.valid_of_reachable h₁
  rw [DMap.get!_map_eq_of_pos]
  rotate_left; exact hb₁
  exact List.suffix_cons_of_suffix ih

theorem exi_mem_hist_of_valid {a} [ha : game.sys.Valid a] : ∃ p, p ∈ a.hist := by
  rw [System.valid_iff] at ha
  obtain ⟨z, h₁, h₂⟩ := ha
  obtain ⟨ps, p', s', rfl, h₄⟩ := game.h_sys_init_valid z
  simp [GameParams.initState] at h₄
  simp [Util.Data.Set.eq_empty_iff] at h₄
  obtain ⟨p, hx⟩ := h₄
  use p
  apply mem_hist_of_reachable h₂
  simpa

theorem acyclic_gstate {a} [ha : game.sys.Valid a] : game.sys.Acyclic a := by
  rw [System.acyclic_iff]
  intro b c t h₁ h₂ h₃
  have hb := System.valid_of_reachable h₁
  have hc : game.sys.Valid c :=
    by
      apply System.valid_of_reachable (a := a)
      exact System.reachable_right h₁ h₂
  rw [tr_eq_some_iff] at h₂
  obtain ⟨h₂, p, t', h₄, h₅, rfl⟩:= h₂
  have hp := game.h_rules_player_mem h₄
  replace h₁ := hist_suffix_of_reachable h₁ hp
  replace h₃ := hist_suffix_of_reachable h₃ hp
  simp [updateHist, h₂, GameParams.updateHist] at h₃
  rw [DMap.get!_map_eq_of_pos hp] at h₃
  simp at h₃

theorem validTr_iff {a} {t : T.Trans} :
game.sys.validTr a t ↔ a.player = t.1 ∧
∃ r, game.rules t.1 a.state t.2 = some r := by
  simp only [System.validTr, System.trTo, tr_eq_some_iff, exists_and_left,
    Prod.exists, and_congr_right_iff]
  intro h
  constructor
  · rintro ⟨b, p, s, h₁, rfl⟩
    simp [h₁, ←h]
  · rintro ⟨p, s, h₁⟩
    simp [h₁]

theorem hasTr_iff_exi_rules_ap_isSome {s : T.GState} :
game.sys.hasTr s ↔ (∃ t, (game.rules s.player s.state t).isSome) := by
  simp only [System.hasTr, validTr_iff]
  constructor
  · rintro ⟨⟨p, t⟩, rfl, r, h₂⟩
    dsimp at h₂
    use t
    simp [h₂]
  · rintro ⟨t, h₁⟩
    refine' ⟨⟨_, t⟩, rfl, _⟩
    rw [Option.isSome_iff_exists] at h₁
    exact h₁

instance : Nonempty T.GState := by
  have h₁ := game.h_sys_init_nemp
  simp [Set.eq_empty_iff] at h₁
  obtain ⟨s, h₁⟩ := h₁
  exact ⟨s⟩