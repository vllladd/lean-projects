import AP.Game.Defs

namespace Game

universe u
variable {T : GameParams.{u}} {game : Game T}

theorem tr_eq_some_iff {a b} {t : T.Trans} :
game.sys.tr a t = some b ↔ a.player = t.1 ∧ ∃ r,
game.rules t.1 a.state t.2 = some r ∧ b =
{ player := r.1
, state := r.2
, hist := game.updateHist a t
} := by
  simp only [game.h_sys_tr, GameParams.sys_tr, GameParams.updateHist,
    Option.bind_eq_bind, Option.bind, Option.dite_none_right_eq_some,
    updateHist, Prod.exists]
  constructor
  · rintro ⟨h₁, h₂⟩
    use h₁
    split at h₂ <;> simp at h₂
    nm x y z h₃
    use z.1, z.2
    simp [h₁, h₂, h₃]
  · rintro ⟨h₁, x, y, h₂, rfl⟩
    use h₁
    simp [h₁, h₂]

theorem trTo_iff {a b} {t : T.Trans} :
game.sys.trTo a t b ↔ a.player = t.1 ∧ ∃ r,
game.rules t.1 a.state t.2 = some r ∧ b =
{ player := r.1
, state := r.2
, hist := game.updateHist a t
} := tr_eq_some_iff

@[simp]
theorem player_mem_hist_initState {p' p s} : p' ∈ (T.initState p s).hist := by
  simp [GameParams.initState]

theorem player_mem_hist_of_initial {p s} [h : game.sys.Initial s] : p ∈ s.hist := by
  obtain ⟨p', s', rfl⟩ := game.h_sys_init_valid s
  simp

@[simp]
theorem player_mem_updateHist_iff {p s t} :
p ∈ game.updateHist s t ↔ p ∈ s.hist := by
  unfold updateHist GameParams.updateHist
  split_ifs with h₁
  · simp
  rfl

theorem player_mem_hist_of_valid {a} [hv : game.sys.Valid a] {p} : p ∈ a.hist := by
  classical
  cases hv
  nm s hs h
  rw [System.reachable_iff_exi_trs] at h
  obtain ⟨ts, h₁⟩ := h
  induction ts using List.reverseRecOn generalizing a
  · simp at h₁
    subst h₁
    exact game.player_mem_hist_of_initial
  nm ts t ih
  simp [System.trs_append] at h₁
  iterate split at h₁ <;> simp at h₁
  nm h₂ x s' h₃; clear x
  rcases h₁ with ⟨rfl, h₁⟩; clear h₁
  generalize hb : game.sys.trs s ts = b at h₂ h₃
  specialize @ih b.1 _
  · simp [Prod.eq_iff_fst_eq_snd_eq, hb, h₂]
  generalize b.1 = c at h₃ ih
  clear! b
  rw [tr_eq_some_iff] at h₃
  obtain ⟨h₁, r, h₂, h₃, rfl⟩ := h₃
  simpa

theorem hist_suffix_of_reachable {a} [hv : game.sys.Valid a] {b p}
(h : game.sys.Reachable a b) : a.hist.get! p <:+ b.hist.get! p := by
  revert hv
  induction h using System.reachable_ind_right
  · intro hv
    rfl
  clear a b
  nm a b c t h₁ h₂ ih
  intro hv
  specialize @ih _
  rw [tr_eq_some_iff] at h₂
  rcases h₂ with ⟨h₂, ⟨p', c⟩, h₃, rfl⟩
  simp [Game.updateHist, GameParams.updateHist, h₂]
  have hb := System.valid_of_reachable h₁
  rw [DMap.get!_map_eq_of_pos]
  rotate_left
  · exact game.player_mem_hist_of_valid
  exact List.suffix_cons_of_suffix ih

theorem acyclic_gstate {a} [ha : game.sys.Valid a] : game.sys.Acyclic a := by
  rw [System.acyclic_iff]
  intro b c t h₁ h₂ h₃
  generalize (default : T.Player) = p
  have hb := System.valid_of_reachable h₁
  have hc : game.sys.Valid c :=
    by
      apply System.valid_of_reachable (a := a)
      exact System.reachable_right h₁ h₂
  replace h₁ := hist_suffix_of_reachable (p := p) h₁
  replace h₃ := hist_suffix_of_reachable (p := p) h₃
  rw [tr_eq_some_iff] at h₂
  obtain ⟨h₂, ⟨p', t'⟩, h₄, rfl⟩:= h₂
  simp at h₃
  clear! p'
  simp [updateHist, h₂, GameParams.updateHist] at h₃
  rw [DMap.get!_map_eq_of_pos game.player_mem_hist_of_valid] at h₃
  simp at h₃

theorem validTr_iff {a} {t : T.Trans} :
game.sys.validTr a t ↔ a.player = t.fst ∧
∃ r, game.rules t.1 a.state t.2 = some r := by
  simp only [System.validTr, System.trTo, tr_eq_some_iff, Prod.exists,
    exists_and_left, and_congr_right_iff]; tauto

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
    rwa [←Option.isSome_iff_exists]

instance : Nonempty T.GState := by
  have h₁ := game.h_sys_init_nemp
  simp [Set.eq_empty_iff] at h₁
  obtain ⟨s, h₁⟩ := h₁
  exact ⟨s⟩