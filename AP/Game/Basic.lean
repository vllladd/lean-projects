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

theorem tr_to_iff {a b} {t : T.Trans} :
game.sys.tr_to a t b ↔ a.player = t.1 ∧ ∃ r,
game.rules t.1 a.state t.2 = some r ∧ b =
{ player := r.1
, state := r.2
, hist := game.updateHist a t
} := tr_eq_some_iff

@[simp]
theorem mem_hist_initState {p' p s} : p' ∈ (T.initState p s).hist := by
  unfold GameParams.initState
  simp
  sorry

#check 0 #exit

theorem player_mem_hist_of_valid {a} [hv : game.sys.Valid a] {p} : p ∈ a.hist := by
  cases hv
  nm s hs h
  rcases hs with ⟨hs⟩
  revert hs
  induction h <;> clear s <;> intro hs
  · nm s
    obtain ⟨p', s', rfl⟩ := @game.h_sys_init_valid _ hs
    simp

#check 0 #exit

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
  rw [DMap.get!_map_eq_of_pos]
  rotate_left
  · 
  
  -- exact List.suffix_cons_of_suffix ih

#check 0 #exit

theorem acyclic_gstate {a} : game.sys.Acyclic a := by
  rw [System.acyclic_iff]
  intro b c t h₁ h₂ h₃
  replace h₁ := hist_suffix_of_reachable h₁
  replace h₃ := hist_suffix_of_reachable h₃
  rw [tr_to_iff] at h₂
  obtain ⟨h₂, ⟨p, t'⟩, h₄, rfl⟩:= h₂
  simp at h₃