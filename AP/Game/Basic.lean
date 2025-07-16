import AP.Game.Defs

namespace Game

universe u
variable {T : GameParams.{u}} {game : Game T}

theorem tr_eq_some_iff {a b} {t : T.Trans} :
game.sys.tr a t = some b ↔ a.player = t.1 ∧ ∃ r,
game.rules t.1 a.state t.2 = some r ∧ b =
{ player := r.1
, state := r.2
, hist := t :: a.hist
} := by
  simp [game.h_sys_tr, GameParams.sys_tr, Option.bind]
  split
  · nm x y h₁
    simp
    rintro hp p s h₂ rfl
    simp [h₁] at h₂
  nm x y z h₁
  simp
  intro hp
  constructor
  · rintro ⟨h₂, rfl⟩
    use z.1, z.2
  · rintro ⟨u, v, h₂, h₃⟩
    simp [h₁] at h₂
    subst h₂
    exact h₃.symm

theorem tr_to_iff {a b} {t : T.Trans} :
game.sys.tr_to a t b ↔ a.player = t.1 ∧ ∃ r,
game.rules t.1 a.state t.2 = some r ∧ b =
{ player := r.1
, state := r.2
, hist := t :: a.hist
} := tr_eq_some_iff

theorem hist_suffix_of_reachable {a b}
(h : game.sys.Reachable a b) : a.hist <:+ b.hist := by
  induction h using System.reachable_ind_right
  · rfl
  clear a b
  nm a b c t h₁ h₂ ih
  rw [tr_eq_some_iff] at h₂
  rcases h₂ with ⟨h₂, ⟨p, c⟩, h₃, rfl⟩
  simp
  exact List.suffix_cons_of_suffix ih

theorem acyclic_gstate {a} : game.sys.Acyclic a := by
  rw [System.acyclic_iff]
  intro b c t h₁ h₂ h₃
  replace h₁ := hist_suffix_of_reachable h₁
  replace h₃ := hist_suffix_of_reachable h₃
  rw [tr_to_iff] at h₂
  obtain ⟨h₂, ⟨p, t'⟩, h₄, rfl⟩:= h₂
  simp at h₃