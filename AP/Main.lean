import AP.Defs

noncomputable section
open scoped Classical

@[simp]
theorem game_play_zero {g : Game} : g.play 0 = g := rfl

@[simp]
theorem game_play_succ {n} {g : Game} : g.play (n + 1) = (g.play n).move := by
  apply Function.iterate_succ_apply'

@[simp]
theorem a_moves_eq_emp_iff {s} : A_moves s = ∅ ↔ ∀ s₁, ¬s.a_move s₁ := by
  simp [A_moves, Set.eq_empty_iff_forall_notMem]

@[simp]
theorem d_moves_eq_emp_iff {s} : D_moves s = ∅ ↔ ∀ s₁, ¬s.d_move s₁ := by
  simp [D_moves, Set.eq_empty_iff_forall_notMem]

@[simp]
theorem mem_a_moves {s s₁} : s₁ ∈ A_moves s ↔ s.a_move s₁ := by apply Iff.refl

@[simp]
theorem mem_d_moves {s s₁} : s₁ ∈ D_moves s ↔ s.d_move s₁ := by apply Iff.refl

@[simp]
theorem strat_ap_eq_none_iff {f : State' → State' → Prop}
{st : StratT # λ s => setOf # f s} {s} :
st.1.f s = none ↔ ∀ s₁, ¬f s.state s₁ := by
  rcases st with ⟨⟨ms, f', h₁⟩, h₂⟩; simp at h₁ h₂ ⊢
  subst h₂; specialize h₁ s; split at h₁
  case _ m h =>
    simp [h]; intro s₁; rw [Set.ext_iff] at h₁
    specialize h₁ s₁; simp at h₁; exact h₁
  case _ m s₂ h => simp [h]; exact ⟨_, h₁⟩

@[simp]
theorem a_strat_ap_eq_none_iff {a : A_strat} {s} :
a.1.f s = none ↔ ∀ s₁, ¬s.state.a_move s₁ := strat_ap_eq_none_iff

@[simp]
theorem d_strat_ap_eq_none_iff {a : D_strat} {s} :
a.1.f s = none ↔ ∀ s₁, ¬s.state.d_move s₁ := strat_ap_eq_none_iff

theorem of_strat_ap_eq_some {f : State' → State' → Prop}
{st : StratT # λ (s : State') => setOf # f s} {s : State} {s₁}
(h : st.1.f s = some s₁) : f s.state s₁ := by
  rcases st with ⟨⟨ms, f', h₂⟩, h₃⟩; simp at h h₃
  subst h₃; specialize h₂ s; simp [h] at h₂; exact h₂

theorem of_a_strat_ap_eq_some {a : A_strat} {s s₁} :
a.1.f s = some s₁ → s.state.a_move s₁ := of_strat_ap_eq_some

theorem of_d_strat_ap_eq_some {d : D_strat} {s s₁} :
d.1.f s = some s₁ → s.state.d_move s₁ := of_strat_ap_eq_some

def State'.reachable (s s₁ : State') :=
  ∃ (g : Game) (n : ℕ), s = g.state' ∧ s₁ = (g.play n).state'

def State'.valid s := ∃ pw, (state'₀ pw).reachable s

inductive State'.Reachable (s₀ : State') : State' → Prop where
| h₀ : Reachable s₀ s₀
| ha : ∀ (s s₁ : State'), s.a_move s₁ → Reachable s₀ s → Reachable s₀ s₁
| hd : ∀ (s s₁ : State'), s.d_move s₁ → Reachable s₀ s → Reachable s₀ s₁

theorem of_state_reachable {P : State' → Prop} {s₀ s : State'}
(hs : s₀.reachable s) (hp : P s₀)
(ha : ∀ (s s₁ : State'), s.a_move s₁ → P s → P s₁)
(hd : ∀ (s s₁ : State'), s.d_move s₁ → P s → P s₁) : P s := by
  rcases hs with ⟨g₀, n, rfl, rfl⟩
  induction n
  case zero => simpa
  case succ n ih =>
    simp; generalize g₀.play n = g at ih ⊢
    clear hp g₀; unfold Game.move
    split_ifs with h₁ h₂
    · exact ih;
    · simp; clear hd h₁ h₂; split
      case _ m h => exact ih
      case _ m s₂ h =>
        replace h := of_strat_ap_eq_some h
        apply ha _ _ h ih
    · simp; clear ha h₁ h₂; split
      case _ m h => exact ih
      case _ m s₂ h =>
        replace h := of_strat_ap_eq_some h
        apply hd _ _ h ih

theorem Reachable_or_reachable {s₀ s : State'}
(h : s₀.reachable s) : s₀.Reachable s := by
  · apply of_state_reachable h <;> clear h s
    · constructor
    · intro s s₁ h₁ h₂; apply State'.Reachable.ha <;> assumption
    · intro s s₁ h₁ h₂; apply State'.Reachable.hd <;> assumption

theorem pw_eq_of_Reachable {s₀ s : State'} (h : s₀.Reachable s) :
s.pw = s₀.pw := by
  induction h with
  | h₀ => rfl
  | ha s₁ s₂ h₁ h₂ h₃ => rw [←h₃]; rcases h₁ with ⟨a₁, rfl, _⟩; rfl
  | hd s₁ s₂ h₁ h₂ h₃ => rw [←h₃]; rcases h₁ with ⟨a₁, rfl, _⟩; rfl

theorem exi_Reachable_or_valid {s : State'} (h : s.valid) :
∃ pw, (state'₀ pw).Reachable s := by
  rcases h with ⟨pw, h⟩; replace h := Reachable_or_reachable h
  use pw, h

theorem Reachable_or_valid {s : State'} (h : s.valid) :
(state'₀ s.pw).Reachable s := by
  rcases h with ⟨pw, h⟩; replace h := Reachable_or_reachable h
  convert h; apply pw_eq_of_Reachable h

def point_equiv_prod : Point ≃ Prod ℤ ℤ := by
  use λ ⟨x, y⟩ => ⟨x, y⟩, λ ⟨x, y⟩ => ⟨x, y⟩ <;> intro x <;> simp

instance : Infinite Point := by
  rw [point_equiv_prod.infinite_iff]; infer_instance

theorem grid_always_inf {s : State'} (h : s.valid) : s.grid.Infinite := by
  obtain ⟨pw, h₁⟩ := exi_Reachable_or_valid h; clear h
  induction h₁ with
  | h₀ => apply Set.infinite_univ
  | ha s₁ s₂ h₁ h₂ h₃ => rcases h₁ with ⟨_, rfl, _⟩; simpa
  | hd s₁ s₂ h₁ h₂ h₃ => rcases h₁ with ⟨_, rfl, _⟩; simpa

theorem grid_always_nonempty {s : State'} (h : s.valid) :
s.grid.Nonempty := Set.Infinite.nonempty # grid_always_inf h

theorem d_always_has_move {s : State'} (h : s.valid) :
∃ s₁, s.d_move s₁ := by
  obtain h₁ := grid_always_inf h
  obtain ⟨p, h₂, h₃⟩ : ∃ p, p ∈ s.grid ∧ p ≠ s.a := by
    obtain ⟨grid', h₂⟩ := hv # s.grid.erase s.a
    have h₃ : grid'.Infinite := by simpa [h₂]
    obtain ⟨p, hp⟩ := h₃.nonempty
    use p; simp [h₂] at hp; simp [hp]
  use {s with grid := s.grid.erase p}, p

def Game.valid (g : Game) :=
∃ pw a d n, g = (game₀ pw a d).play n

def State.valid (s : State) :=
∃ (g : Game), g.valid ∧ s = g.state

theorem valid_state_of_valid_game {g : Game} (h : g.valid) :
g.state.valid := by use g

@[simp]
theorem pw_state'₀ {pw} : (state'₀ pw).pw = pw := rfl

@[simp]
theorem pw_state₀ {pw} : (state₀ pw).pw = pw := rfl

@[simp]
theorem pw_game₀ {pw a d} : (game₀ pw a d).pw = pw := rfl

@[simp]
theorem game_pw_play_eq {g : Game} {n} : (g.play n).pw = g.pw := by
  sorry

@[simp]
theorem game_pw_state_play_eq {g : Game} {n} : (g.play n).state.pw = g.pw :=
  game_pw_play_eq

theorem valid_state'_of_valid_state {s : State} (h : s.valid) :
s.state.valid := by
  rcases h with ⟨g, ⟨pw, a, d, n, hg⟩, hs⟩
  use s.pw, game₀ pw a d, n; simp [hs, hg]; rfl

-- theorem d_always_has_move' {g : Game} (hg : Game.valid) :
-- g.d.1.f g.state ≠ none := by

-- theorem a_turn_of_ended {pw a d n g} (h₁ : g = (game₀ pw a d).play n)
-- (h₂ : g.ended) : g.a_turn