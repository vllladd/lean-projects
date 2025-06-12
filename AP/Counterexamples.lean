import AP.Determinacy

noncomputable section
open scoped Classical

theorem counterexample₁ : ¬∀ (g₁ g₂ : Game), g₁.move = g₂.move → g₁ = g₂ := by
  push_neg
  obtain ⟨g, hg⟩ := hv (game₀ 0 default default).move
  use g, g.move
  have he : ¬g.ended :=
    by
      subst hg
      exact game₀_move_not_ended
  have ht : g.a_turn :=
    by
      subst hg
      simp [game_move_a_turn_iff_of_not_ended he]
  have h₁ : ¬g.a_has_move :=
    by
      subst g
      apply not_a_has_move_of_pw_0
      simp
  have h₂ : g.move = {g with ended := True} :=
    by
      simp [Game.move, he, ht]
      rw [a_strat_ap_eq_of_not_a_has_move h₁]
  have h₃ : g.move.move = g.move :=
    by
      apply game_move_eq_of_ended
      rw [h₂]
      trivial
  have h₄ : g.move.ended :=
    by
      rw [h₂]
      trivial
  use h₃.symm
  apply ne_of_congr Game.ended
  simp [he, h₄]

theorem counterexample₂ : ¬∀ (g₁ g₂ : Game),
g₁.move.toState = g₂.move.toState → g₁.toState = g₂.toState := by
  push_neg
  obtain ⟨a₂, s₂, sx, h₁⟩ := exi_a_ap_eq_some
  use ⟨s₂.push sx, default, default, default, True⟩
  use ⟨s₂, a₂, default, True, False⟩
  simp [Game.move, h₁]

theorem counterexample₃ : ¬∀ (g₁ g₂ : Game),
g₁.move.toState = g₂.move.toState → g₁.toState = g₂.toState := by
  push_neg
  have h := counterexample₂
  push_neg at h
  obtain ⟨g₁, g₂, h₁, h₂⟩ := h
  use g₁, g₂

theorem counterexample₄ : ¬∀ (s₁ s₂ : State'),
s₁.a_move s₂ → ¬(s₂.a_move s₁) := by
  push_neg
  use state'₀ 1, {state'₀ 1 with a_pos := (1, 0)}
  simp [State'.a_move, state'₀, grid₀, point₀, Point.dist]
  rfl

theorem counterexample₅ : ¬∀ (g : Game),
g.d_wins ↔ ∃ n, (g.play (n + 1)).ended ∧ (g.play n).a_turn := by
  push_neg
  obtain ⟨g, hg⟩ := hv {Game.dflt with a_turn := False, ended := True}
  dsimp at hg
  use g
  left
  constructor
  · simp [Game.d_wins, Game.a_wins]
    use 0
    simp [hg]
  intro n hn
  rw [game_play_eq_of_ended # by simp [hg]]
  simp [hg]

theorem counterexample₆ : ¬∀ (g₁ g₂ : Game) (n m : ℕ),
g₁.toState = g₂.toState → (g₁.play n).toState' = (g₂.play m).toState' →
(g₁.play n).toState = (g₂.play m).toState := by
  push_neg
  obtain ⟨a, ha⟩ := hv # mk_a_strat # λ s => (1 - s.a_pos.x, 0)
  obtain ⟨d, hd⟩ := hv # mk_d_strat # λ s => (0, 1)
  obtain ⟨s₀, hs₀⟩ := hv
    ({pw := 1, grid := Set.univ, a_pos := (0, 0)} : State')
  obtain ⟨g₁, hg₁⟩ := hv
    ({ a := a, d := d, toState := ⟨s₀, []⟩
     , a_turn := False, ended := False} : Game)
  obtain ⟨g₂, hg₂⟩ := hv
    ({ a := a, d := d, toState := ⟨s₀, []⟩
     , a_turn := True, ended := False} : Game)
  use g₁, g₂, 1, 3, by simp [hg₁, hg₂]
  obtain ⟨s₁, hs₁⟩ := hv
    ({pw := 1, grid := Set.univ.erase (0, 1), a_pos := (0, 0)} : State')
  obtain ⟨s₂, hs₂⟩ := hv
    ({pw := 1, grid := Set.univ, a_pos := (1, 0)} : State')
  obtain ⟨s₃, hs₃⟩ := hv
    ({pw := 1, grid := Set.univ.erase (0, 1), a_pos := (1, 0)} : State')
  dsimp only at hg₁ hg₂
  have h₁ : g₁.play 1 =
    { a := a, d := d, toState := ⟨s₁, [s₀]⟩
    , a_turn := True, ended := False} := by
    simp [Game.move, hg₁, hs₀]
    split
    · nm m h₁
      simp at h₁
      change ¬(state'₀ 1).d_has_move at h₁
      simp at h₁
    nm m s hs
    clear m
    rw [hd] at hs
    simp [State.push, hs₁]
    rw [mk_d_strat_ap_eq_some_iff_of_pos] at hs
    exact hs
    simp [State'.d_move]
    use (0, 1)
    simp
  dsimp only at h₁
  have h₂ : g₂.play 1 =
    { a := a, d := d, toState := ⟨s₂, [s₀]⟩
    , a_turn := False, ended := False} := by
    simp [Game.move, hg₂, hs₀]
    split
    · nm m h₂
      contrapose! h₂
      simp
      rw [a_has_move_iff]
      use (1, 0)
      simp [Point.dist]
      decide
    nm m s hs
    clear m
    rw [ha] at hs
    simp [State.push, hs₂]
    rw [mk_a_strat_ap_eq_some_iff_of_pos] at hs
    exact hs
    simp [State'.a_move, Point.dist]
    decide
  dsimp only at h₂
  have h₃ : g₂.play 2 =
    { a := a, d := d, toState := ⟨s₃, [s₀, s₂]⟩
    , a_turn := True, ended := False} := by
    dsimp
    rw [game_play_succ, h₂]
    simp [Game.move]
    split
    · nm m hs
      contrapose! hs
      simp
      rw [d_has_move_iff]
      use (0, 1)
      simp [hs₂]
    nm m s hs
    simp [State.push, hs₃]
    rw [hd, mk_d_strat_ap_eq_some_iff_of_pos] at hs
    simp [hs₂] at hs
    exact hs
    use (0, 1)
    simp [hs₂]
  dsimp only at h₃
  have h₄ : g₂.play 3 =
    { a := a, d := d, toState := ⟨s₁, [s₀, s₂, s₃]⟩
    , a_turn := False, ended := False} := by
    dsimp
    rw [game_play_succ, h₃]
    simp [Game.move]
    split
    · nm m hs
      contrapose! hs
      simp
      rw [a_has_move_iff]
      use (0, 0)
      simp [hs₃, Point.dist]
      decide
    nm m s hs
    simp [State.push, hs₁]
    rw [ha, mk_a_strat_ap_eq_some_iff_of_pos] at hs
    · simp [hs₃] at hs
      exact hs
    dsimp
    use (0, 0)
    simp [hs₃, Point.dist]
    decide
  dsimp only at h₄
  rw [h₁, h₄]
  simp