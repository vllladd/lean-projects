import Projects.AP.Alts.Alt1.Auxi
import Projects.Temp

namespace AP.Alt₁

@[simp] theorem Point.x_toAlt {p : Point} : p.toAlt.x = p.x := rfl
@[simp] theorem Point.y_toAlt {p : Point} : p.toAlt.y = p.y := rfl
@[simp] theorem Point.toAlt_mk {x y} : (⟨x, y⟩ : Point).toAlt = ⟨x, y⟩ := rfl

@[simp] theorem Point.x_ofAlt {p : PointZ} : (Point.ofAlt p).x = p.x := rfl
@[simp] theorem Point.y_ofAlt {p : PointZ} : (Point.ofAlt p).y = p.y := rfl
@[simp] theorem Point.ofAlt_mk {x y} : Point.ofAlt ⟨x, y⟩ = ⟨x, y⟩ := rfl

@[simp]
theorem ofAlt_dist {p₁ p₂ : PointZ} :
dist (.ofAlt p₁) (.ofAlt p₂) = (p₁.dist p₂).toNat := by
  rcases p₁, p₂ with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩; simp [dist]

@[simp]
theorem Board.pw_toAlt {b : Board} {pw aTurn hist} : (b.toAlt pw aTurn hist).pw = pw := rfl

@[simp]
theorem Board.taken_toAlt {b : Board} {pw aTurn hist} :
(b.toAlt pw aTurn hist).taken = Set'.ofSet (Set.univ \ b.squares |>.image (·.toAlt)) := rfl

@[simp]
theorem Board.aPos_toAlt {b : Board} {pw aTurn hist} :
(b.toAlt pw aTurn hist).aPos = b.A.toAlt := rfl

@[simp]
theorem Board.aTurn_toAlt {b : Board} {pw aTurn hist} :
(b.toAlt pw aTurn hist).aTurn = aTurn := rfl

@[simp]
theorem Board.hist_toAlt {b : Board} {pw aTurn hist} :
(b.toAlt pw aTurn hist).hist = hist := rfl

@[simp]
theorem State.pw_toAlt {s : State} {pw hist} : (s.toAlt pw hist).pw = pw := rfl

@[simp]
theorem State.taken_toAlt {s : State} {pw hist} :
(s.toAlt pw hist).taken = Set'.ofSet (Set.univ \ s.board.squares |>.image (·.toAlt)) := rfl

@[simp]
theorem State.aPos_toAlt {s : State} {pw hist} :
(s.toAlt pw hist).aPos = s.board.A.toAlt := rfl

@[simp]
theorem State.aTurn_toAlt {s : State} {pw hist} : (s.toAlt pw hist).aTurn = s.aTurn := rfl

@[simp]
theorem State.hist_toAlt {s : State} {pw hist} : (s.toAlt pw hist).hist = hist := rfl

@[simp]
theorem State.board_ofAlt {s act hist} : (State.ofAlt s act hist).board = Board.ofAlt s := rfl

@[simp]
theorem State.history_ofAlt {s act hist} : (State.ofAlt s act hist).history = hist := rfl

@[simp]
theorem State.act_ofAlt {s act hist} : (State.ofAlt s act hist).act ↔ act := by rfl

@[simp]
theorem State.aTurn_mk {b hist act} :
(⟨b, hist, act⟩ : State).aTurn = decide (Odd hist.length) := rfl

@[simp]
theorem toAlt_state₀ {pw hist} :
state₀.toAlt pw hist = (AP.initState pw 0).setHist hist := by
  simp [state₀, board₀, initState, center]; ext :1 <;> simp

@[simp]
theorem Point.toAlt_ofAlt {p} : (Point.ofAlt p).toAlt = p := rfl

@[simp]
theorem Point.ofAlt_toAlt {p} : Point.ofAlt p.toAlt = p := rfl

@[simp]
theorem Board.squares_ofAlt {s} : (Board.ofAlt s).squares =
Set.univ \ s.taken.toSet.image .ofAlt := rfl

@[simp]
theorem Board.a_ofAlt {s} : (Board.ofAlt s).A = .ofAlt s.aPos := rfl

@[simp]
theorem Board.ofAlt_init {s : AP.State} : Board.ofAlt s.init = ⟨Set.univ, .ofAlt s.aPos₀⟩ := by
  ext:1 <;> simp

theorem State.toAlt_ofAlt {s : AP.State} {act pw hist₁ hist₂}
(h : Odd hist₁.length ↔ s.aTurn) :
(State.ofAlt s act hist₁).toAlt pw hist₂ = (s.setPw pw).setHist hist₂ := by
  ext:1 <;> simp [Set.image_image, aTurn, h]

@[simp]
theorem State.board_setHist {s : State} {hist} : (s.setHist hist).board = s.board := rfl

@[simp]
theorem State.history_setHist {s : State} {hist} : (s.setHist hist).history = hist := rfl

@[simp]
theorem State.act_setHist {s : State} {hist} : (s.setHist hist).act = s.act := rfl

theorem Board.ofAlt_toAlt {s : State} {pw hist}
(h₁ : s.FinSq) : Board.ofAlt (s.toAlt pw hist) = s.board := by
  ext p :2 <;> simp
  generalize hs : Point.toAlt '' (.univ \ s.board.squares) = set
  have h₂ : set.Finite
  · subst hs; apply h₁.image
  simp [Set'.mem_ofSet h₂]; simp [←hs]

theorem State.ofAlt_toAlt {s : State} {pw hist₁ hist₂} (h₁ : s.FinSq) :
State.ofAlt (s.toAlt pw hist₁) s.act hist₂ = s.setHist hist₂ := by
  ext:1 <;> simp [Board.ofAlt_toAlt h₁]

@[simp]
theorem Game.not_aWinsAt_iff {pw} {g : Game pw} : ¬g.AWins ↔ g.DWins := by
  simp [AWins, DWins]

@[simp]
theorem Game.not_dWinsAt_iff {pw} {g : Game pw} : ¬g.DWins ↔ g.AWins := by
  simp [AWins, DWins]

@[simp]
theorem dMoveValid_none {b : Board} : DMoveValid b none := by
  simp [DMoveValid]

@[instance]
theorem A.nonempty {pw} : Nonempty (A pw) :=
  ⟨⟨λ _ _ h => ⟨_, h.choose_spec⟩⟩⟩

@[instance]
theorem D.nonempty : Nonempty D :=
  ⟨⟨λ _ _ => ⟨none, by simp⟩⟩⟩

noncomputable instance {pw} : Inhabited (A pw) := inferInstance
noncomputable instance : Inhabited D := inferInstance

@[simp] theorem board_state₀ : state₀.board = board₀ := rfl
@[simp] theorem squares_board₀ : board₀.squares = Set.univ := rfl
@[simp] theorem a_board₀ : board₀.A = ⟨0, 0⟩ := rfl
@[simp] theorem aTurn_state₀ : state₀.aTurn = false := rfl

@[simp]
theorem toAlt_board₀_not_aTurn {pw hist} :
board₀.toAlt pw false hist = (AP.initState pw 0).setHist hist := by
  ext <;> simp

instance : Inhabited Board := ⟨board₀⟩
instance : Inhabited State := ⟨state₀⟩

@[simp]
theorem toAltH_state₀_eq {pw} : state₀.toAltH pw = AP.initState pw 0 := by
  simp [State.toAltH, State.toAltH?, Board.toAltH?]
  apply choose?_of_pos (P := λ (s : Option AP.State) => s.getd = _) _ _
  · use AP.initState pw 0; simp
  rintro s h ⟨h₁, h₂⟩; simp; rw [←h₂]; simp
  rw [State.hist_eq_aPos_of] <;> rw [←h₂] <;> simp

@[simp]
theorem toAltH_board₀_eq {pw} : board₀.toAltH pw false = AP.initState pw 0 :=
  toAltH_state₀_eq

@[simp, instance]
theorem initial_toAltH_state₀ {pw} : sys.Initial # state₀.toAltH pw := by
  simp

@[simp]
theorem aHws_toAltH_state₀ {pw} : (state₀.toAltH pw).aHws ↔ AP.aHwsPw pw := by
  rw [aHwsPw_iff_p 0]
  simp [State.toAltH, State.toAltH?, Board.toAltH?]
  apply choose?_of_pos (P := λ (x : Option AP.State) => x.getd.aHws ↔ _) _ _
  · use AP.initState pw 0; simp
  rintro s - ⟨hs, h₂⟩
  simp at h₂ ⊢
  rw [setHist_eq_comm] at h₂
  simp at h₂
  rw [←h₂]
  have h₁ : sys.WF # s.setHist [0]; simp [h₂]
  simp

@[simp]
theorem dHws_toAltH_state₀ {pw} : (state₀.toAltH pw).dHws ↔ AP.dHwsPw pw := by
  contrapose!; simp [aHwsPw_iff_p 0]

@[simp]
theorem Game.play_zero {pw} {g : Game pw} : g.play 0 = g := rfl

@[simp]
theorem Game.s_initGame {pw a d s} : (initGame a d s : Game pw).s = s := rfl

@[simp]
theorem Game.act_initGame {pw a d s} : (initGame a d s : Game pw).act = s.act := rfl

@[simp]
theorem act_state₀ : state₀.act := trivial

theorem State.dwn_eq {pw} {s : State} : s.dwn pw = (s.toAltH pw).dwn := rfl

theorem Game.play_succ {pw} {g : Game pw} {n} : g.play (n + 1) = (g.play n).playMove := by
  rw [play, Function.iterate_succ']; rfl

theorem Game.play_succ' {pw} {g : Game pw} {n} : g.play (n + 1) = g.playMove.play n := rfl

@[simp]
theorem Game.state_setState {pw} {g : Game pw} {s} : (g.setState s).s = s := rfl

@[simp]
theorem Game.act_setState {pw} {g : Game pw} {s} : (g.setState s).act ↔ s.act := by rfl

@[simp]
theorem Game.act_applyDMove {s m} : (applyDMove s m).act ↔ s.act := by rfl

@[simp]
theorem Game.act_playDMoveAt {pw} {g : Game pw} {h} : (playDMoveAt g h).act := by
  simpa [playDMoveAt]

theorem Game.playMove_eq_of_not_act {pw} {g : Game pw} (h : ¬g.act) : g.playMove = g := by
  simp [playMove, h]

theorem Game.play_eq_of_not_act {pw} {g : Game pw} {n} (h : ¬g.act) : g.play n = g := by
  induction n; rfl; nm n ih; rw [play_succ, ih]; exact playMove_eq_of_not_act h

@[simp]
theorem State.act_finish {s : State} : ¬s.finish.act := by
  simp [finish]

@[simp]
theorem Game.act_finish {pw} {g : Game pw} : ¬g.finish.act := by
  simp [finish]

@[simp]
theorem Game.playMove_finish {pw} {g : Game pw} : g.finish.playMove = g.finish := by
  apply playMove_eq_of_not_act; simp

@[simp]
theorem Game.play_finish {pw} {g : Game pw} {n} : g.finish.play n = g.finish := by
  apply play_eq_of_not_act; simp

@[simp]
theorem a_playDMoveAt {pw} {g : Game pw} {h} : (playDMoveAt g h).a = g.a := rfl

@[simp] theorem a_initGame {pw a d s} : (initGame a d s : Game pw).a = a := rfl
@[simp] theorem d_initGame {pw a d s} : (initGame a d s : Game pw).d = d := rfl

@[simp]
theorem State.aTurn_applyMove {s m} : (applyMove s m).aTurn = !s.aTurn := by
  simp [applyMove, State.aTurn]

@[simp]
theorem State.aTurn_applyDMove {s m} : (applyDMove s m).aTurn = !s.aTurn := by
  simp [applyDMove]

@[simp]
theorem aTurn_playDMoveAt {pw} {g : Game pw} {h} : (playDMoveAt g h).s.aTurn = !g.s.aTurn := by
  simp [playDMoveAt]

@[simp]
theorem applyDMoveB_none {b} : applyDMoveB b none = b := rfl

@[simp]
theorem State.board_applyMove {s b} : (applyMove s b).board = b := rfl

@[simp]
theorem State.history_applyMove {s b} : (applyMove s b).history = s.history ++ [s.board] := rfl

@[simp]
theorem State.act_applyMove {s b} : (applyMove s b).act ↔ s.act := by rfl

@[simp]
theorem applyDMove_none {s} : applyDMove s none = s.setHist (s.history ++ [s.board]) := by
  ext:1 <;> simp [applyDMove]

@[simp]
theorem State.aTurn_setHist {s : State} {hist} :
(s.setHist hist).aTurn = decide (Odd hist.length) := by
  simp [setHist]

theorem State.toAltH_setHist {pw} {s : State} {hist}
(ht : s.aTurn = decide (Odd hist.length)) :
(s.setHist hist).toAltH pw = s.toAltH pw := by
  simp [toAltH, toAltH?, ←ht]

theorem State.wf_iff {pw} {s : State} : s.WF pw ↔ ∃ a d n g,
(initGame a d state₀ : Game pw).play n = g ∧ (g.s = s ∨ ∃ h, (playDMoveAt g h).s = s) :=
  ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

@[simp, instance]
theorem wf_state₀ {pw} : state₀.WF pw := by
  rw [State.wf_iff]; use default, default, 0; simp

@[simp]
theorem Game.setState_initGame {pw a d s s'} :
(initGame a d s : Game pw).setState s' = initGame a d s' := rfl

@[simp]
theorem Game.s_finish {pw} {g : Game pw} : g.finish.s = g.s.finish := rfl

@[simp]
theorem State.aTurn_finish {s : State} : s.finish.aTurn = s.aTurn := rfl

@[simp]
theorem State.act_applyAMove {s : State} {b} : (applyAMove s b).act ↔ s.act := by rfl

@[simp]
theorem State.aTurn_applyAMove {s : State} {b} : (applyAMove s b).aTurn = !s.aTurn := by
  simp [applyAMove]

theorem Game.act_play_initGame_of_not_aTurn {pw a d n g s}
(h₁ : s.aTurn = false) (h₂ : s.act) (h₃ : (initGame a d s : Game pw).play n = g)
(h₄ : g.s.aTurn = false) : g.act := by
  induction n generalizing s g
  · simp at h₃; simpa [←h₃]
  nm n ih
  rw [play_succ'] at h₃
  simp [playMove, h₂] at h₃
  simp [playDMoveAt] at h₃
  generalize_proofs at h₃
  generalize h₅ : applyDMove s (d.f s h₂).m = s₁ at h₃
  have h₆ : s₁.act; simpa [←h₅]
  simp [playAMoveAt] at h₃
  rw! (castMode := .all) [eq_true_of h₆, true_and] at h₃
  split_ifs at h₃ with h₇
  rotate_left
  · replace h₃ := congrArg (·.s.aTurn) h₃
    simp [←h₅, h₁, h₄] at h₃
  simp [playAMoveAt'] at h₃
  generalize_proofs at h₃
  generalize hs₂ : applyAMove s₁ (a.f s₁ h₆ h₇).m = s₂ at h₃
  have H₁ : s₂.act; simpa [←hs₂]
  have H₂ : s₁.aTurn = true; simpa [←h₅]
  have H₃ : s₂.aTurn = false; simpa [←hs₂]
  grind

@[simp]
theorem Game.s_playDMoveAt_eq_iff {pw} {g₁ g₂ : Game pw} {h₁ h₂} :
(playDMoveAt g₁ h₁).s = (playDMoveAt g₂ h₂).s ↔
applyDMove g₁.s (g₁.d.f g₁.s h₁).m = applyDMove g₂.s (g₂.d.f g₂.s h₂).m := by rfl

@[simp] theorem Game.a_finish {pw} {g : Game pw} : g.finish.a = g.a := rfl
@[simp] theorem Game.d_finish {pw} {g : Game pw} : g.finish.d = g.d := rfl

@[simp] theorem Game.a_setState {pw} {g : Game pw} {s} : (g.setState s).a = g.a := rfl
@[simp] theorem Game.d_setState {pw} {g : Game pw} {s} : (g.setState s).d = g.d := rfl

@[simp]
theorem Game.a_playAMoveAt' {pw} {g : Game pw} {a : A pw} {h₁ h₂} :
(playAMoveAt' a g h₁ h₂).a = g.a := rfl

@[simp]
theorem Game.d_playAMoveAt' {pw} {g : Game pw} {a : A pw} {h₁ h₂} :
(playAMoveAt' a g h₁ h₂).d = g.d := rfl

@[simp]
theorem Game.a_playAMoveAt {pw} {g : Game pw} : (playAMoveAt g).a = g.a := by
  simp [playAMoveAt]; split_ifs <;> simp

@[simp]
theorem Game.d_playAMoveAt {pw} {g : Game pw} : (playAMoveAt g).d = g.d := by
  simp [playAMoveAt]; split_ifs <;> simp

@[simp]
theorem Game.a_playDMoveAt {pw} {g : Game pw} {h} : (playDMoveAt g h).a = g.a := by
  simp [playDMoveAt]

@[simp]
theorem Game.d_playDMoveAt {pw} {g : Game pw} {h} : (playDMoveAt g h).d = g.d := by
  simp [playDMoveAt]

@[simp]
theorem Game.a_playMove {pw} {g : Game pw} : g.playMove.a = g.a := by
  simp [playMove]; split_ifs <;> simp

@[simp]
theorem Game.d_playMove {pw} {g : Game pw} : g.playMove.d = g.d := by
  simp [playMove]; split_ifs <;> simp

@[simp]
theorem Game.a_play {pw} {g : Game pw} {n} : (g.play n).a = g.a := by
  induction n; rfl; simpa [play_succ]

@[simp]
theorem Game.d_play {pw} {g : Game pw} {n} : (g.play n).d = g.d := by
  induction n; rfl; simpa [play_succ]

@[simp]
theorem State.board_finish {s : State} : s.finish.board = s.board := rfl

theorem Game.s_playAMoveAt_eq_of {pw} {g₁ g₂ : Game pw} (h₁ : g₁.s.act ↔ g₂.s.act)
(h₂ : AHasValidMove pw g₁.s.board ↔ AHasValidMove pw g₂.s.board) : ∀ h₁ h₂ h₃ h₄,
(playAMoveAt g₁).s = (playAMoveAt g₂).s ↔
applyAMove g₁.s (g₁.a.f g₁.s h₁ h₂).m = applyAMove g₂.s (g₂.a.f g₂.s h₃ h₄).m := by
  simp_all [playAMoveAt, playAMoveAt', applyAMove, act]

theorem Game.playAMoveAt_eq_of_neg {pw} {g : Game pw}
(h : ¬g.act ∨ ¬AHasValidMove pw g.s.board) : playAMoveAt g = g.finish := by
  simp [playAMoveAt]; tauto

theorem Game.s_play_initGame_d_set_eq_of_ne {pw a d s s₁ dRef n}
(h : ∀ k < n, (initGame a d s |>.play k : Game pw).s ≠ s₁) :
(initGame a (d.set s₁ dRef) s |>.play n).s = (initGame a d s |>.play n).s := by
  induction n; simp
  nm n ih
  specialize ih # by grind
  simp [play_succ, playMove, act]
  rw! (castMode := .all) [ih]
  split_ifs with h₁
  on_goal 2 => exact ih
  generalize hg : (initGame a d s).play n = g at *
  generalize hg₁ : (initGame a (d.set s₁ dRef) s).play n = g₁ at *
  have H₁ : g₁.a = g.a; simp [←hg, ←hg₁]
  simp [playDMoveAt]
  rw! [ih]
  suffices h₂ : applyDMove g.s (g₁.d.f g.s h₁).m = applyDMove g.s (g.d.f g.s h₁).m
  · rw [h₂]
    generalize h₃ : applyDMove g.s (g.d.f g.s h₁).m = s'
    have h₄ : s'.act; simpa [←h₃]
    by_cases h₅ : ¬AHasValidMove pw s'.board
    · iterate 2 rw [playAMoveAt_eq_of_neg # by tauto];; simp
    push_neg at h₅
    have h₆ := @s_playAMoveAt_eq_of _ (g₁.setState s') (g.setState s')
      (by simp) (by simp) (by simpa) (by simpa) (by simpa) (by simpa)
    rw [h₆]; clear h₆
    simp; grind
  congr 2; simp [←hg₁, D.set]
  rw [if_neg]; simp [←hg]
  rw [←hg]; apply h; omega

-- theorem Game.s_play_eq_iff_of_act {pw} {g : Game pw} {n m}
-- (h : g.play (max n m) |>.act) : (g.play n).s = (g.play m).s ↔ n = m := by
--   sorry

-- #check 0 #exit

-- theorem wf_playDMoveAt {pw} {g : Game pw} {h} (hs : g.s.WF pw)
-- (ht : g.s.aTurn = false) : (playDMoveAt g h).s.WF pw := by
--   rw [State.wf_iff] at hs ⊢
--   choose a d n g₁ h₁ h₂ using hs
--   rcases h₂ with h₂ | ⟨h₂, h₃⟩
--   ·
--     generalize hg' : (initGame a (d.set g₁.s g.d) state₀).play n = g'
--     refine' ⟨a, _, n, g', hg', _⟩
--     have h₃ : g₁.s.act
--     ·
--       replace h₂ := congrArg (·.aTurn) h₂
--       simp [ht] at h₂
--       apply Game.act_play_initGame_of_not_aTurn _ _ h₁ <;> simp_all
--     right
--     have h₄ : g'.s = g.s
--     ·
--       -- rw [←h₂, ←hg', ←h₁]
--       rw [←h₂, ←h₁, ←hg']
--       apply Game.s_play_initGame_d_set_eq_of_ne
--       intro k hk
--       simp [←h₁]
--       rw [Game.s_play_eq_iff_of_act]; omega
--       rw [max_eq_right_of_lt hk, h₁]
--     simp [h₄, h]
--     simp [applyDMove, applyMove]
--     congr 1
--     simp [←hg']
--     simp [D.set]
--     grind
--   ·
--     sorry

-- #check 0 #exit

-- theorem dHws_and_dwn_lt_toAltH_playDMoveAt_dOptimal_of_dHws {pw} {g g₁ : Game pw} {h}
-- (h₁ : g.d = (dOptimal pw).getd)
-- (h₂ : g.s.toAltH pw |>.dHws)
-- (ht : g.s.aTurn = false)
-- (hg₁ : playDMoveAt g h = g₁) :
-- (g₁.s.toAltH pw).dHws ∧ g₁.s.dwn pw < g.s.dwn pw := by
--   sorry

-- #check 0 #exit

-- theorem DHws_of_alt {pw} (h : AP.dHwsPw pw) : DHws pw := by
--   specialize h 0
--   generalize h₀ : state₀ = s
--   
--   replace h : s.toAltH pw |>.dHws
--   ·
--     subst h₀
--     simp [State.toAltH, State.toAltH?, Board.toAltH?]
--     
--     apply choose?_of_pos (P := λ (x : Option AP.State) => x.getd.dHws) _ _
--     ·
--       use AP.initState pw 0
--       simp
--     
--     rintro s - ⟨hs, h₂⟩
--     simp at h₂ ⊢
--     rw [setHist_eq_comm] at h₂
--     simp at h₂
--     rw [←h₂] at h
--     
--     have h₁ : sys.WF # s.setHist [0]
--     ·
--       simp [h₂]
--     
--     simp at h
--     exact h
--   
--   have h₁ : s.toAltH pw = AP.initState pw 0
--   ·
--     simp [←h₀]
--   
--   generalize hn : s.dwn pw = n
--   generalize h₂ : (dOptimal pw).getd = d
--   use d
--   intro a
--   have hs : sys.WF # s.toAltH pw; simp [h₁]
--   
--   rw [h₀]
--   have h₃ : s.act
--   ·
--     rw [←h₀]
--     simp
--   
--   have ht : s.aTurn = false
--   ·
--     simp [←h₀]
--   
--   clear h₀ h₁
--   
--   use n
--   
--   induction n using Nat.strong_induction_on generalizing s
--   nm n ih
--   cases n
--   ·
--     contrapose! hn
--     simpa [State.dwn_eq, State.dwn_eq_zero_iff_aHws]
--   nm n
--   simp at ih
--   
--   simp [Game.play_succ', Game.playMove, h₃, playAMoveAt]
--   rw! [eq_true_of Game.act_playDMoveAt]
--   rw! (castMode := .all) [true_and]
--   
--   split_ifs with h₄
--   on_goal 2 => simp
--   
--   generalize_proofs H₁ H₂ H₃
--   by_contra H
--   generalize hg₁ : playDMoveAt (initGame a d s) H₁ = g₁
--   contrapose H; clear H
--   rw! [hg₁] at h₄ ⊢
--   
--   have ht₁ : g₁.s.aTurn = true
--   ·
--     clear ih
--     subst hg₁
--     simpa
--   
--   obtain ⟨h₅, h₆⟩ : (g₁.s.toAltH pw).dHws ∧ g₁.s.dwn pw < s.dwn pw
--   ·
--     clear ih
--     apply @dHws_and_dwn_lt_toAltH_playDMoveAt_dOptimal_of_dHws pw (initGame a d s) g₁
--     simp [h₂]; all_goals simpa
--   
--   have hs₁ : sys.WF # g₁.s.toAltH pw
--   ·
--     clear ih
--     simp [←hg₁]
--   
--   -- specialize ih _ (by omega) g₁.s h₅ rfl hs₁ (by simpa [←hg₁])