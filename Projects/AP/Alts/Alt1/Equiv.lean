import Projects.AP.Util
import Projects.AP.Alts.Alt1.Auxi

namespace AP.Alt₁

@[simp] theorem Point.x_toAlt {p : Point} : p.toAlt.x = p.x := rfl
@[simp] theorem Point.y_toAlt {p : Point} : p.toAlt.y = p.y := rfl
@[simp] theorem Point.toAlt_mk {x y} : (⟨x, y⟩ : Point).toAlt = ⟨x, y⟩ := rfl

@[simp] theorem Point.x_ofAlt {p : PointZ} : (Point.ofAlt p).x = p.x := rfl
@[simp] theorem Point.y_ofAlt {p : PointZ} : (Point.ofAlt p).y = p.y := rfl
@[simp] theorem Point.ofAlt_mk {x y} : Point.ofAlt ⟨x, y⟩ = ⟨x, y⟩ := rfl

@[simp]
theorem ofAlt_dist {p₁ p₂ : PointZ} : dist (.ofAlt p₁) (.ofAlt p₂) = (p₁.dist p₂).toNat := by
  rcases p₁, p₂ with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩; simp [dist]

theorem dist_eq_alt {p₁ p₂ : Point} : dist p₁ p₂ = (p₁.toAlt.dist p₂.toAlt).toNat := by
  rcases p₁, p₂ with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩; simp [dist]

@[simp] theorem Game.act_iff {pw} {g : Game pw} : g.act ↔ g.s.act := by rfl

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

@[simp, instance]
theorem A.nonempty {pw} : Nonempty (A pw) :=
  ⟨⟨λ _ _ h => ⟨_, h.choose_spec⟩⟩⟩

@[simp, instance]
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
theorem toAltH_state₀ {pw} : state₀.toAltH pw = AP.initState pw 0 := by
  simp [State.toAltH, State.toAltH?, Board.toAltH?]
  apply choose?_of_pos (P := λ (s : Option AP.State) => s.getd = _) _ _
  · use AP.initState pw 0; simp
  rintro s h ⟨h₁, h₂⟩; simp; rw [←h₂]; simp
  rw [State.hist_eq_aPos_of] <;> rw [←h₂] <;> simp

@[simp]
theorem toAltH_board₀ {pw} : board₀.toAltH pw false = AP.initState pw 0 :=
  toAltH_state₀

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
theorem Game.act_initGame {pw a d s} : (initGame a d s : Game pw).s.act = s.act := rfl

@[simp]
theorem act_state₀ : state₀.act := trivial

theorem State.dwn_eq {pw} {s : State} : s.dwn pw = (s.toAltH pw).dwn := rfl

@[simp]
theorem Game.play_succ {pw} {g : Game pw} {n} : g.play (n + 1) = (g.play n).playMove := by
  rw [play, Function.iterate_succ']; rfl

theorem Game.play_succ' {pw} {g : Game pw} {n} : g.play (n + 1) = g.playMove.play n := rfl

@[simp]
theorem Game.state_setState {pw} {g : Game pw} {s} : (g.setState s).s = s := rfl

@[simp]
theorem Game.act_setState {pw} {g : Game pw} {s} : (g.setState s).s.act ↔ s.act := by rfl

@[simp]
theorem Game.act_applyDMove {s m} : (applyDMove s m).act ↔ s.act := by rfl

@[simp]
theorem Game.act_playDMoveAt {pw} {g : Game pw} {h} : (playDMoveAt g h).s.act := by
  simpa [playDMoveAt]

theorem Game.playMove_eq {pw} {g : Game pw} : g.playMove = haveI := Classical.propDecidable
if hs : g.s.act then playAMoveAt # playDMoveAt g hs else g := rfl

theorem Game.playMove_eq_of_not_act {pw} {g : Game pw} (h : ¬g.s.act) : g.playMove = g := by
  simp [playMove_eq, h]

theorem Game.play_eq_of_not_act {pw} {g : Game pw} {n} (h : ¬g.s.act) : g.play n = g := by
  induction n; rfl; nm n ih; rw [play_succ, ih]; exact playMove_eq_of_not_act h

@[simp]
theorem State.act_finish {s : State} : ¬s.finish.act := by
  simp [finish]

@[simp]
theorem Game.act_finish {pw} {g : Game pw} : ¬g.finish.s.act := by
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
(h₄ : g.s.aTurn = false) : g.s.act := by
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
  split_ifs at h₃ with h₇
  rotate_left
  · replace h₃ := congrArg (·.s.aTurn) h₃
    simp [←h₅, h₁, h₄] at h₃
  rcases h₇ with ⟨h₇, h₈⟩
  simp [playAMoveAt'] at h₃
  generalize_proofs at h₃
  generalize hs₂ : applyAMove s₁ (a.f s₁ h₆ h₈).m = s₂ at h₃
  have H₁ : s₂.act; simpa [←hs₂]
  have H₂ : s₁.aTurn = true; simpa [←h₅]
  have H₃ : s₂.aTurn = false; simpa [←hs₂]
  grind

@[simp]
theorem Game.s_playAMoveAt'_eq_iff {pw} {g₁ g₂ : Game pw} {h₁ h₂ h₃ h₄} :
(playAMoveAt' g₁.a g₁ h₁ h₂).s = (playAMoveAt' g₂.a g₂ h₃ h₄).s ↔
applyAMove g₁.s (g₁.a.f g₁.s h₁ h₂).m = applyAMove g₂.s (g₂.a.f g₂.s h₃ h₄).m := by rfl

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

theorem Game.s_playAMoveAt_eq_iff_of {pw} {g₁ g₂ : Game pw} (h₁ : g₁.s.act ↔ g₂.s.act)
(h₂ : AHasValidMove pw g₁.s.board ↔ AHasValidMove pw g₂.s.board) : ∀ h₁ h₂ h₃ h₄,
(playAMoveAt g₁).s = (playAMoveAt g₂).s ↔
applyAMove g₁.s (g₁.a.f g₁.s h₁ h₂).m = applyAMove g₂.s (g₂.a.f g₂.s h₃ h₄).m := by
  simp_all [playAMoveAt, playAMoveAt', applyAMove, act]

theorem Game.playAMoveAt_eq_of_neg {pw} {g : Game pw}
(h : ¬g.s.act ∨ ¬AHasValidMove pw g.s.board) : playAMoveAt g = g.finish := by
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
  have h₂ : applyDMove g.s (g₁.d.f g.s h₁).m = applyDMove g.s (g.d.f g.s h₁).m
  · congr 2; simp [←hg₁, D.set]
    rw [if_neg]; simp [←hg]
    rw [←hg]; apply h; omega
  rw [h₂]
  generalize h₃ : applyDMove g.s (g.d.f g.s h₁).m = s'
  have h₄ : s'.act; simpa [←h₃]
  by_cases h₅ : ¬AHasValidMove pw s'.board
  · iterate 2 rw [playAMoveAt_eq_of_neg # by tauto];; simp
  push Not at h₅
  have h₆ := @s_playAMoveAt_eq_iff_of _ (g₁.setState s') (g.setState s')
    (by simp) (by simp) (by simpa) (by simpa) (by simpa) (by simpa)
  rw [h₆]; clear h₆
  simp; grind

theorem Game.act_of_act_playMove {pw} {g : Game pw} (h : g.playMove.s.act) : g.s.act := by
  by_contra h₁; simp [playMove_eq, h₁] at h

theorem Game.act_of_act_play {pw} {g : Game pw} {n} (h : (g.play n).s.act) : g.s.act := by
  induction n; simp at h; exact h
  nm n ih; apply ih
  simp [play_succ] at h
  exact act_of_act_playMove h

@[simp]
theorem State.length_history_applyAMove {s m} :
(applyAMove s m).history.length = s.history.length + 1 := by
  simp [applyAMove]

@[simp]
theorem State.length_history_applyDMove {s m} :
(applyDMove s m).history.length = s.history.length + 1 := by
  simp [applyDMove]

@[simp]
theorem Game.length_history_playAMoveAt' {pw} {g : Game pw} {a : A pw} {h₁ h₂} :
(playAMoveAt' a g h₁ h₂).s.history.length = g.s.history.length + 1 := by
  simp [playAMoveAt']

@[simp]
theorem Game.length_history_playDMoveAt {pw} {g : Game pw} {h} :
(playDMoveAt g h).s.history.length = g.s.history.length + 1 := by
  simp [playDMoveAt]

@[simp]
theorem State.history_finish {s : State} : s.finish.history = s.history := rfl

theorem Game.length_history_playMove_eq_of_act {pw} {g : Game pw}
(h : g.playMove.s.act) : g.playMove.s.history.length = g.s.history.length + 2 := by
  have h₁ := act_of_act_playMove h
  simp [h₁, playMove, playAMoveAt]
  rw [dif_pos]; simp
  simp [playMove, h₁, playAMoveAt] at h
  split_ifs at h with h₂ <;> simp_all

theorem Game.length_history_play_eq_of_act {pw} {g : Game pw} {n}
(h : (g.play n).act) : (g.play n).s.history.length = g.s.history.length + n * 2 := by
  induction n; simp; nm n ih
  simp [play_succ] at h ⊢
  specialize ih # act_of_act_playMove h
  rw [length_history_playMove_eq_of_act h]; omega

@[simp]
theorem Game.play_add {pw} {g : Game pw} {n m} : g.play (n + m) = (g.play n).play m := by
  nth_rw 1 [play, add_comm]; rw [Function.iterate_add]; rfl

theorem Game.s_play_eq_iff_of_act {pw} {g : Game pw} {n m}
(h : g.play (max n m) |>.act) : (g.play n).s = (g.play m).s ↔ n = m := by
  symm; constructor; rintro rfl; rfl
  contrapose!
  intro h₁
  apply ne_of_congr (·.history.length)
  wlog h₂ : n < m with ih; grind
  clear h₁
  rw [max_eq_right_of_lt h₂] at h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le # le_of_lt h₂
  simp at h ⊢
  rw [length_history_play_eq_of_act h]; omega

@[simp]
theorem history_state₀ : state₀.history = [] := rfl

@[simp]
theorem Game.aTurn_playAMoveAt' {pw} {g : Game pw} {a : A pw} {h₁ h₂} :
(playAMoveAt' a g h₁ h₂).s.aTurn = !g.s.aTurn := by
  simp [playAMoveAt']

theorem Game.aTurn_playMove_eq_of_act {pw} {g : Game pw}
(h : g.playMove.s.act) : g.playMove.s.aTurn = g.s.aTurn := by
  simp [playMove] at h ⊢
  split_ifs at h ⊢ with h₁; on_goal 2 => contradiction
  generalize hg₁ : playDMoveAt g h₁ = g₁ at h ⊢
  have h₂ : g₁.s.act; simp [←hg₁]
  simp [playAMoveAt] at h ⊢
  rw! (castMode := .all) [Game.act, eq_true_of h₂, true_and] at h ⊢
  split_ifs at h ⊢ with h₃; on_goal 2 => simp at h
  simp [←hg₁]

theorem Game.aTurn_play_eq_of_act {pw} {g : Game pw} {n}
(h : (g.play n).act) : (g.play n).s.aTurn = g.s.aTurn := by
  induction n; simp; nm n ih; simp at h ⊢
  specialize ih (act_of_act_playMove h)
  rwa [aTurn_playMove_eq_of_act h]

theorem aState_iff' {pw s} : AState pw s ↔ s.WF pw ∧ s.aTurn = true := by
  constructor <;> rintro ⟨⟩ <;> constructor <;> assumption

theorem dState_iff' {pw s} : DState pw s ↔ s.WF pw ∧ s.aTurn = false := by
  constructor <;> rintro ⟨⟩ <;> constructor <;> assumption

@[simp, instance]
theorem aState_playDMoveAt {pw} {g : Game pw} {h}
[hs : DState pw g.s] : AState pw (playDMoveAt g h).s := by
  rw [dState_iff'] at hs; choose hs ht using hs; rw [aState_iff']
  rw [State.wf_iff] at hs ⊢
  symm; split_ands; simpa
  choose a d n g₁ h₁ h₂ using hs
  symm at h₂; rcases h₂ with ⟨h', h₂⟩ | h₂
  · contrapose h₂; clear h₂
    apply ne_of_congr (·.aTurn)
    simp [ht]
    rw [←h₁] at h' ⊢
    simp [Game.aTurn_play_eq_of_act h']
  have h₃ : g₁.s.act
  · replace h₂ := congrArg (·.aTurn) h₂
    simp [ht] at h₂
    apply Game.act_play_initGame_of_not_aTurn _ _ h₁ <;> simp_all
  generalize hg' : (initGame a (d.set g₁.s g.d) state₀).play n = g'
  refine' ⟨a, _, n, g', hg', _⟩; right
  have h₄ : g'.s = g.s
  · rw [←h₂, ←h₁, ←hg']
    apply Game.s_play_initGame_d_set_eq_of_ne
    intro k hk
    simp [←h₁]
    rw [Game.s_play_eq_iff_of_act]; omega
    rw [max_eq_right_of_lt hk, h₁]
    exact h₃
  simp [h₄, h, applyDMove, applyMove]
  congr 1; simp [←hg', D.set]; grind

theorem Game.playAMoveAt_eq_of_not_act {pw} {g : Game pw}
(h : ¬g.s.act) : playAMoveAt g = g.finish := by
  simp [playAMoveAt, h]

theorem Game.s_play_initGame_a_set_eq_of_ne {pw a d s s₁ aRef n}
(h : ∀ k < n, ∀ h, (playDMoveAt (initGame a d s |>.play k) h : Game pw).s ≠ s₁) :
(initGame (a.set s₁ aRef) d s |>.play n).s = (initGame a d s |>.play n).s := by
  induction n; simp
  nm n ih
  specialize ih # by grind
  simp [play_succ, playMove, act]
  rw! (castMode := .all) [ih]
  split_ifs with h₁
  on_goal 2 => exact ih
  generalize hg : (initGame a d s).play n = g at *
  generalize hg₁ : (initGame (a.set s₁ aRef) d s).play n = g₁ at *
  generalize_proofs H₁
  generalize hgx : playDMoveAt g₁ H₁ = gx
  generalize hgy : playDMoveAt g h₁ = gy
  have H₂ : gx.s = gy.s
  · subst hgx hgy
    simp
    congr 1
    simp [←hg₁, ←hg]
    rw! [ih]
    rfl
  simp [playAMoveAt, act]
  rw! (castMode := .all) [H₂]
  split_ifs with H₃; on_goal 2 => simp [H₂]
  rcases H₃ with ⟨H₃, H₄⟩
  simp
  have H₅ : gx.a = a.set s₁ aRef; simp [←hgx, ←hg₁]
  have H₆ : gy.a = a; simp [←hgy, ←hg]
  rw! [H₅, H₆, ←H₂]
  congr 2
  simp [A.set]
  contrapose!; rintro - rfl
  contrapose h; clear h
  simp
  use n, by rfl
  simp [hg, h₁, hgy, H₂]

theorem Game.playAMoveAt_eq_of_pos {pw} {g : Game pw}
(h₁ : g.s.act) (h₂ : AHasValidMove pw g.s.board) :
playAMoveAt g = playAMoveAt' g.a g h₁ h₂ := by
  simp [playAMoveAt, h₁, h₂]

theorem Game.act_of_act_playAMoveAt {pw} {g : Game pw} (h : playAMoveAt g |>.act) : g.s.act := by
  by_contra! h₁; simp [playAMoveAt, h₁] at h

theorem Game.aHasValidMove_of_act_playAMoveAt {pw} {g : Game pw}
(h : playAMoveAt g |>.act) : AHasValidMove pw g.s.board := by
  by_contra! h₁; simp [playAMoveAt, h₁] at h

theorem Game.s_playAMoveAt_eq_iff_of_act_playAMoveAt {pw} {g₁ g₂ : Game pw}
(h₁ : playAMoveAt g₁ |>.act) (h₂ : playAMoveAt g₂ |>.act) :
(playAMoveAt g₁).s = (playAMoveAt g₂).s ↔ applyAMove g₁.s (g₁.a.f g₁.s
(act_of_act_playAMoveAt h₁) (aHasValidMove_of_act_playAMoveAt h₁)).m =
applyAMove g₂.s (g₂.a.f g₂.s (act_of_act_playAMoveAt h₂)
(aHasValidMove_of_act_playAMoveAt h₂)).m := by
  have H₁ := act_of_act_playAMoveAt h₁
  have H₂ := act_of_act_playAMoveAt h₂
  have H₃ := aHasValidMove_of_act_playAMoveAt h₁
  have H₄ := aHasValidMove_of_act_playAMoveAt h₂
  simp [playAMoveAt]; rw [dif_pos ⟨H₁, H₃⟩, dif_pos ⟨H₂, H₄⟩]; simp

@[simp]
theorem Game.act_playAMoveAt' {pw} {g : Game pw} {a : A pw} {h₁ h₂} :
(playAMoveAt' a g h₁ h₂).act ↔ g.s.act := by rfl

theorem State.finish_eq_of_not_act {s : State} (h : ¬s.act) : s.finish = s := by
  ext:1 <;> simp_all

theorem Game.finish_eq_of_not_act {pw} {g : Game pw} (h : ¬g.s.act) : g.finish = g := by
  ext:1 <;> simp; exact State.finish_eq_of_not_act h

@[simp]
theorem dState_state₀ {pw} : DState pw state₀ := by
  simp [dState_iff']; use default, default, 0; simp

@[simp]
theorem AState.aTurn {pw : outParam ℕ} {s} [hs : AState pw s] : s.aTurn = true := hs.ht

@[simp]
theorem DState.aTurn {pw : outParam ℕ} {s} [hs : DState pw s] : s.aTurn = false := hs.ht

@[simp, instance]
theorem wf_playAMoveAt {pw} {g : Game pw}
[hs : AState pw g.s] : (playAMoveAt g).s.WF pw := by
  rw [aState_iff'] at hs; choose hs ht using hs
  by_cases h : ¬g.s.act
  · rw [Game.playAMoveAt_eq_of_neg # by tauto]
    simpa [State.finish_eq_of_not_act h]
  push Not at h
  rw [State.wf_iff] at hs ⊢
  choose a d n g₁ h₁ h₂ using hs
  rcases h₂ with h₂ | ⟨h', h₂⟩
  · have h₀ : g₁.s.act; simpa [h₂]
    contrapose h₂; clear h₂
    apply ne_of_congr (·.aTurn)
    simp [ht]
    rw [←h₁]
    rw [Game.aTurn_play_eq_of_act]; simp
    simpa [h₁]
  generalize hg₀ : (initGame (a.set g.s g.a) d state₀).play n = g₀
  generalize hg' : (initGame (a.set g.s g.a) d state₀).play (n + 1) = g'
  refine' ⟨_, d, n + 1, g', hg', _⟩; left
  have h₄ : g₀.s = g₁.s
  · rw [←hg₀, ←h₁]
    apply Game.s_play_initGame_a_set_eq_of_ne
    intro k hk H₁
    apply ne_of_congr (·.history.length)
    simp [←h₂, ←h₁]
    rw [Game.length_history_play_eq_of_act H₁]
    rw [Game.length_history_play_eq_of_act # by rwa [h₁]]
    simp; omega
  simp [hg₀] at hg'
  have h₀ : g₀.s.act; simpa [Game.act, h₄]
  generalize hgx : playAMoveAt g = gx
  generalize hgy : playDMoveAt g₀ h₀ = gy
  replace hg' : playAMoveAt gy = g'
  · rw [←hg']; simp [Game.playMove, h₀, hgy]
  have Hd₀ : g₀.d = d; simp [←hg₀]
  have Hd₁ : g₁.d = d; simp [←h₁]
  have H₁ : gy.s = g.s
  · simp [←hgy, ←h₂, Hd₀, Hd₁]; rw! [h₄]; rfl
  have H₂ : gy.s.act; simp [←hgy]
  by_cases H₃ : ¬AHasValidMove pw g.s.board
  · rw [←hg', Game.playAMoveAt_eq_of_neg # by grind]
    rw [←hgx, Game.playAMoveAt_eq_of_neg # by grind]
    simp [H₁]
  push Not at H₃
  have H₄ : g'.act
  · simp [←hg']
    rw [Game.playAMoveAt_eq_of_pos H₂ # by grind]
    simpa [playAMoveAt']
  have H₅ : gx.act
  · rw [←hgx]; rwa [Game.playAMoveAt_eq_of_pos h H₃]
  simp [←hg', ←hgx]
  rw [Game.s_playAMoveAt_eq_iff_of_act_playAMoveAt (by grind) (by grind)]
  rw! [H₁]; congr 2; simp [←hgy, ←hg₀, A.set]

@[simp, instance]
theorem Game.wf_playMove {pw} {g : Game pw}
[hs : DState pw g.s] : g.playMove.s.WF pw := by
  simp [playMove]; split_ifs <;> infer_instance

theorem Game.playAMoveAt_eq_of_act {pw} {g : Game pw}
(h : (playAMoveAt g).act) : playAMoveAt g = playAMoveAt' g.a g
(act_of_act_playAMoveAt h) (aHasValidMove_of_act_playAMoveAt h) := by
  simp [playAMoveAt, act_of_act_playAMoveAt h, aHasValidMove_of_act_playAMoveAt h]

theorem Game.aTurn_playAMoveAt_of_act {pw} {g : Game pw}
(h : (playAMoveAt g).act) : (playAMoveAt g).s.aTurn = !g.s.aTurn := by
  simp [playAMoveAt_eq_of_act h]

theorem dState_playAMoveAt_of_act {pw} {g : Game pw} [hs : AState pw g.s]
(h : (playAMoveAt g).s.act) : DState pw (playAMoveAt g).s := by
  constructor; simp [Game.aTurn_playAMoveAt_of_act h]

theorem Game.dState_playMove_of_act {pw} {g : Game pw}
[hs : DState pw g.s] (h : g.playMove.act) : DState pw g.playMove.s := by
  constructor; rw [aTurn_playMove_eq_of_act h, hs.ht]

@[simp, instance]
theorem Game.wf_play {pw} {g : Game pw} {n} [hs : DState pw g.s] : (g.play n).s.WF pw := by
  induction n; simp; infer_instance
  nm n ih; simp; by_cases h₁ : (g.play n).s.act
  · suffices : DState pw (g.play n).s; infer_instance
    constructor; rw [aTurn_play_eq_of_act h₁, hs.ht]
  rwa [playMove_eq_of_not_act h₁]

theorem Game.dState_play_of_act {pw} {g : Game pw} {n}
[hs : DState pw g.s] (h : (g.play n).act) : DState pw (g.play n).s := by
  constructor; rw [aTurn_play_eq_of_act h, hs.ht]

theorem not_dHws_of_aHws {pw} (h : AHws pw) : ¬DHws pw := by
  obtain ⟨a, h⟩ := h; simp [DHws, DHwsAt]
  intro d; use a; specialize h d; exact h

theorem not_aHws_of_dHws {pw} (h : DHws pw) : ¬AHws pw := by
  contrapose! h; exact not_dHws_of_aHws h

@[simp, instance]
theorem State.wf_toAltH_state₀ {pw} : sys.WF # state₀.toAltH pw := by
  simp

@[simp, instance]
theorem State.wf_getd_toAltH?_state₀ {pw} : sys.WF # state₀.toAltH? pw |>.getd :=
  wf_toAltH_state₀

@[simp]
theorem State.even_length_history_of_dState {pw s} [hs : DState pw s] :
Even s.history.length := by
  have h := hs.ht; simp [aTurn] at h; exact h

@[simp]
theorem State.not_odd_length_history_of_dState {pw s} [hs : DState pw s] :
¬Odd s.history.length := by simp

@[simp]
theorem State.aTurn_eq_of_DState {pw s} [hs : DState pw s] : s.aTurn = false := by
  simp [aTurn]

theorem Board.getd_toAltH?_eq_toAlt_of {pw t₁ t₂} {b₁ b₂ : Board}
(h : ∃ s₁ s₂, sys.WF s₁ ∧ sys.WF s₂ ∧ b₁.toAlt pw t₁ s₁.hist = s₁ ∧
b₂.toAlt pw t₂ s₂.hist = s₂ ∧ s₁ = s₂.setHist s₁.hist) :
∃ hist, (b₁.toAltH? pw t₁).getd = b₂.toAlt pw t₂ hist := by
  choose s₁ s₂ hs₁ hs₂ h₁ h₂ h₃ using h
  have h₄ : ∃ s, sys.WF s ∧ b₁.toAlt pw t₁ s.hist = s; tauto
  have h₅ := τ_spec h₄
  generalize h₆ : (τ _, _ : AP.State) = s at h₅
  choose hs h₅ using h₅; use s.hist
  rw [toAltH?, choose?_eq_of_pos h₄, h₆]
  clear h₆; simp; rw [←h₅]
  generalize s₁.hist = ps₁ at *
  generalize s₂.hist = ps₂ at *
  generalize s.hist = ps at *
  subst h₂ h₃ h₅
  simp [AP.State.ext_iff] at h₁ ⊢
  rcases h₁ with ⟨H₁, H₂, rfl⟩
  simp [H₁, H₂]

theorem Board.toAlt_eq_setHist {s : State} {pw t hist} (hist₁ : List PointZ) :
s.board.toAlt pw t hist = (s.board.toAlt pw t hist₁).setHist hist := rfl

theorem Board.toAlt_eq_setHist_nil {s : State} {pw t hist} :
s.board.toAlt pw t hist = (s.board.toAlt pw t []).setHist hist := rfl

theorem State.exi_wf_toAlt_board_iff_exi_hist {pw t} {s : State} :
(∃ s₁, sys.WF s₁ ∧ s.board.toAlt pw t s₁.hist = s₁) ↔
∃ hist, sys.WF (s.board.toAlt pw t hist) := by
  constructor
  · rintro ⟨s₁, hs₁, h₁⟩; use s₁.hist; rwa [h₁]
  · rintro ⟨hist, h⟩; use s.board.toAlt pw t hist, h; simp

theorem State.exi_hist_toAlt_board_of_wfCnd {pw t} {s : State}
(h : WFCnd # s.board.toAlt pw t []) : ∃ hist, sys.WF # s.board.toAlt pw t hist := by
  conv => right; ext; rw [Board.toAlt_eq_setHist_nil]
  exact AP.State.exi_hist_wf_of_wfCnd h

theorem State.exi_wf_toAlt_board_of_wfCnd {pw t} {s : State}
(h : WFCnd # s.board.toAlt pw t []) :
∃ s₁, sys.WF s₁ ∧ s.board.toAlt pw t s₁.hist = s₁ := by
  rw [exi_wf_toAlt_board_iff_exi_hist]; exact exi_hist_toAlt_board_of_wfCnd h

@[simp]
theorem Game.squares_board_playAMoveAt {pw} {g : Game pw} :
(playAMoveAt g).s.board.squares = g.s.board.squares := by
  rw [playAMoveAt]; split_ifs <;> rfl

theorem State.finite_univ_diff_squares_of_play' {pw} {a : A pw} {d n g s}
(h₁ : (Set.univ \ s.board.squares).Finite) (h₂ : (initGame a d s).play n = g) :
(Set.univ \ g.s.board.squares).Finite := by
  induction n generalizing s
  · simp at h₂; simpa [←h₂]
  nm n ih
  rw [Game.play_succ'] at h₂
  generalize hg₀ : (initGame a d s).playMove = g₀ at h₂
  apply @ih g₀.s
  rotate_left
  · convert h₂
    subst hg₀
    ext :1 <;> simp
  subst hg₀
  simp [Game.playMove]
  split_ifs with h₃; on_goal 2 => simpa
  simp [playDMoveAt, applyDMove, applyDMoveB]
  split; assumption; simpa

@[simp]
theorem State.finite_univ_diff_squares_of_play {pw} {a : A pw} {d n g}
(h : (initGame a d state₀).play n = g) : (Set.univ \ g.s.board.squares).Finite := by
  apply finite_univ_diff_squares_of_play' _ h; simp

@[simp]
theorem State.finite_univ_diff_squares {s pw} [hs : WF pw s] :
.univ \ s.board.squares |>.Finite := by
  rw [wf_iff] at hs; obtain ⟨a, d, n, g, h₁, h₂⟩ := hs
  have h₃ := finite_univ_diff_squares_of_play h₁
  rcases h₂ with rfl | ⟨h₂, rfl⟩; exact h₃
  simp [playDMoveAt, applyDMove, applyDMoveB]
  split; exact h₃; simpa

@[simp]
theorem State.finite_image_univ_diff_squares {s pw} [hs : WF pw s] :
(·.toAlt) '' (.univ \ s.board.squares) |>.Finite := by
  apply Set.Finite.image; simp

@[simp]
theorem State.mem_ofSet_image_univ_diff_squares {s pw p} [hs : WF pw s] :
p ∈ Set'.ofSet ((·.toAlt) '' (.univ \ s.board.squares)) ↔
p ∈ (·.toAlt) '' (.univ \ s.board.squares) := by
  simp [Set'.mem_ofSet]

@[simp]
theorem Point.toAlt_eq_iff {a b : Point} : a.toAlt = b.toAlt ↔ a = b := by
  symm; constructor; rintro rfl; rfl
  intro h; simp [toAlt] at h; ext <;> tauto

@[simp]
theorem wf_state₀ {pw} : State.WF pw state₀ := by
  rw [State.wf_iff]; use default, default, 0; simp

theorem Game.aTurn_playMove_iff {pw} {g : Game pw} (ha : g.s.act) (ht : g.s.aTurn = false) :
g.playMove.s.aTurn = haveI := Classical.propDecidable; !decide g.playMove.act := by
  simp [playMove, ha]; simp [playAMoveAt]; split_ifs with h₁ <;> simp_all; tauto

theorem Game.aTurn_play_iff {pw} {g : Game pw} {n} (ha : g.s.act) (ht : g.s.aTurn = false) :
(g.play n).s.aTurn = haveI := Classical.propDecidable; !decide (g.play n).act := by
  induction n generalizing g
  · simpa [ht]
  nm n ih; simp; by_cases h₁ : (g.play n).act
  · rw [aTurn_playMove_iff h₁]
    contrapose h₁; simp at h₁
    simpa [ih ha ht]
  · rw [playMove_eq_of_not_act h₁, ih ha ht]
    congr 2
    replace h₁ : (g.play n).act = False
    · grind
    rw [h₁]
    simp
    rw [playMove_eq_of_not_act] <;> tauto

@[simp]
theorem Game.length_history_le_playAMoveAt {pw} {g : Game pw} :
g.s.history.length ≤ (playAMoveAt g).s.history.length := by
  simp [playAMoveAt]; split_ifs <;> simp

@[simp]
theorem Game.length_history_le_playDMoveAt {pw} {g : Game pw} {h} :
g.s.history.length ≤ (playDMoveAt g h).s.history.length := by
  simp [playDMoveAt]

@[simp]
theorem Game.length_history_le_playMove {pw} {g : Game pw} :
g.s.history.length ≤ g.playMove.s.history.length := by
  simp [playMove]
  split_ifs with h; on_goal 2 => rfl
  apply length_history_le_playAMoveAt.trans'
  simp

@[simp]
theorem Game.length_history_le_play {pw} {g : Game pw} {n} :
g.s.history.length ≤ (g.play n).s.history.length := by
  induction n generalizing g <;> simp; nm n ih
  apply length_history_le_playMove.trans' ih

theorem Game.length_hist_play_le_of_le {pw} {g : Game pw} {k n}
(h : k ≤ n) : (g.play k).s.history.length ≤ (g.play n).s.history.length := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; simp

@[simp]
theorem Game.length_hist_lt_playMove_iff_act {pw} {g : Game pw} :
g.s.history.length < g.playMove.s.history.length ↔ g.s.act := by
  constructor
  · contrapose!; intro h
    rw [playMove_eq_of_not_act h]
  intro h
  simp [playMove, h]
  apply lt_of_lt_of_le (b := playDMoveAt g h |>.s.history.length)
  · simp
  · simp only [length_history_le_playAMoveAt]

theorem Game.length_hist_play_lt_of_lt_and_act {pw} {g : Game pw} {k n}
(h₁ : k < n) (h₂ : (g.play k).act) :
(g.play k).s.history.length < (g.play n).s.history.length := by
  rw [←Nat.add_one_le_iff] at h₁ ⊢
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  simp only [play_add, play_succ]
  apply length_history_le_play.trans'; simpa

@[simp]
theorem Game.setState_inj {pw} {g : Game pw} {s₁ s₂} :
g.setState s₁ = g.setState s₂ ↔ s₁ = s₂ := by
  simp [setState]

@[simp]
theorem A.f_set_of_eq {pw} {a a₀ : A pw} {s} : (a.set s a₀).f s = a₀.f s := by
  simp [set]

@[simp]
theorem D.f_set_of_eq {d d₀ : D} {s} : (d.set s d₀).f s = d₀.f s := by
  simp [set]

@[simp]
theorem Game.playAMoveAt'_set_of_eq {pw} {g : Game pw} {a a₀ : A pw} {h₁ h₂} :
playAMoveAt' (a.set g.s a₀) g h₁ h₂ = playAMoveAt' a₀ g h₁ h₂ := by
  simp [playAMoveAt']

@[simp]
theorem Game.playAMoveAt_initGame_a_set_of_eq {pw} {a a₀ : A pw} {d s} :
(playAMoveAt # initGame (a.set s a₀) d s).s = (playAMoveAt # initGame a₀ d s).s := by
  simp [playAMoveAt]
  split_ifs with h₁ h₂ h₂ <;> try tauto
  simp [playAMoveAt']

@[simp]
theorem Game.playDMoveAt_initGame_d_set_of_eq {pw} {a : A pw} {d d₀ : D} {s} {h} :
(playDMoveAt (initGame a (d.set s d₀) s) h).s = (playDMoveAt (initGame a d₀ s) h).s := by
  simp

@[simp] theorem Game.initGame_self {pw} {g : Game pw} : initGame g.a g.d g.s = g := rfl
theorem Game.eq_initGame {pw} {g : Game pw} : g = initGame g.a g.d g.s := rfl

@[simp]
theorem Game.s_playAMoveAt_congr {pw} {g : Game pw} {d} :
(playAMoveAt # initGame g.a d g.s).s = (playAMoveAt g).s := by
  simp [playAMoveAt]; split_ifs <;> tauto

@[simp]
theorem Game.s_playDMoveAt_congr {pw} {g : Game pw} {a} {h} :
(playDMoveAt (initGame a g.d g.s) h).s = (playDMoveAt g h).s := by
  simp

theorem Game.act_play_of_le {pw} {g : Game pw} {n k}
(h₁ : (g.play n).act) (h₂ : k ≤ n) : (g.play k).act := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₂
  simp at h₁; exact act_of_act_play h₁

theorem Game.wf_playAMoveAt' {pw} {g : Game pw} [hs : State.WF pw g.s]
(h : g.s.aTurn) : State.WF pw (playAMoveAt g).s := by
  obtain ⟨a, d, n, g₁, h₁, h₂ | ⟨h₂, h₃⟩⟩ := id hs
  · rw [←h₂, ←h₁] at h
    rw [aTurn_play_iff (by simp) (by simp)] at h
    simp at h
    have h₃ : ¬g.s.act
    · rwa [←h₂, ←h₁]
    rw [playAMoveAt_eq_of_neg (by tauto)]
    rwa [finish_eq_of_not_act h₃]
  have h₂' : g₁.s.act := h₂
  generalize ha' : a.set g.s g.a = a'
  refine' ⟨a', d, n + 1, initGame a' d (playAMoveAt g).s, _, _⟩
  simp
  have H₂ : g₁.d = d; simp [←h₁]
  convert_to (initGame a' d g₁.s).playMove = _
  on_goal 3 => simp
  · subst ha'
    congr
    ext:1 <;> simp
    rw [←h₁]
    rw [s_play_initGame_a_set_eq_of_ne]
    intro k hk h₅
    apply ne_of_congr (·.history.length)
    simp [←h₃, ←h₁]
    apply ne_of_lt
    rw [←Nat.add_one_le_iff] at hk ⊢
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp only [play_add, play_succ, Order.add_one_le_iff]
    apply length_history_le_play.trans'
    simpa
  · ext:1 <;> simp
    subst ha'
    simp [playMove, h₂]
    simp [playDMoveAt, H₂] at h₃ ⊢
    simp [h₃]

theorem Game.wf_playDMoveAt' {pw} {g : Game pw} [hs : State.WF pw g.s] {hh}
(h : g.s.aTurn = false) : State.WF pw (playDMoveAt g hh).s := by
  obtain ⟨a, d, n, g₁, h₁, h₂ | ⟨h₂, h₃⟩⟩ := id hs
  rotate_left
  · rw [←h₃] at h
    simp at h
    rw [←h₁] at h
    rw [aTurn_play_iff (by simp) (by simp)] at h
    simp [h₁] at h
    tauto
  have h₃ : g₁.s.act; rwa [h₂]
  generalize hd' : d.set g.s g.d = d'
  refine' ⟨a, d', n, initGame a d' g.s, _⟩
  apply and_of
  · subst hd'
    ext:1 <;> simp
    conv => rhs; rw [←h₂, ←h₁]
    apply s_play_initGame_d_set_eq_of_ne
    intro k hk
    apply ne_of_congr (·.history.length)
    rw [length_history_play_eq_of_act]
    rotate_left
    · apply act_play_of_le _ # le_of_lt hk
      rwa [h₁]
    simp
    rw [←h₂, ←h₁]
    rw [length_history_play_eq_of_act (by rwa [h₁])]
    simp; omega
  intro h₄
  right
  simp [hh]
  subst hd'
  simp

@[simp, instance]
theorem Game.wf_playAMoveAt {pw} {g : Game pw} [hs : AState pw g.s] :
State.WF pw (playAMoveAt g).s := by
  apply wf_playAMoveAt'; simp

@[simp, instance]
theorem Game.wf_playDMoveAt {pw} {g : Game pw} [hs : DState pw g.s] {hh} :
State.WF pw (playDMoveAt g hh).s := by
  apply wf_playDMoveAt'; simp

theorem dState_play_initGame_of {pw} {a : A pw} {d s n} [hs : DState pw s]
(h : initGame a d s |>.play n |>.s |>.act) :
DState pw # initGame a d s |>.play n |>.s := by
  generalize hg : (initGame a d s).play n = g at h ⊢
  simp [dState_iff']
  have hs₁ : g.s.WF pw
  · simp [←hg]
    apply Game.wf_play (hs := by simpa)
  simp [hs₁]
  simp [←hg]
  rw [Game.aTurn_play_eq_of_act (by rwa [hg])]
  simp

theorem State.invariant_of_wf {pw s} {p : State → Prop} [hs : WF pw s]
(h₁ : p state₀) (h₄ : ∀ ⦃s⦄, WF pw s → p s → p s.finish)
(h₂ : ∀ ⦃s m⦄, WF pw s → AMoveValid pw s.board m → p s → p (applyAMove s m))
(h₃ : ∀ ⦃s m⦄, WF pw s → DMoveValid s.board m → p s → p (applyDMove s m)) : p s := by
  rw [wf_iff] at hs
  choose a d n g h₄ h₅ using hs
  induction n generalizing g s
  · simp at h₄
    subst h₄
    simp at h₅
    rcases h₅ with rfl | rfl
    · exact h₁
    apply h₃ (by simp) _ h₁
    exact d.f state₀ (by simp) |>.2
  nm n ih
  simp at h₄
  generalize hg : (initGame a d state₀).play n = g at h₄
  subst h₄
  specialize @ih g.s g hg
  simp at ih
  have h₆ : p g.playMove.s
  · simp [Game.playMove]
    split_ifs with h₆; on_goal 2 => exact ih
    generalize hs' : (playDMoveAt g h₆).s = s'
    rw [playAMoveAt]
    have hs : WF pw g.s
    · use a, d, n, g, hg; simp
    have h₈ : p s'
    · subst hs'
      apply h₃ hs _ ih
      convert d.f g.s h₆ |>.2
      simp [←hg]
    have hs₁ : WF pw s'
    · subst hs'
      apply Game.wf_playDMoveAt'
      simp [←hg]
      rw [Game.aTurn_play_eq_of_act]; rfl
      rwa [hg]
    split_ifs with h₇
    rotate_left
    · subst hs'; exact h₄ hs₁ h₈
    rcases h₇ with ⟨h₇, h₉⟩
    apply h₂ (by rwa [hs']) _ (by rwa [hs'])
    simp [hs'] at h₉ ⊢
    rw [Game.act, hs'] at h₇
    rw! [hs']
    convert a.f s' h₇ h₉ |>.2
    simp [←hg]
  rcases h₅ with rfl | ⟨h₅, rfl⟩
  · exact h₆
  apply h₃ _ _ h₆
  · suffices : DState pw g.s; infer_instance
    rw [←hg]
    apply dState_play_initGame_of (hs := dState_state₀)
    simp [hg]
    exact Game.act_of_act_playMove h₅
  convert d.f _ _ |>.2
  · simp [←hg]
  · exact h₅

theorem Board.invariant_of_wf {pw s} {p : Board → Prop} [hs : State.WF pw s] (h₁ : p board₀)
(h₂ : ∀ ⦃b m⦄, AMoveValid pw b m → p b → p (applyAMoveB b m))
(h₃ : ∀ ⦃b m⦄, DMoveValid b m → p b → p (applyDMoveB b m)) : p s.board := by
  apply s.invariant_of_wf <;> tauto

@[simp]
theorem dMoveValid_some_iff {b p} : DMoveValid b (some p) ↔ p ≠ b.A ∧ p ∈ b.squares := by rfl

theorem dMoveValid_iff {b m} : DMoveValid b m ↔ m = none ∨
∃ p, m = some p ∧ p ≠ b.A ∧ p ∈ b.squares := by
  cases m <;> simp

@[simp] theorem Board.a_applyAMoveB {b m} : (applyAMoveB b m).A = m := rfl

@[simp] theorem Board.a_applyDMoveB {b m} : (applyDMoveB b m).A = b.A := by
  cases m <;> rfl

@[simp]
theorem Board.squares_applyAMoveB {b m} : (applyAMoveB b m).squares = b.squares := rfl

@[simp]
theorem Board.squares_applyDMoveB {b m} :
(applyDMoveB b m).squares = b.squares \ m.elim ∅ ({·}) := by
  cases m <;> simp [applyDMoveB]

theorem State.a_mem_squares_of_wf {pw s} [hs : WF pw s] : s.board.A ∈ s.board.squares := by
  apply Board.invariant_of_wf (p := λ b => b.A ∈ b.squares) <;> clear! s; simp
  · simp [AMoveValid]; tauto
  · intro b m h₁ h₂
    simp [dMoveValid_iff] at h₁
    simp
    cases m <;> simp_all
    tauto

@[simp]
theorem squares_board_applyAMove {s m} :
(applyAMove s m).board.squares = s.board.squares := rfl

theorem Game.lt_of_not_act_play {pw} {g : Game pw} {n k}
(h₁ : (g.play k).s.act) (h₂ : ¬(g.play n).s.act) : k < n := by
  by_contra! h₃
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₃; clear h₃
  apply h₂; clear h₂
  apply act_play_of_le h₁
  simp

@[simp]
theorem Game.state_playDMoveAt_ne_self {pw} {g : Game pw} {h} : (playDMoveAt g h).s ≠ g.s := by
  apply ne_of_congr (·.history.length); simp

@[simp]
theorem Game.playDMoveAt_ne_self {pw} {g : Game pw} {h} : playDMoveAt g h ≠ g := by
  apply ne_of_congr (·.s); simp

@[simp]
theorem Game.play_initGame_aTurn_eq_true_iff_not_act {pw} {a : A pw} {d n} :
(initGame a d state₀ |>.play n |>.s.aTurn) ↔ ¬(initGame a d state₀ |>.play n).s.act := by
  symm; constructor
  · contrapose
    simp
    intro h
    apply act_play_initGame_of_not_aTurn (h₃ := rfl) <;> simp_all
  intro h
  induction n
  · simp at h
  nm n ih
  simp at h ⊢
  generalize hg : (initGame a d state₀).play n = g at ih h ⊢
  intro h₁
  rw [aTurn_playMove_eq_of_act h₁] at h
  specialize ih h
  apply ih; clear ih
  exact act_of_act_playMove h₁

@[simp]
theorem Game.play_initGame_aTurn_eq_false_iff_act {pw} {a : A pw} {d n} :
(initGame a d state₀ |>.play n |>.s.aTurn) = false ↔
(initGame a d state₀ |>.play n).s.act := by
  contrapose; simp

-- #check 0 #exit

-- theorem aState_iff {pw s} : AState pw s ↔ ∃ a d n g h,
-- (initGame a d state₀ : Game pw).play n = g ∧ (playDMoveAt g h).s = s := by
--   rw [aState_iff', State.wf_iff]
--   symm; constructor
--   ·
--     rintro ⟨a, d, n, g, h₁, h₂, rfl⟩
--     symm; split_ands
--     ·
--       simp
--       rw [←h₂]
--       simp; grind
--     use a, d, n, g, h₂
--     simp [h₁]
--   
--   rintro ⟨⟨a, d, n, g, h₁, h₂⟩, ht⟩
--   use a, d
--   by_cases h₃ : g.s.act
--   ·
--     use n, g, h₃, h₁
--     rcases h₂ with rfl | h₂
--     on_goal 2 => tauto
--     exfalso
--     rw [←h₁] at ht
--     simp at ht
--     simp [h₁, h₃] at ht
--   
--   induction n generalizing g
--   
--   ·
--     simp [←h₁] at h₃
--   
--   nm n ih
--   
--   simp at h₁
--   generalize hg : (initGame a d state₀).play n = g at h₁; nm g₁
--   specialize ih g hg
--   
--   simp [h₃] at h₂
--   subst h₂
--   
--   sorry
-- 
-- #check 0 #exit

-- @[simp]
-- theorem State.exi_not_mem_squares_of_aState {pw s} [hs : AState pw s] :
-- ∃ p, p ∉ s.board.squares := by
--   rw [aState_iff'] at hs
--   obtain ⟨hs, ht⟩ := hs
--   rw [wf_iff] at hs
--   choose a d n g h₁ h₂ using hs
--   cases n
--   ·
--     simp at h₁
--     subst h₁
--     simp at h₂
--     rcases h₂ with ⟨⟩
-- 
-- #check 0 #exit
-- 
-- theorem State.exi_toAlt_board_of_wf {pw s} [hs : WF pw s] :
-- ∃ s₁, sys.WF s₁ ∧ s.board.toAlt pw s.aTurn s₁.hist = s₁ := by
--   -- cases hs; nm hs ht
--   apply exi_wf_toAlt_board_of_wfCnd
--   constructor <;> simp; exact a_mem_squares_of_wf
--   ·
--     intro h; replace hs : AState pw s; use h; clear h
--     simp [Set'.eq_empty_iff]
--   -- intro p hp
--   -- simp [AP.State.aMove]
--   -- revert p ht hp
--   -- apply s.invariant_of_wf; iterate 2 simp
--   -- all_goals clear! s
--   -- ·
--   --   rintro s m hs h₁ - h₃ p hp
--   --   simp [applyAMove] at h₃ hp ⊢
--   --   choose h₁ h₄ h₅ using h₁
--   --   use s.board.A.toAlt
--   --   simp [h₁]
--   --   use a_mem_squares_of_wf
--   --   rw [dist_eq_alt] at h₄
--   --   simp at h₄
--   --   rwa [Point.dist_comm]
--   -- rintro s m hs h₁ - h₃ p hp
--   -- simp [applyDMove] at h₃ hp ⊢
--   -- 
--   -- replace hs : AState pw s; use h₃
--   -- clear h₃
--   -- 
--   -- cases m <;> simp at hp ⊢
--   -- ·
--   --   clear h₁
--   -- ·
--   --   nm p₁
--   --   simp at h₁
-- 
-- #check 0 #exit
-- 
-- -- theorem State.exi_toAlt_board_of_dState {pw s t} [hs : DState pw s] :
-- -- ∃ s₁, sys.WF s₁ ∧ s.board.toAlt pw t s₁.hist = s₁ := by
-- 
-- -- #check 0 #exit
-- 
-- -- theorem Game.toAltH_playDMoveAt_of_none {pw} {g : Game pw} {h} [hs : DState pw g.s]
-- -- (h₁ : (g.d.f g.s h).m = none) : ∃ hist,
-- -- (playDMoveAt g h).s.toAltH pw = g.s.toAlt pw hist := by
-- --   simp [playDMoveAt, applyDMove, applyDMoveB, h₁, applyMove,State.toAltH,
-- --     State.toAltH?, State.toAlt]
-- --   
-- --   congr 1
-- --   apply Board.getd_toAltH?_eq_toAlt_of
-- --   simp_rw [State.toAlt_eq]
-- 
-- -- #check 0 #exit
-- 
-- -- theorem dHws_and_dwn_lt_toAltH_playDMoveAt_dOptimal_of_dHws {pw} {g g₁ : Game pw} {h}
-- -- [hs : DState pw g.s]
-- -- (h₁ : g.d = (dOptimal pw).getd)
-- -- (h₂ : g.s.toAltH pw |>.dHws)
-- -- (hg₁ : playDMoveAt g h = g₁) :
-- -- (g₁.s.toAltH pw).dHws ∧ g₁.s.dwn pw < g.s.dwn pw := by
-- --   split_ands
-- --   ·
-- --     simp [←hg₁]
-- -- 
-- -- #check 0 #exit
-- -- 
-- -- theorem DHws_of_alt {pw} (h : AP.dHwsPw pw) : DHws pw := by
-- --   specialize h 0
-- --   generalize h₀ : state₀ = s
-- --   
-- --   replace h : s.toAltH pw |>.dHws
-- --   ·
-- --     subst h₀
-- --     simp [State.toAltH, State.toAltH?, Board.toAltH?]
-- --     
-- --     apply choose?_of_pos (P := λ (x : Option AP.State) => x.getd.dHws) _ _
-- --     ·
-- --       use AP.initState pw 0
-- --       simp
-- --     
-- --     rintro s - ⟨hs, h₂⟩
-- --     simp at h₂ ⊢
-- --     rw [setHist_eq_comm] at h₂
-- --     simp at h₂
-- --     rw [←h₂] at h
-- --     
-- --     have h₁ : sys.WF # s.setHist [0]
-- --     ·
-- --       simp [h₂]
-- --     
-- --     simp at h
-- --     exact h
-- --   
-- --   have h₁ : s.toAltH pw = AP.initState pw 0
-- --   ·
-- --     simp [←h₀]
-- --   
-- --   generalize hn : s.dwn pw = n
-- --   generalize h₂ : (dOptimal pw).getd = d
-- --   use d
-- --   intro a
-- --   have hs : sys.WF # s.toAltH pw; simp [h₁]
-- --   
-- --   rw [h₀]
-- --   have h₃ : s.act
-- --   ·
-- --     rw [←h₀]
-- --     simp
-- --   
-- --   have ht : s.aTurn = false
-- --   ·
-- --     simp [←h₀]
-- --   
-- --   clear h₀ h₁
-- --   
-- --   use n
-- --   
-- --   induction n using Nat.strong_induction_on generalizing s
-- --   nm n ih
-- --   cases n
-- --   ·
-- --     contrapose! hn
-- --     simpa [State.dwn_eq, State.dwn_eq_zero_iff_aHws]
-- --   nm n
-- --   simp at ih
-- --   
-- --   rw [Game.play_succ', Game.playMove]
-- --   simp [h₃, playAMoveAt]
-- --   rw! [eq_true_of Game.act_playDMoveAt]
-- --   rw! (castMode := .all) [true_and]
-- --   
-- --   split_ifs with h₄
-- --   on_goal 2 => simp
-- --   
-- --   generalize_proofs H₁ H₂ H₃
-- --   by_contra H
-- --   generalize hg₁ : playDMoveAt (initGame a d s) H₁ = g₁
-- --   contrapose H; clear H
-- --   rw! [hg₁] at h₄ ⊢
-- --   
-- --   have ht₁ : g₁.s.aTurn = true
-- --   ·
-- --     clear ih
-- --     subst hg₁
-- --     simpa
-- --   
-- --   obtain ⟨h₅, h₆⟩ : (g₁.s.toAltH pw).dHws ∧ g₁.s.dwn pw < s.dwn pw
-- --   ·
-- --     clear ih
-- --     apply @dHws_and_dwn_lt_toAltH_playDMoveAt_dOptimal_of_dHws pw (initGame a d s) g₁
-- --     simp [h₂]; all_goals simpa
-- --   
-- --   have hs₁ : sys.WF # g₁.s.toAltH pw
-- --   ·
-- --     clear ih
-- --     simp [←hg₁]
-- --   
-- --   -- specialize ih _ (by omega) g₁.s h₅ rfl hs₁ (by simpa [←hg₁])
-- 
-- -- theorem Game.toAltH_playDMoveAt {pw} {g : Game pw} {h} [hs : DState pw g.s] :
-- -- ∃ hist s', (g.s.toAltH pw).dMove (Point.toAlt # g.d.f g.s h) = some s' ∧
-- -- (playDMoveAt g h).s.toAltH pw = s'.setHist hist
-- -- 
-- -- #check 0 #exit
-- 
-- -- @[simp, instance]
-- -- theorem State.wf_toAltH {pw} {s : State} [hs : s.WF pw] : sys.WF # s.toAltH pw := by
-- --   rw [wf_iff] at hs
-- --   choose a d n g h₁ h₂ using hs
-- --   induction n generalizing g
-- --   ·
-- --     simp at h₁
-- --     simp [←h₁] at h₂
-- --     rcases h₂ with rfl | ⟨h', h₂⟩; simp
-- 
-- -- @[simp]
-- -- theorem State.pw_toAltH {pw} {s : State} : (s.toAltH pw).pw = pw := by
-- --   unfold toAltH toAltH? Board.toAltH?