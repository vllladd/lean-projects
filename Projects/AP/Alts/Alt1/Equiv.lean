import Projects.AP.Alts.Alt1.Auxi

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
  apply choose?_of (P := λ (s : Option AP.State) => s.getd = _) _ _
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
  apply choose?_of (P := λ (x : Option AP.State) => x.getd.aHws ↔ _) _ _
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
--     apply choose?_of (P := λ (x : Option AP.State) => x.getd.dHws) _ _
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