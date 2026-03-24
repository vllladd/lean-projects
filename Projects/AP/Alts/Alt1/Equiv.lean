import Projects.AP.Alts.Alt1.Thms

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
theorem State.pw_toAlt {s : State} {pw hist} : (s.toAlt pw hist).pw = pw := rfl

@[simp]
theorem State.taken_toAlt {s : State} {pw hist} : (s.toAlt pw hist).taken =
Set'.ofSet (Set.univ \ s.board.squares |>.image (·.toAlt)) := rfl

@[simp]
theorem State.aPos_toAlt {s : State} {pw hist} : (s.toAlt pw hist).aPos = s.board.A.toAlt := rfl

@[simp]
theorem State.aTurn_toAlt {s : State} {pw hist} : (s.toAlt pw hist).aTurn =
decide (Odd s.history.length) := rfl

@[simp]
theorem State.hist_toAlt {s : State} {pw hist} : (s.toAlt pw hist).hist = hist := rfl

@[simp]
theorem State.board_ofAlt {s act hist} : (State.ofAlt s act hist).board = Board.ofAlt s := rfl

@[simp]
theorem State.history_ofAlt {s act hist} : (State.ofAlt s act hist).history = hist := rfl

@[simp]
theorem State.act_ofAlt {s act hist} : (State.ofAlt s act hist).act ↔ act := by rfl

@[simp]
theorem toAlt_state₀ {pw hist} : state₀.toAlt pw hist = (AP.initState pw 0).setHist hist := by
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

theorem State.toAlt_ofAlt {s : AP.State} {act pw hist₁ hist₂} (h₁ : s.aTurn ↔ Odd hist₁.length) :
(State.ofAlt s act hist₁).toAlt pw hist₂ = (s.setPw pw).setHist hist₂ := by
  ext:1 <;> simp [Set.image_image]; grind

@[simp]
theorem State.board_setHist {s : State} {hist} : (s.setHist hist).board = s.board := rfl

@[simp]
theorem State.history_setHist {s : State} {hist} : (s.setHist hist).history = hist := rfl

@[simp]
theorem State.act_setHist {s : State} {hist} : (s.setHist hist).act = s.act := rfl

theorem Board.ofAlt_toAlt {s : State} {pw hist}
(h₁ : s.finSq) : Board.ofAlt (s.toAlt pw hist) = s.board := by
  ext p :2 <;> simp
  generalize hs : Point.toAlt '' (.univ \ s.board.squares) = set
  have h₂ : set.Finite
  · subst hs; apply h₁.image
  simp [Set'.mem_ofSet h₂]; simp [←hs]

theorem State.ofAlt_toAlt {s : State} {pw hist₁ hist₂} (h₁ : s.finSq) :
State.ofAlt (s.toAlt pw hist₁) s.act hist₂ = s.setHist hist₂ := by
  ext:1 <;> simp [Board.ofAlt_toAlt h₁]