import AP.AP.Defense

namespace AP.King

def state₀ : State :=
  initState 1 0

def interior₁ : Set' PointZ :=
  (0 : PointZ).nbhd Box.offset

def dKingOp₂ : DStrat := .mk # λ s => List.head? # do
  let p ← Box.interior.toList
  guard # p ≠ s.aPos ∧ p ∉ s.taken
  return p

def dKingOp₁ : DStrat :=
  Box.defense.st dKingOp₂

def dKingOp : DStrat := .mk' # λ s =>
  match Box.guardTiles \ s.taken |>.erase s.aPos |>.toList.head? with
  | none => dKingOp₁.f s
  | some p => p

-----

@[simp]
instance : dKingOp₂.WF := by
  unfold dKingOp₂; infer_instance

@[simp]
instance : dKingOp₁.WF := by
  unfold dKingOp₁; infer_instance

@[simp]
instance : dKingOp.WF := by
  unfold dKingOp
  rw [DStrat.wf_iff]
  intro s hs
  dsimp
  split; exact DStrat.validTr s
  nm x p h; clear x
  rw [List.head?_eq_some_iff] at h
  choose xs h using h
  rw [DState.validTr_iff]
  split_ands
  · rintro rfl
    contrapose! h
    apply ne_of_congr (s.aPos ∈ ·)
    simp
  · contrapose! h
    apply ne_of_congr (∃ x ∈ ·, x ∈ s.taken)
    simp; tauto

@[simp]
instance : sys.WF state₀ := by
  unfold state₀; infer_instance

theorem dWins_dKingOp {a : AStrat} [ha : a.WF] : state₀.dWins ⟨a, dKingOp⟩ := by
  sorry