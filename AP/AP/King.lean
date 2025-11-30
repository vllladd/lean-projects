import AP.AP.Defense

namespace AP.King

def state₀ : State :=
  initState 1 0

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

end King

theorem AState.aPos_dist_le_of_tr {s s' p} [hs : AState s]
(h : sys.tr s p = some s') : s'.aPos.dist s.aPos ≤ s.pw := by
  simp [hs.tr_eq_some_iff] at h; grind

theorem State.aPos_dist_le_of_simulate_two {s r f} [hs : sys.WF s]
(h : sys.simulate f s 2 = r) : r.1.aPos.dist s.aPos ≤ s.pw := by
  rcases r with ⟨s₂, r⟩; dsimp
  simp [System.simulate] at h
  split at h; simp at h; simp [←h]
  nm x s₁ h₁
  replace hs := s.aState_or_dState
  rcases hs with hs | hs
  · have hs₁ := DState.of_tr h₁
    have h₂ := hs.aPos_dist_le_of_tr h₁
    split at h
    · nm x h₃; clear x
      simp at h; simpa [←h]
    nm x s₂ h₃; clear x
    simp at h
    rcases h with ⟨rfl, rfl⟩
    rwa [DState.aPos_eq_of_tr h₃]
  · have hs₁ := AState.of_tr h₁
    have h₂ := hs.aPos_eq_of_tr h₁
    split at h
    · nm x h₃; clear x
      simp at h
      rcases h with ⟨rfl, rfl⟩
      simp [h₂]
    nm x s₂ h₃; clear x
    simp at h
    rcases h with ⟨rfl, rfl⟩
    rw [←h₂]
    rw [←pw_eq_of_tr h₁]
    exact AState.aPos_dist_le_of_tr h₃

theorem State.aPos_dist_le_of_simulate_mul_two {s r f n} [hs : sys.WF s]
(h : sys.simulate f s (n * 2) = r) : r.1.aPos.dist s.aPos ≤ s.pw * n := by
  subst r
  induction n
  · simp
  nm n ih
  simp [Nat.add_one_mul, sys.simulate_add]
  generalize hr : sys.simulate f s (n * 2) = r at ih ⊢
  rcases r with ⟨s₁, r⟩
  dsimp at ih ⊢
  generalize hr₁ : sys.simulate f s₁ 2 = r₁
  rcases r₁ with ⟨s₃, r₁⟩
  dsimp
  split_ifs with h₁
  rotate_left; grind
  subst h₁
  simp
  have h₁ := sys.reachable_of_simulate_eq hr
  have hs₁ := sys.wf_of_reachable h₁
  suffices h : s₃.aPos.dist s₁.aPos ≤ s.pw
  · suffices : s₃.aPos.dist s.aPos ≤ s₃.aPos.dist s₁.aPos + s₁.aPos.dist s.aPos; grind
    apply Point.triangle
  simp [←pw_eq_of_reachable h₁]
  exact aPos_dist_le_of_simulate_two (r := ⟨s₃, r₁⟩) hr₁

-- theorem State.aPos_distle_of_simulate_le {s f k n r₁ r₂} [hs : sys.WF s]
-- (h₁ : sys.simulate f s k = r₁) (h₂ : sys.simulate f s n = r₂) (h₃ : k ≤ n) :
-- r₁.1.aPos.dist s.aPos ≤ r₂.1.aPos.dist s.aPos := by
--   obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₃; clear h₃
--   induction n generalizing r₂
--   · simp at h₂; subst h₁ h₂; rfl
--   nm n ih
--   rw [←add_assoc, System.simulate_add] at h₂
--   generalize hr : sys.simulate f s (k + n) = r at h₂
--   rcases r with ⟨s₁, r⟩
--   specialize ih hr
--   simp at h₂
--   split_ifs at h₂ with h₃
--   rotate_left
--   · subst h₂; simpa
--   subst h₃
--   rcases r₂ with ⟨s₂, r₂⟩
--   simp at h₂ ⊢ ih

-- #check 0 #exit

namespace King

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
instance : DState state₀ := by
  unfold state₀; infer_instance

@[simp] theorem pw_state₀ : state₀.pw = 1 := rfl
@[simp] theorem aPos_state₀ : state₀.aPos = 0 := rfl

-- #check 0 #exit

theorem dWins_dKingOp {a : AStrat} [ha : a.WF] : state₀.dWins ⟨a, dKingOp⟩ := by
  let f d n := sys.simulate (Strat.f ⟨a, d⟩) state₀ n
  generalize hr : f dKingOp 200 = r
  rcases r with ⟨s₁, n⟩
  by_cases hn : n ≠ 0
  · use 200; simpa [f, hr]
  push_neg at hn; subst hn
  have hs₁ := DState.of_simulate_mul_two_eq_full (n := 100) hr
  
  have h₁ : ∀ k ≤ 200, (f dKingOp k).1.aPos.dist 0 ≤ 100
  ·
    intro k hk
    generalize hr₁ : f dKingOp k = r₁
    have h₁ := State.aPos_dist_le_of_simulate_mul_two (n := 100) hr
    simp at h₁
    sorry
  
  sorry