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
  rcases r₁ with ⟨s', r₁⟩
  dsimp
  split_ifs with h₁
  rotate_left; grind
  subst h₁
  simp
  have h₁ := sys.reachable_of_simulate_eq hr
  have hs₁ := sys.wf_of_reachable h₁
  suffices h : s'.aPos.dist s₁.aPos ≤ s.pw
  · suffices : s'.aPos.dist s.aPos ≤ s'.aPos.dist s₁.aPos + s₁.aPos.dist s.aPos; grind
    apply Point.triangle
  simp [←pw_eq_of_reachable h₁]
  exact aPos_dist_le_of_simulate_two (r := ⟨s', r₁⟩) hr₁

theorem DState.aPos_dist_le_div_two_of_simulate {s f n r} [hs : DState s]
(h : sys.simulate f s n = r) : r.1.aPos.dist s.aPos ≤ s.pw * (n / 2) := by
  induction n using Nat.mod_2_ind <;> nm n
  · simp; exact s.aPos_dist_le_of_simulate_mul_two h
  rw [add_comm, System.simulate_add] at h
  split at h; nm x s₁ r₁ h₁; clear x
  split at h; nm x s₂ r₂ h₂; clear x
  simp [System.simulate] at h₁
  convert_to _ ≤ (s.pw * n : ℤ); simp; omega
  split at h₁
  · nm x h₃; clear x
    simp at h₁; rcases h₁ with ⟨rfl, rfl⟩
    simp at h; simp [←h]; grind
  nm x s' h₃; clear x
  simp at h₁; rcases h₁ with ⟨rfl, rfl⟩
  simp at h
  subst h
  simp
  have hs' := AState.of_tr h₃
  rw [←DState.aPos_eq_of_tr h₃, ←pw_eq_of_tr h₃]
  exact s'.aPos_dist_le_of_simulate_mul_two (r := (s₂, r₂)) h₂

theorem AState.of_simulate_mul_two_add_one_eq_full {s s₁ : State}
{st : Strat} {n : ℕ} [hs : DState s]
(h : sys.simulate st.f s (n * 2 + 1) = (s₁, 0)) : AState s₁ := by
  simp at h; obtain ⟨s', h₁, h₂⟩ := h
  have hs' := AState.of_tr h₁
  exact AState.of_simulate_mul_two_eq_full h₂

theorem DState.of_simulate_mul_two_add_one_eq_full {s s₁ : State}
{st : Strat} {n : ℕ} [hs : AState s]
(h : sys.simulate st.f s (n * 2 + 1) = (s₁, 0)) : DState s₁ := by
  simp at h; obtain ⟨s', h₁, h₂⟩ := h
  have hs' := DState.of_tr h₁
  exact DState.of_simulate_mul_two_eq_full h₂

theorem State.aTurn_eq_of_simulate_mul_two_eq_full {s s' f n} [hs : sys.WF s]
(h : sys.simulate f s (n * 2) = (s', 0)) : s'.aTurn = s.aTurn := by
  have hs' : sys.WF s' := sys.wf_of_simulate_eq h
  replace hs := s.aState_or_dState; rcases hs with hs | hs
  · replace hs' := AState.of_simulate_mul_two_eq_full h; simp
  · replace hs' := DState.of_simulate_mul_two_eq_full h; simp

theorem State.size_taken_eq_of_simulate_mul_two_eq_full {s s' f n} [hs : sys.WF s]
(h : sys.simulate f s (n * 2) = (s', 0)) : s'.taken.size = s.taken.size + n := by
  have hs' : sys.WF s' := sys.wf_of_simulate_eq h
  have h₁ := s.length_hist_eq_size_taken_mul_two_add_ite
  have h₂ := s'.length_hist_eq_size_taken_mul_two_add_ite
  have h₃ := aTurn_eq_of_simulate_mul_two_eq_full h
  rw [length_hist_eq_of_simulate_eq h] at h₂
  simp [h₁] at h₂; grind

theorem AState.size_taken_eq_of_tr {s s' p} [hs : AState s]
(h : sys.tr s p = some s') : s'.taken.size = s.taken.size :=
  congrArg (·.size) # AState.taken_eq_of_tr h

theorem DState.size_taken_eq_of_tr {s s' p} [hs : DState s]
(h : sys.tr s p = some s') : s'.taken.size = s.taken.size + 1 := by
  rw [DState.tr_eq_some_iff] at h
  rcases h with ⟨⟨h₁, h₂⟩, rfl⟩
  simp [Set'.size_insert h₂]

theorem State.pw_eq_of_simulate_eq {s f n r} [hs : sys.WF s]
(h : sys.simulate f s n = r) : r.1.pw = s.pw :=
  pw_eq_of_reachable # sys.reachable_of_simulate_eq h

theorem DState.size_taken_diff_eq_of_simulate_full_mul_two {s s' n} {st : Strat}
[hs : DState s] (h : sys.simulate st.f s (n * 2) = (s', 0)) :
(s'.taken \ s.taken).size = n := by
  have hs' := DState.of_simulate_mul_two_eq_full h
  have h₁ := s.length_hist_eq_size_taken_mul_two_add_ite
  have h₂ := s'.length_hist_eq_size_taken_mul_two_add_ite
  rw [Set'.size_diff_eq_of_subset]
  rotate_left; exact taken_subset_of_reachable # sys.reachable_of_simulate_eq h
  simp at h₁ h₂
  rw [State.length_hist_eq_of_simulate_eq h] at h₂
  grind

theorem DState.exi_d_move_not_mem_of_aWins {s} {st : Strat} (set : Set' PointZ)
[hs : DState s] (h : s.aWins st) : ∃ n s', DState s' ∧
sys.simulate st.f s n = (s', 0) ∧ st.d.f s' ∉ set := by
  by_contra! h₁
  replace h₁ : ∀ n s' r, sys.simulate st.f s (n * 2) = (s', r) → r = 0 ∧ st.d.f s' ∈ set
  · intro n s' r h₂
    apply and_of
    · specialize h (n * 2)
      simp [h₂] at h
      exact h
    rintro rfl
    have hs' := DState.of_simulate_mul_two_eq_full h₂
    exact h₁ (n * 2) s' hs' h₂
  have h₂ : ∀ n, (sys.simulate st.f s (n * 2)).1.taken \ s.taken ⊆ set
  · intro n
    induction n
    · simp
    nm n ih
    generalize hr : sys.simulate st.f s (n * 2) = r at ih
    rcases r with ⟨s₁, r⟩
    dsimp at ih
    obtain rfl : r = 0; grind
    simp [add_mul]
    rw [sys.simulate_add, hr]
    simp
    simp [System.simulate]
    split
    · exact ih
    nm x s₂ h₂; clear x
    have hs₁ := DState.of_simulate_mul_two_eq_full hr
    suffices h₃ : s₂.taken \ s.taken ⊆ set
    · split; exact h₃
      nm x s₃ h₄; clear x
      have hs₂ := AState.of_tr h₂
      simpa [AState.taken_eq_of_tr h₄]
    simp at h₂
    suffices h₃ : st.d.f s₁ ∈ set
    · intro p
      specialize ih p
      rw [DState.taken_eq_of_tr h₂]
      simp at ih ⊢
      grind
    have h₃ := taken_subset_of_reachable # sys.reachable_of_simulate_eq hr
    have h₄ := h₁ _ _ _ hr |>.2
    simp at h₄; exact h₄
  specialize h₂ # set.size + 1
  generalize hr : sys.simulate st.f s ((set.size + 1) * 2) = r at h₂
  rcases r with ⟨s₁, r⟩
  obtain rfl := h₁ _ _ _ hr |>.1
  dsimp at h₂
  have h₃ := hs.size_taken_diff_eq_of_simulate_full_mul_two hr
  replace h₂ := Set'.size_le_of_subset h₂
  omega

theorem AState.exi_d_move_not_mem_of_aWins {s} {st : Strat} (set : Set' PointZ)
[hs : AState s] (h : s.aWins st) : ∃ n s', DState s' ∧
sys.simulate st.f s n = (s', 0) ∧ st.d.f s' ∉ set := by
  obtain ⟨s₁, h₁⟩ : ∃ s', sys.tr s (st.a.f s) = some s'
  · specialize h 1
    simp at h
    exact h
  have hs₁ := DState.of_tr h₁
  replace h : s₁.aWins st
  · intro n
    specialize h (n + 1)
    simp [h₁] at h
    exact h
  obtain ⟨n, s₂,hs₂, h₂, h₃⟩ := hs₁.exi_d_move_not_mem_of_aWins set h
  use n + 1, s₂, hs₂
  simpa [h₁, h₂]

theorem State.exi_d_move_not_mem_of_aWins {s} {st : Strat} (set : Set' PointZ)
[hs : sys.WF s] (h : s.aWins st) : ∃ n s', DState s' ∧
sys.simulate st.f s n = (s', 0) ∧ st.d.f s' ∉ set := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs <;> exact hs.exi_d_move_not_mem_of_aWins set h

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
@[simp] theorem taken_state₀ : state₀.taken = ∅ := rfl

theorem dWins_dKingOp₁_of_cnd {s} {a : AStrat} [hs : DState s] [ha : a.WF]
(h : Box.defense.cnd s) : s.dWins ⟨a, dKingOp₁⟩ := by
  by_contra h₁; simp at h₁
  obtain ⟨n, s', hs', h₂, h₃⟩ := s.exi_d_move_not_mem_of_aWins Box.interior h₁
  dsimp at h₃
  simp [dKingOp₁, Defense.st, Option.getD] at h₃
  split at h₃
  · nm x p h₄; clear x
    apply h₃
    apply Box.mem_interior_of_f_eq_some h₄
    · apply Box.mem_interior₁_of_simulate h h₂
    apply Set'.subset_trans (s₂ := s.taken)
    rotate_left
    · apply taken_subset_of_reachable
      exact sys.reachable_of_simulate_eq h₂
    rw [Box.cnd_defense_iff_guardTiles] at h
    exact h.2.2
  nm x h₄; clear x
  simp [dKingOp₂, Option.getD] at h₃
  split at h₃
  · nm x p₁ h₅; clear x
    simp at h₅
    rcases h₅ with ⟨h₅, s₁, h₆⟩
    replace h₅ := List.mem_of_head? h₅
    simp [h₃] at h₅
  nm x h₅; clear x
  simp [List.flatMap_fn_replicate_guard] at h₅
  replace h₅ := List.forall_of_find?_eq_some_imp h₅ # by grind
  simp at h₅
  specialize h₁ (n + 2)
  generalize hr : sys.simulate (Strat.f ⟨a, dKingOp₁⟩) s (n + 2) = r at h₁
  rcases r with ⟨s₂, r⟩
  dsimp at h₁
  subst h₁
  have H₄ := Box.mem_interior₁_of_simulate h hr
  replace H₄ : s₂.aPos ∈ Box.interior
  · exact Set'.mem_of_subset (by simp) H₄
  rw [sys.simulate_add, h₂] at hr
  simp at hr
  obtain ⟨s₁, h₁, h₆⟩ := hr
  have hs₁ := AState.of_tr h₁
  simp [AState.tr_eq_some_iff] at h₆
  rcases h₆ with ⟨⟨H₁, H₂, H₃⟩, h₆⟩
  subst h₆
  dsimp at *
  specialize h₅ _ H₄
  simp [←DState.aPos_eq_of_tr h₁, H₁] at h₅
  apply H₂
  apply Set'.mem_of_subset _ h₅
  exact taken_subset_of_tr h₁

theorem dWins_dKingOp_of_cnd {s} {a : AStrat} [hs : DState s] [ha : a.WF]
(h : Box.defense.cnd s) : s.dWins ⟨a, dKingOp⟩ := by
  have h₁ := Box.guardTiles_subset_taken_of_cnd_defense h
  obtain ⟨n, h₂⟩ := dWins_dKingOp₁_of_cnd (a := a) h
  use n; convert h₂ using 2
  clear h h₂
  rename' h₁ => h
  apply simulate_congr; simp only [implies_true]
  intro k hk sd hsd h₁ h₂ h₃
  simp [dKingOp]
  split; rfl
  nm x p h₄; clear x
  exfalso
  replace h₄ := List.mem_of_head? h₄
  simp at h₄
  specialize h p
  rcases h₄ with ⟨-, h₄, h₅⟩
  simp [h₄] at h
  apply h₅; clear h₅
  apply State.mem_taken_of_reachable _ h
  apply sys.reachable_of_simulate_eq h₁

theorem dWins_dKingOp {a : AStrat} [ha : a.WF] : state₀.dWins ⟨a, dKingOp⟩ := by
  let f d n := sys.simulate (Strat.f ⟨a, d⟩) state₀ n
  generalize hr : f dKingOp 200 = r
  rcases r with ⟨s₁, n⟩
  by_cases hn : n ≠ 0
  · use 200; simpa [f, hr]
  push_neg at hn; subst hn
  have hs₁ := DState.of_simulate_mul_two_eq_full (n := 100) hr
  have h₁ : ∀ k ≤ 200, (f dKingOp k).1.aPos.dist 0 ≤ k / 2
  · intro k hk
    generalize hr₁ : f dKingOp k = r₁
    have h₁ := DState.aPos_dist_le_div_two_of_simulate (s := state₀) hr₁
    simp at h₁
    exact h₁
  have h₂ : ∀ k ≤ 200, (f dKingOp k).1.aPos ∉ Box.guardTiles
  · intro k hk h₂
    specialize h₁ k hk
    replace h₂ := Box.le_dist_center_of_mem_guardTiles h₂
    omega
  have hf : ∀ {d n k s r₀ r}, f d n = r₀ → r₀.2 = 0 → f d k = (s, r) → k < n →
    r = 0 ∧ ∃ s', f d (k + 1) = (s', 0) ∧ sys.tr s (Strat.f ⟨a, d⟩ s) = some s'
  · intro d n k s r₀ r H₁ H₂ H₃ H₄
    exact sys.exi_simulate_succ_eq_of H₁ H₂ H₃ H₄
  have h₃ : ∀ k ≤ 200, (Box.guardTiles ∩ (f dKingOp k).1.taken).size = (k + 1) / 2
  · intro k hk
    induction k
    · simp [f]
    nm k ih
    specialize ih # by omega
    generalize hr₁ : f dKingOp k = r₁ at ih
    rcases r₁ with ⟨s₂, r₁⟩
    dsimp at ih
    obtain ⟨rfl, s', h₃, h₄⟩ := hf hr rfl hr₁ (by omega)
    simp [h₃]
    induction k using Nat.mod_2_ind <;> nm k
    rotate_left
    · have hs₂ := AState.of_simulate_mul_two_add_one_eq_full hr₁
      simp [add_assoc] at ih
      trans k + 1; rotate_left; omega
      rw [←ih, AState.taken_eq_of_tr h₄]
    have hs₂ := DState.of_simulate_mul_two_eq_full hr₁
    simp [add_assoc] at ih ⊢
    simp [dKingOp] at h₄
    rw [Set'.erase_eq_of_not_mem] at h₄
    rotate_left
    · simp
      rw [Prod.fst_eq_of_eq_mk hr₁]
      apply h₂
      omega
    split at h₄
    · nm x h₅; clear x
      exfalso
      simp at h₅
      rw [Set'.diff_eq_empty_iff_subset] at h₅
      replace h₅ := Set'.size_le_of_subset h₅
      simp at h₅
      have h₆ := State.size_taken_eq_of_simulate_mul_two_eq_full hr₁
      rw [h₆] at h₅
      simp at h₅
      omega
    nm x p h₅; clear x
    rw [DState.taken_eq_of_tr h₄]
    replace h₅ := List.mem_of_head? h₅
    simp at h₅
    rcases h₅ with ⟨h₅, h₆⟩
    rw [Set'.size_inter_insert_right h₅ h₆, ih]
  have h₄ : Box.defense.cnd s₁
  · rw [Box.cnd_defense_iff_guardTiles, State.pw_eq_of_simulate_eq hr]
    simp
    split_ands
    · specialize h₁ _ # by rfl
      simp [hr] at h₁
      exact h₁
    specialize h₃ _ # by rfl
    simp [hr] at h₃
    apply Set'.subset_of_size_inter_eq_size_left
    simpa
  obtain ⟨n, h₅⟩ := dWins_dKingOp_of_cnd (a := a) h₄
  use n + 200
  rw [System.simulate_add']
  dsimp [f] at hr
  simpa [hr]

theorem dHwsPw_one : dHwsPw 1 := by
  intro p
  rw [dHws_initState_iff_dHws_origin]
  change state₀.dHws
  use dKingOp, inferInstance
  intro a ha
  exact dWins_dKingOp