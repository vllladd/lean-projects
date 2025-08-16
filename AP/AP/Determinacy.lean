import AP.AP.Basic

namespace AP

theorem State.not_a_hws_of_d_hws {s : State} (h : s.d_hws) : ¬s.a_hws := by
  obtain ⟨d, hd, h⟩ := h
  simp [a_hws]
  intro a ha
  use d, hd
  exact h a ha

theorem AState.of_simulate_mul_two {sa} [ha : AState sa]
{st : Strat} [hst : st.WF] {n} : AState (sys.simulate st.f sa # n * 2).1 := by
  induction n generalizing sa; exact ha
  nm n ih
  simp [Nat.succ_mul]
  split; exact ha
  nm x sd h₁; clear x
  have hd := DState.of_tr h₁
  split; nm x h₂; simp at h₂
  nm x sa' h₂; clear x
  have ha' := AState.of_tr h₂
  exact ih

instance {sa} [ha : AState sa] {st : Strat} [hst : st.WF] {n} :
AState (sys.simulate st.f sa # n * 2).1 := ha.of_simulate_mul_two

theorem AState.a_wins_of_ind {sa} [ha : AState sa]
{st : Strat} [hst : st.WF] {p : State → Prop}
(h : ∀ {sa} [AState sa], p sa → ∃ sd, sys.tr sa (st.a.f sa) = some sd ∧
∀ sa', sys.tr sd (st.d.f sd) = some sa' → p sa') (hp : p sa) :
sa.a_wins st := by
  rw [sa.a_wins_iff_mul_two]
  intro n
  suffices h₁ : ∃ b, sys.simulate st.f sa (n * 2) = (b, 0) ∧ p b
  · obtain ⟨b, h₁, h₂⟩ := h₁; simp [h₁]
  induction n
  · use sa; simpa
  nm n ih
  clear hp
  rename' sa => sa₀, ha => ha₀
  obtain ⟨sa, ih, hp⟩ := ih
  simp only [Nat.succ_mul, System.simulate_add]
  have ha : AState sa
  · replace ih := congrArg (·.1) ih; subst ih; infer_instance
  simp [ih]
  specialize h hp
  obtain ⟨sd, h₁, h₂⟩ := h
  simp [h₁]
  have hd := DState.of_tr h₁
  obtain ⟨sa', h₃⟩ := hst.wf_d.1 hd.hasTr hd.turn
  simp [h₃]
  exact h₂ _ h₃

def aOptimalCnd (sa : State) (pa : PointZ) : Prop :=
  ∃ sd, sys.tr sa pa = some sd ∧ ∀ pd sa', sys.tr sd pd = some sa' → sa'.a_hws

open Classical in noncomputable
def aOptimal : AStrat :=
  .mk # λ sa => if ∃ pa, aOptimalCnd sa pa
  then Classical.epsilon # aOptimalCnd sa
  else Classical.epsilon # sys.validTr sa

theorem wf_aOptimal : aOptimal.WF := by
  rw [aStrat_wf_iff]
  intro sa hsa h₁
  dsimp [aOptimal]
  generalize hp : Classical.epsilon (aOptimalCnd sa) = pa
  simp
  split_ifs with h₂
  rotate_left
  · have h₃ := Classical.epsilon_spec h₁
    simp at h₃
    exact h₃
  simp at h₁
  have h₃ := Classical.epsilon_spec h₂
  rw [hp] at h₃
  simp [aOptimalCnd] at h₃
  exact h₃.1

instance : aOptimal.WF := wf_aOptimal

-- #check 0 #exit

theorem AState.of_ind {sa sa'} [hs : AState sa] [hs' : AState sa] {p : State → Prop}
(h₁ : p sa) (h₂ : ∀ sa [AState sa] pa sd pd sa',
sys.tr sa pa = some sd → sys.tr sd pd = some sa' → p sa')
(h₃ : sys.Reachable sa sa') : p sa' := by
  sorry

-- #check 0 #exit

theorem AState.a_hws_of_ind {sa : State} [hs : AState sa] {p : State → Prop}
(h₁ : p sa) (h₂ : ∀ sa [AState sa], p sa → ∃ pa sd, sys.tr sa pa = some sd ∧
∀ pd sa', sys.tr sd pd = some sa' → p sa') : sa.a_hws := by
  classical
  use aOptimal, inferInstance
  intro d hd
  intro n
  induction n generalizing sa p; simp
  nm n ih
  have h₄ := ih h₁ h₂
  rw [System.simulate_add]
  simp [h₄]
  generalize h₃ : sys.simulate (Strat.mk aOptimal d).f sa n = r at h₄ ⊢
  rcases r with ⟨sa', r⟩
  dsimp at h₄ ⊢
  subst h₄
  sorry

#check 0 #exit

theorem State.a_hws_of_ind {s : State} [hs : s.WF] {p : State → Prop}
(h₁ : p s)
(h₂ : ∀ s [s.WF], )

#check 0 #exit

theorem State.a_hws_of_not_d_hws {s : State} [hs : s.WF] (h : ¬s.d_hws) : s.a_hws := by
  simp [d_hws] at h
  simp [a_hws]

#check 0 #exit

@[simp]
theorem State.not_a_hws_iff {s : State} [hs : s.WF] : ¬s.a_hws ↔ s.d_hws := by
  refine' ⟨λ h => _, s.not_a_hws_of_d_hws⟩
  contrapose! h; exact s.a_hws_of_not_d_hws h

@[simp]
theorem State.not_d_hws_iff_a_hws {s : State} [hs : s.WF] : ¬s.d_hws ↔ s.a_hws := by
  simp [not_iff_comm']