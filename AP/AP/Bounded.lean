import AP.AP.King

namespace AP

theorem State.length_hist_lt_of_tr {s s' p}
(h : sys.tr s p = some s') : s.hist.length < s'.hist.length := by
  simp [hist_eq_of_tr h]

theorem State.forall_d_wins_bounded_of_forall_d_wins {s} [hs : sys.WF s]
{d : DStrat} [Hd : d.WF] (h : ∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩) :
∃ (n : ℕ), ∀ (a : AStrat), a.WF → (sys.simulate (Strat.mk a d).f s n).2 ≠ 0 := by
  contrapose! h
  simp
  apply exi_a_wins_of_ind (p := λ s => ∀ (n : ℕ), ∃ (a : AStrat), a.WF ∧
    (sys.simulate (Strat.mk a d).f s n).2 = 0) h <;> clear! s; rotate_left
  · intro sd hd sa ih h₁ n
    specialize ih (n + 1)
    obtain ⟨a, Ha, ih⟩ := ih
    simp [h₁] at ih
    use a
  intro sa ha ih
  have ht : sys.hasTr sa
  · specialize ih 1
    obtain ⟨a, h₁, h₂⟩ := ih
    simp at h₂; split at h₂; simp at h₂; nm x sd h₃; clear x
    exact ⟨_, _, h₃⟩
  rw [skolemize'] at ih
  obtain ⟨f, hf⟩ := ih
  obtain ⟨g, hg⟩ : ∃ (g : ℕ → {pa : PointZ // pa.dist sa.aPos ≤ sa.pw}),
    ∀ n, n ≠ 0 → (g n).1 = (f n).f sa
  · refine' ⟨_, _⟩
    · intro n
      use if n = 0 then sa.aPos else (f n).f sa
      specialize hf n
      rcases hf with ⟨h₁, h₂⟩
      cases n <;> simp; nm n
      simp at h₂; split at h₂; simp at h₂; nm x sd h₃; clear x
      simp at h₃
      exact h₃.1.2.2
    intro n hn
    simp [hn]
  have h₂ := @Point.finite_setOf_dist_le sa.aPos sa.pw
  obtain ⟨⟨pa, h₃⟩, h₄⟩ := Set.exists_infinite_preimage_of (f := g) (hb := h₂)
  simp at h₃
  suffices h₅ : ∀ n, n ≠ 0 → ∃ (a : AStrat), a.WF ∧ a.f sa = pa ∧
    (sys.simulate (Strat.mk a d).f sa n).2 = 0
  · obtain ⟨a, h₆, h₇, h₈⟩ := h₅ 1 (by simp)
    clear h₈
    obtain ⟨sd, h₈⟩ := a.validTr ht
    rw [h₇] at h₈; clear h₇
    use pa, sd, h₈
    clear! a
    intro n
    specialize h₅ (n + 1) (by simp)
    obtain ⟨a, Ha, h₅, h₆⟩ := h₅
    simp [h₅, h₈] at h₆
    use a
  suffices h₅ : ∀ (k : ℕ), ∃ (n : ℕ), k ≤ n ∧ g n = ⟨pa, h₃⟩
  · intro k hk
    specialize h₅ k
    obtain ⟨n, hn, h₅⟩ := h₅
    specialize hg n _
    · rintro rfl; simp [hk] at hn
    rw [Subtype.ext_iff, hg] at h₅
    specialize hf n
    rcases hf with ⟨hf, h₆⟩
    use f n, hf, h₅
    exact System.simulate_snd_eq_zero_of_le_and_eq_zero h₆ hn
  contrapose! h₄
  simp [Set.preimage]
  obtain ⟨k, hk⟩ := h₄
  apply Set.finite_of_subset_finset # Finset.Ico 0 k
  simp
  intro n h₄
  specialize hk n
  simp [h₄] at hk
  exact hk

theorem State.forall_d_wins_iff_forall_d_wins_bounded {s} [hs : sys.WF s]
{d : DStrat} [Hd : d.WF] : (∀ (a : AStrat), a.WF → s.d_wins ⟨a, d⟩) ↔
∃ (n : ℕ), ∀ (a : AStrat), a.WF → (sys.simulate (Strat.mk a d).f s n).2 ≠ 0 := by
  use forall_d_wins_bounded_of_forall_d_wins
  rintro ⟨n, h₁⟩
  intro a Ha
  specialize h₁ a Ha
  use n

theorem State.d_hws_iff_d_hws_bounded {s} [hs : sys.WF s]
(h : s.d_hws) : ∃ (n : ℕ) (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF →
(sys.simulate (Strat.mk a d).f s n).2 ≠ 0 := by
  obtain ⟨d, Hd, h⟩ := h
  rw [forall_d_wins_iff_forall_d_wins_bounded] at h
  obtain ⟨n, h₁⟩ := h
  use n, d

def State.getATrap (s : State) : Set PointZ :=
  {p | ∃ s', sys.Reachable s s' ∧ s'.aPos = p}

def State.aTrapped (s : State) : Prop :=
  s.getATrap.Finite

theorem State.a_wins_iff_add {s st} (k : ℕ) :
s.a_wins st ↔ ∀ n, (sys.simulate st.f s # k + n).2 = 0 := by
  constructor <;> intro h₁ n
  · exact h₁ # k + n
  · apply System.simulate_snd_eq_zero_of_le_and_eq_zero # h₁ n
    linarith

theorem State.d_wins_iff_add {s st} (k : ℕ) :
s.d_wins st ↔ ∃ n, (sys.simulate st.f s # k + n).2 ≠ 0 := by
  constructor <;> rintro ⟨n, h₁⟩
  · use n
    contrapose! h₁
    apply System.simulate_snd_eq_zero_of_le_and_eq_zero h₁
    linarith
  · use k + n

#check 0 #exit

not_reachable_of_acyclic_and_simulate_and_lt

theorem State.d_hws_of_exi_aTrapped {s} [hs : sys.WF s]
(h : ∃ (d : DStrat), d.WF ∧ ∀ (a : AStrat), a.WF → ∃ n,
(sys.simulate (Strat.mk a d).f s n).1.aTrapped) : s.d_hws := by
  classical
  obtain ⟨d, Hd, h₁⟩ := h
  rw [←not_a_hws_iff, a_hws]
  push_neg; simp
  intro a Ha
  specialize h₁ a Ha
  obtain ⟨n, h₁⟩ := h₁
  generalize hr : sys.simulate (Strat.mk a d).f s n = r
  rcases r with ⟨s₁, r⟩
  simp [hr] at h₁
  generalize hd₁ : DStrat.mk' (λ s => if sys.Reachable s₁ s then
    choose? (· ∈ s.getATrap) else d.f s) = d₁
  have Hd₁ : d₁.WF; subst hd₁; infer_instance
  
  by_cases hr' : r = 0; rotate_left
  · use d, Hd, n; simpa [hr]
  subst hr'
  
  use d₁, Hd₁
  use n + s₁.getATrap.ncard
  have h₂ : sys.simulate (Strat.mk a d₁).f s n = ⟨s₁, 0⟩
  · rw [←hr]
    apply simulate_congr # by simp
    rintro k hk sd hd h₂ h₃ ⟨pd, sa, h₄⟩
    dsimp
    suffices h₅ : ¬sys.Reachable s₁ sd
    · simp [←hd₁, mk_strat_fn, h₅]
    have h₅ := System.reachable_of_simulate_full h₂
    have h₆ : sys.Reachable sa s₁
    · 
  simp [System.simulate_add, h₂]
  sorry