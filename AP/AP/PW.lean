import AP.AP.Mimic

namespace AP

@[simp]
theorem DStrat.tr_ne_none {s} {d : DStrat} [hs : DState s] [hd : d.WF] :
sys.tr s (d.f s) ≠ none := by
  obtain ⟨s', h₁⟩ := hd.validTr s; simp [h₁]

@[simp]
theorem State.chooseDMove_tr_ne_none {s} [hs : DState s] :
sys.tr s s.chooseDMove ≠ none := by
  obtain ⟨s', h₁⟩ := hs.validTr_chooseDMove; simp [h₁]

@[simp]
theorem State.dHws_of_pw_0 {s} [hs : sys.WF s] (h : s.pw = 0) : s.dHws := by
  use default, inferInstance
  intro a Ha
  replace hs := s.aState_or_dState; rcases hs with hs | hs
  · use 1
    simp
    split; simp
    nm x s' h₁; clear x
    simp [h] at h₁
    rcases h₁ with ⟨⟨h₁, h₂, h₃⟩, h₄⟩
    simp [h₃] at h₁
  · use 2
    simp
    split
    · nm x h₁; simp at h₁
    nm x s₁ h₁; clear x
    split; simp; nm x s₂ h₂; clear x
    have hs₁ := AState.of_tr h₁
    simp [pw_eq_of_tr h₁, h] at h₂
    rcases h₂ with ⟨⟨h₂, h₃, h₄⟩, h₅⟩
    simp [h₄] at h₂

@[simp]
theorem dHwsPw_0 : dHwsPw 0 :=
  λ _ => State.dHws_of_pw_0 rfl

@[simp]
theorem DState.tr_setPw {s p pw} [hs : DState s] :
sys.tr (s.setPw pw) p = (sys.tr s p).map (·.setPw pw) := by
  ext s'; simp [sys, State.move, State.dMove]; intros; rfl

@[simp]
theorem DState.validTr_setPw {s p pw} [hs : DState s] :
sys.validTr (s.setPw pw) p = sys.validTr s p := by
  simp [System.validTr]

theorem State.aHws_setPw_of_le {s pw} [hs : sys.WF s]
(h₁ : s.pw ≤ pw) (h₂ : s.aHws) : (s.setPw pw).aHws := by
  have hs' := wf_setPw_of_le h₁
  obtain ⟨a, Ha, h₂⟩ := h₂
  use .mk (a.f # ·.setPw s.pw), inferInstance
  intro d Hd n
  specialize h₂ (.mk (d.f # ·.setPw pw)) inferInstance n
  apply simulate_congr_rel_full (r := λ s₁ s₂ => s₁.pw = s.pw ∧ s₁.setPw pw = s₂)
    h₂ (by simp) (by simp)
  · rintro sa sa' sd hsa hsa' hsd h₃ ⟨h₀, h₄⟩
    use sd.setPw pw
    simp [-AState.tr_eq_some_iff] at h₃
    have h₄' : sa'.setPw s.pw = sa; simpa [←h₄]
    have h₅ : sys.tr sa' (a.f sa) = sd.setPw pw
    · simp [-AState.tr_eq_some_iff, ←h₄]
      rw [tr_setPw_eq_some_of (by linarith) h₃]
    have h₆ : sys.validTr sa' (a.f sa) := ⟨_, h₅⟩
    simp [-AState.tr_eq_some_iff, h₄', h₆]
    use h₅; rwa [pw_eq_of_tr h₃]
  · rintro sd sd' sa hsd hsd' hsa h₃ ⟨h₀, h₄⟩
    have h₄' : sd'.setPw s.pw = sd; simpa [←h₄]
    have h₅ : sd'.setPw pw = sd'; simp [←h₄]
    simp [-DState.tr_eq_some_iff, ←h₄', h₅] at h₃
    obtain ⟨sa', h₃, rfl⟩ := h₃
    simp [-DState.tr_eq_some_iff]
    rwa [setPw_eq_self_of]
    simp [pw_eq_of_tr h₃, ←h₄]

theorem State.dHws_of_setPw_le {s : State} {pw} [hs : sys.WF s]
(h₁ : s.pw ≤ pw) (h₂ : (s.setPw pw).dHws) : s.dHws := by
  have hs' := wf_setPw_of_le h₁
  contrapose h₂; simp at h₂ ⊢
  exact aHws_setPw_of_le h₁ h₂

theorem State.dHws_setPw_of_le {s : State} {pw} [hs : sys.WF # s.setPw pw]
(h₁ : pw ≤ s.pw) (h₂ : s.dHws) : (s.setPw pw).dHws := by
  generalize h₃ : s.setPw pw = s' at hs
  have h₄ : s'.pw = pw; simp [←h₃]; subst h₄
  rw [setPw_eq_comm] at h₃
  have h₄ : sys.WF s; rw [←h₃]; exact wf_setPw_of_le h₁
  rw [←h₃] at h₂; exact dHws_of_setPw_le h₁ h₂

theorem State.aHws_of_setPw_le {s : State} {pw} [hs : sys.WF # s.setPw pw]
(h₁ : pw ≤ s.pw) (h₂ : (s.setPw pw).aHws) : s.aHws := by
  generalize h₃ : s.setPw pw = s' at hs
  have h₄ : s'.pw = pw; simp [←h₃]; subst h₄
  rw [setPw_eq_comm] at h₃
  have h₄ : sys.WF s; rw [←h₃]; exact wf_setPw_of_le h₁
  rw [←h₃] at h₂; contrapose h₂; simp at h₂ ⊢
  apply dHws_of_setPw_le h₁; simpa [h₃]

theorem aHwsPw_of_le {pw pw'} (h₁ : pw ≤ pw') (h₂ : aHwsPw pw) : aHwsPw pw' := by
  intro p
  sorry -- Translational symmetry

theorem dHwsPw_of_le {pw pw'} (h₁ : pw' ≤ pw) (h₂ : dHwsPw pw) : dHwsPw pw' := by
  contrapose h₂; simp at h₂ ⊢; exact aHwsPw_of_le h₁ h₂