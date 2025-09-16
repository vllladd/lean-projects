import AP.AP.Mimic
import AP.AP.Symmetry

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
  have h₃ := wf_setPw_of_le h₁
  apply aHws_of_rel (r := λ s₁ s₁' => s₁.pw = s.pw ∧ s₁.setPw pw = s₁') h₂ (by simp) (by simp)
  · rintro sa sa' sd p hsa hsa' hsd ⟨h₄, rfl⟩ h₅; use sd.setPw pw
    simp [-AState.tr_eq_some_iff, pw_eq_of_tr h₅, h₄]
    exact tr_setPw_eq_some_of (by rwa [h₄]) h₅
  · rintro sd sd' sa' p hsd hsd' hsa' ⟨h₄, rfl⟩ h₅; use sa'.setPw s.pw
    simp [-DState.tr_eq_some_iff, pw_eq_of_tr h₅] at h₅ ⊢; obtain ⟨sa, h₅, rfl⟩ := h₅
    simp [-DState.tr_eq_some_iff]; convert h₅; simpa [pw_eq_of_tr h₅]

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

theorem aHws_initState_iff_aHws_origin {pw p} :
(initState pw p).aHws ↔ (initState pw 0).aHws := by
  rw [State.aHws_iff_sym (sym := translate (-p))]; simp [translate]

theorem dHws_initState_iff_dHws_origin {pw p} :
(initState pw p).dHws ↔ (initState pw 0).dHws := by
  rw [←not_iff_not]; simp [aHws_initState_iff_aHws_origin]

@[simp]
theorem not_aHwsPw_iff {pw} : ¬aHwsPw pw ↔ dHwsPw pw := by
  simp [aHwsPw, dHwsPw]; symm; constructor; intro h; simp [h]
  rintro ⟨p₀, h⟩ p; rw [dHws_initState_iff_dHws_origin] at h ⊢; exact h

@[simp]
theorem not_dHwsPw_iff {pw} : ¬dHwsPw pw ↔ aHwsPw pw := by
  rw [←not_aHwsPw_iff, not_not]

theorem aHwsPw_of_le {pw pw'} (h₁ : pw ≤ pw') (h₂ : aHwsPw pw) : aHwsPw pw' :=
  λ p => State.aHws_of_setPw_le h₁ # h₂ p

theorem dHwsPw_of_le {pw pw'} (h₁ : pw' ≤ pw) (h₂ : dHwsPw pw) : dHwsPw pw' := by
  contrapose h₂; simp at h₂ ⊢; exact aHwsPw_of_le h₁ h₂