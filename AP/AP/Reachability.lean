import AP.AP.WF

namespace AP

def State.diff (s₁ s : State) : ℕ :=
  s₁.hist.length - s.hist.length

def State.diffTrs (s₁ s : State) : List PointZ :=
  s₁.hist.take (s₁.diff s) |>.reverse

def State.isReachable (s₁ s₂ : State) : Bool :=
  sys.trs s₁ (s₂.diffTrs s₁) == (s₂, [])

-----

theorem State.diff_eq_of_simulate' {s f n s₁ r}
(h : sys.simulate f s n = (s₁, r)) : s₁.diff s + r = n := by
  unfold diff
  rw [length_hist_eq_of_simulate_eq h]
  have h₁ := sys.snd_le_of_simulate_eq h
  omega

theorem State.diff_eq_of_simulate {s f n s₁ r}
(h : sys.simulate f s n = (s₁, r)) : s₁.diff s = n - r := by
  have := diff_eq_of_simulate' h; omega

theorem State.diff_eq_of_simulate_full {s f n s₁}
(h : sys.simulate f s n = (s₁, 0)) : s₁.diff s = n :=
  diff_eq_of_simulate h

@[simp]
theorem State.length_diffTrs {s s₁ : State} : (s₁.diffTrs s).length = s₁.diff s := by
  simp [diffTrs, diff]

@[simp]
theorem State.diff_self {s : State} : s.diff s = 0 := by
  simp [diff]

@[simp]
theorem State.diffTrs_self {s : State} : s.diffTrs s = [] := by
  simp [diffTrs]

theorem State.diff_eq_of_tr {s s₁ s₂ p} (h : sys.tr s₁ p = some s₂)
(h₁ : sys.Reachable s s₁) : s₂.diff s = s₁.diff s + 1 := by
  simp [diff, length_hist_eq_of_tr h]; have := length_hist_le_of_reachable h₁; omega

theorem State.diffTrs_eq_of_tr {s s₁ s₂ p} (h : sys.tr s₁ p = some s₂)
(h₁ : sys.Reachable s s₁) : s₂.diffTrs s = s₁.diffTrs s ++ [p] := by
  simp [diffTrs, diff_eq_of_tr h h₁, hist_eq_of_tr h]

theorem State.diffTrs_eq_of_trs_full {s ps s₁}
(h : sys.trs s ps = (s₁, [])) : s₁.diffTrs s = ps := by
  induction ps using List.reverseRecOn generalizing s₁
  · simp at h; simp [h]
  nm ps p ih
  simp at h
  choose s' h₁ h₂ using h
  specialize ih h₁
  simpa [diffTrs_eq_of_tr h₂ # sys.reachable_of_trs h₁]

theorem State.isReachable_of_reachable {s₁ s₂ : State}
(h : sys.Reachable s₁ s₂) : s₁.isReachable s₂ := by
  rw [sys.reachable_iff_exi_trs] at h; choose ps h using h
  simp [isReachable, diffTrs_eq_of_trs_full h, h]

theorem State.reachable_of_isReachable {s₁ s₂ : State}
(h : s₁.isReachable s₂) : sys.Reachable s₁ s₂ := by
  simp [isReachable] at h; rw [sys.reachable_iff_exi_trs]; exact ⟨_, h⟩

theorem State.reachable_iff_isReachable {s₁ s₂ : State} :
sys.Reachable s₁ s₂ ↔ s₁.isReachable s₂ :=
  ⟨isReachable_of_reachable, reachable_of_isReachable⟩

instance {s₁ s₂} : Decidable # sys.Reachable s₁ s₂ :=
  decidable_of_iff' _ State.reachable_iff_isReachable

@[simp]
theorem State.isReachable_eq {s₁ s₂ : State} :
s₁.isReachable s₂ = decide (sys.Reachable s₁ s₂) := by
  simp [reachable_iff_isReachable]