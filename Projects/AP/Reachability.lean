import Projects.AP.WF

namespace AP

def State.diff (s s₁ : State) : ℕ :=
  s₁.hist.length - s.hist.length

def State.diffTrs (s s₁ : State) : List PointZ :=
  s₁.hist.take (s.diff s₁) |>.reverse

def State.isReachable (s₁ s₂ : State) : Bool :=
  sys.trs s₁ (s₁.diffTrs s₂) == (s₂, [])

def State.exiSimulate (f : State → PointZ) (s : State) (s₁ : State) : Bool :=
  sys.simulate f s (s.diff s₁) = (s₁, 0)

-- #check 0 #exit

-----

theorem State.diff_eq_of_simulate' {s f n s₁ r}
(h : sys.simulate f s n = (s₁, r)) : s.diff s₁ + r = n := by
  unfold diff
  rw [length_hist_eq_of_simulate_eq h]
  have h₁ := sys.snd_le_of_simulate_eq h
  omega

theorem State.diff_eq_of_simulate {s f n s₁ r}
(h : sys.simulate f s n = (s₁, r)) : s.diff s₁ = n - r := by
  have := diff_eq_of_simulate' h; omega

theorem State.diff_eq_of_simulate_full {s f n s₁}
(h : sys.simulate f s n = (s₁, 0)) : s.diff s₁ = n :=
  diff_eq_of_simulate h

@[simp]
theorem State.length_diffTrs {s s₁ : State} : (s.diffTrs s₁).length = s.diff s₁ := by
  simp [diffTrs, diff]

@[simp]
theorem State.diff_self {s : State} : s.diff s = 0 := by
  simp [diff]

@[simp]
theorem State.diffTrs_self {s : State} : s.diffTrs s = [] := by
  simp [diffTrs]

theorem State.diff_eq_of_tr {s s₁ s₂ p} (h : sys.tr s₁ p = some s₂)
(h₁ : sys.Reachable s s₁) : s.diff s₂ = s.diff s₁ + 1 := by
  simp [diff, length_hist_eq_of_tr h]; have := length_hist_le_of_reachable h₁; omega

theorem State.diffTrs_eq_of_tr {s s₁ s₂ p} (h : sys.tr s₁ p = some s₂)
(h₁ : sys.Reachable s s₁) : s.diffTrs s₂ = s.diffTrs s₁ ++ [p] := by
  simp [diffTrs, diff_eq_of_tr h h₁, hist_eq_of_tr h]

theorem State.diffTrs_eq_of_trs_full {s ps s₁}
(h : sys.trs s ps = (s₁, [])) : s.diffTrs s₁ = ps := by
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

theorem State.exiSimulate_of_simulate {s s₁ : State} {f n}
(h : sys.simulate f s n = (s₁, 0)) : s.exiSimulate f s₁ := by
  simpa [exiSimulate, diff_eq_of_simulate_full h]

theorem State.exiSimulate_of_exi_simulate {s s₁ : State} {f}
(h : ∃ n, sys.simulate f s n = (s₁, 0)) : s.exiSimulate f s₁ := by
  choose n h using h; exact exiSimulate_of_simulate h

theorem State.exi_simulate_of_exiSimulate {s s₁ : State} {f}
(h : s.exiSimulate f s₁) : ∃ n, sys.simulate f s n = (s₁, 0) := by
  simp [exiSimulate] at h; exact ⟨_, h⟩

theorem State.exi_simulate_iff_exiSimulate {s s₁ : State} {f} :
(∃ n, sys.simulate f s n = (s₁, 0)) ↔ s.exiSimulate f s₁ :=
  ⟨exiSimulate_of_exi_simulate, exi_simulate_of_exiSimulate⟩

instance {s s₁ : State} {f} : Decidable # ∃ n, sys.simulate f s n = (s₁, 0) :=
  decidable_of_iff' _ State.exi_simulate_iff_exiSimulate

@[simp]
theorem State.exiSImulate_eq {s s₁ : State} {f} :
s.exiSimulate f s₁ = decide (∃ n, sys.simulate f s n = (s₁, 0)) := by
  simp [exi_simulate_iff_exiSimulate]

theorem State.diff_eq_of_trs_full {s ps s₁}
(h : sys.trs s ps = (s₁, [])) : s.diff s₁ = ps.length := by
  rw [←length_diffTrs, diffTrs_eq_of_trs_full h]

@[simp]
theorem not_tr_eq_self {s p} : sys.tr s p ≠ some s := by
  intro h; grind [length_hist_eq_of_tr h]

@[simp]
theorem one_le_length_hist {s} [hs : sys.WF s] : 1 ≤ s.hist.length := by
  simp [Nat.one_le_iff_ne_zero]

theorem length_hist_sub_one_add {s n} [hs : sys.WF s] :
s.hist.length - 1 + n = s.hist.length + n - 1 := by
  simp [Nat.sub_add_comm]