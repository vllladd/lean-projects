import AP.System.Reachability

namespace System

universe u
variable {S T : Type u} {sys : System S T}

theorem invariant {p : S → Prop} {a b} [ha : sys.WF a]
(h₁ : p a) (h₂ : sys.Reachable a b)
(h₃ : ∀ {x y t} [sys.WF x] [sys.WF y], p x → sys.tr x t = some y → p y) : p b := by
  revert ha; induction h₂; exact h₁
  clear! a b
  nm a b c t h₂ h₄ ih
  intro ha
  have hb := wf_of_tr h₂
  apply ih
  exact h₃ h₁ h₂

theorem invariant_wf {p : S → Prop} {a}
(h₁ : sys.WF a) (h₂ : ∀ {a}, sys.Initial a → p a)
(h₃ : ∀ {x y t} [sys.WF x] [sys.WF y], p x → sys.tr x t = some y → p y) : p a := by
  rw [wf_def] at h₁
  obtain ⟨s₀, h₁, h₄⟩ := h₁
  exact invariant (h₂ h₁) h₄ h₃

theorem invariant_val {α : Type*} {a b} [ha : sys.WF a] {f : S → α} (h₁ : sys.Reachable a b)
(h₂ : ∀ {x y t} [sys.WF x] [sys.WF y], sys.tr x t = some y → f y = f x) : f b = f a := by
  apply invariant (p := (f · = f a)) rfl h₁
  intro x y t ha hb h₃ h₄
  rw [←h₃]
  exact h₂ h₄

theorem simulate_snd_ne_zero_of_tr_eq_none {f s n}
(h₁ : sys.tr s (f s) = none) (h₂ : n ≠ 0) : (sys.simulate f s n).2 ≠ 0 :=
  simulate_snd_ne_zero_of (n := n) (s' := s) (r := n) (by simp [h₁]) h₂ (by rfl)

theorem exi_simulate_succ_eq_of {f s₀ s s' n k r₀ r}
(h₁ : sys.simulate f s₀ n = (s', r₀)) (hr₀ : r₀ = 0)
(h₂ : sys.simulate f s₀ k = (s, r)) (hk : k < n) :
r = 0 ∧ ∃ s', sys.simulate f s₀ (k + 1) = (s', 0) ∧ sys.tr s (f s) = some s' := by
  subst hr₀
  apply and_of
  · rw [Prod.snd_eq_of_eq_mk h₂]
    exact simulate_snd_eq_zero_of_le_and_eq_zero
      (Prod.snd_eq_of_eq_mk h₁ |>.symm) (le_of_lt hk)
  rintro rfl
  generalize hr : sys.simulate f s₀ (k + 1) = r
  rcases r with ⟨s₁, r⟩; simp
  apply and_of
  · rw [Prod.snd_eq_of_eq_mk hr]
    exact simulate_snd_eq_zero_of_le_and_eq_zero
      (Prod.snd_eq_of_eq_mk h₁ |>.symm) hk
  rintro rfl
  rw [simulate_add] at hr
  simp [h₂] at hr
  exact hr

theorem simulate_add' {f s n m} : sys.simulate f s (m + n) =
let ⟨s₁, n'⟩ := sys.simulate f s n
let (s₂, m') := sys.simulate f s₁ m
if n' ≠ 0 then (s₁, n' + m) else (s₂, n' + m') := by
  conv_lhs => rw [add_comm]; exact simulate_add

theorem simulate_snd_eq_zero_of_tr {f} [hf : sys.SimFn f] {a b c t n r} [ha : sys.WF a]
(h₁ : sys.simulate f a n = (b, r)) (h₂ : sys.tr b t = some c) : r = 0 := by
  rw [Prod.fst_eq_of_eq_mk h₁] at h₂; rw [Prod.snd_eq_of_eq_mk h₁]
  exact simulate_snd_eq_zero_of_hasTr # hasTr_of_eq_some h₂

@[simp high]
theorem snd_simulate_add_one_eq_zero_iff {f s n} :
(sys.simulate f s (n + 1)).2 = 0 ↔ ∃ s₁ s₂,
sys.simulate f s n = (s₁, 0) ∧ sys.tr s₁ (f s₁) = some s₂ := by
  generalize hr : sys.simulate f s (n + 1) = r
  rcases r with ⟨s₂, r⟩
  constructor
  · rintro rfl
    simp at hr
    rw [exists_comm]; use s₂
  rintro ⟨s₁, s₂', h₁, h₂⟩
  simp [simulate_add, h₁] at hr
  simp [simulate, h₂] at hr
  simp [hr]