import AP.System.Acyclic

namespace System

variable {S T} {sys : System S T}

set_option linter.unusedVariables false

theorem aux₁ {s t s'}
(h₁ : sys.valid_tr s t) (h₂ : sys.tr! s t = s') : sys.tr s t = some s' := by
  unfold tr! at h₂
  obtain ⟨a, ha⟩ := h₁
  unfold tr_to at ha
  rw [ha] at h₂ ⊢
  simp at h₂
  rw [h₂]

theorem aux₂ {s t} (h₁ : ¬sys.valid_tr s t) :
sys.tr! s t = s := by
  unfold tr!
  unfold valid_tr tr_to at h₁
  simp at h₁
  rw [←Option.eq_none_iff_forall_ne_some] at h₁
  simp [h₁]

theorem aux₃ {s ts} :
∃ s' rs, sys.trs s ts = (s', rs) ∧ rs.length ≤ ts.length := by
  simp [Prod.ext_iff]

theorem aux₄ {s ts s'}
(h₁ : sys.trs s ts = (s', [])) : sys.Reachable s s' :=
  reachable_of_trs_eq' h₁

theorem aux₅ {f s m} : ∃ s₂ l, sys.simulate f s m = (s₂, l) := by
  simp [Prod.ext_iff]

theorem cntrex₁ : ¬∀ (S T) (sys : System S T) (f s n),
(∀ s', ¬sys.has_tr s') → ∃ k s', sys.simulate f s n = (s', k) ∧ 0 < k := by
  push_neg
  use Unit, Unit, ⟨λ _ _ => none⟩, (λ _ => ()), (), 0
  unfold has_tr
  simp

theorem aux₆ {a b c}
(h₁ : sys.Reachable a b) (h₂ : sys.Reachable b c) : sys.Reachable a c :=
  h₁.trans h₂

theorem aux₇ {f s n s'}
(h₁ : sys.simulate f s n = (s', 0)) : sys.Reachable s s' := by
  exact reachable_of_simulate_full h₁

theorem cntrex₂ : ¬∀ (S T) (sys : System S T),
DecidableHasTr sys → ∃ f, sys.SimFn f := by
  push_neg
  use Unit, Empty, default
  simp
  refine' ⟨⟨_⟩⟩
  intro s
  apply isFalse
  unfold has_tr
  simp

theorem aux₈ {f s n} :
∃! (p : S × ℕ), sys.simulate f s n = (p.1, p.2) := by simp

theorem cntrex₃ : ¬∀ (α β : Type) (P : α → Prop)
(h₁ : ¬∀ x, P x), ¬(∀ x (y : β), P x) := by
  push_neg
  use Unit, Empty, λ _ => False
  simp

theorem cntrex₄ : ¬∀ (S T) (sys : System S T) (s) (h₁ : sys.Acyclic s)
(f) (h₂ : SimFn sys f) (n m sn sm x y) (h₃ : n < m)
(h₄ : sys.simulate f s n = (sn, x))
(h₅ : sys.simulate f s m = (sm, y)),
sn ≠ sm := by
  push_neg
  use Unit, Unit, ⟨λ _ _ => none⟩, ()
  simp [sim_fn_iff, has_tr]
  use default, 0, 1
  simp

theorem aux₉ {s} [h₁ : sys.Acyclic s] {f} [h₂ : SimFn sys f]
{n m sn sm} (h₃ : n < m) : ∃ x y, ∀
(h₄ : sys.simulate f s n = (sn, x))
(h₅ : sys.simulate f s m = (sm, y)),
sn ≠ sm := by
  use 0, 0
  intro h₄ h₅
  rintro rfl
  rw [acyclic_iff_sim_inj] at h₁
  specialize h₁ f n m # by rw [h₄, h₅]
  linarith

theorem aux₁₀ {s} [h₁ : sys.Acyclic s] {f} [h₂ : SimFn sys f]
{n m sn sm} (h₃ : n < m) : ∃ x, ∀
(h₄ : sys.simulate f s n = (sn, x))
(h₅ : sys.simulate f s m = (sm, x)),
sn ≠ sm := by
  use 0
  intro h₄ h₅
  rintro rfl
  rw [acyclic_iff_sim_inj] at h₁
  specialize h₁ f n m # by rw [h₄, h₅]
  linarith

theorem aux₁₁ {s} [h₁ : sys.Acyclic s] {f} [h₂ : SimFn sys f]
{n m sn sm} (h₃ : n < m) {x}
(h₄ : sys.simulate f s n = (sn, x))
(h₅ : sys.simulate f s m = (sm, x)) :
sn ≠ sm := by
  rintro rfl
  rw [acyclic_iff_sim_inj] at h₁
  specialize h₁ f n m # by rw [h₄, h₅]
  linarith

theorem cntrex₅ : ¬∀ (S T) (sys : System S T) [h₁ : Finite S]
{s} [h₂ : Acyclic sys s] {f} [h₃ : SimFn sys f],
∃ N, ∀ n, N ≤ n → ∃ k, 0 < k ∧ ∀ x, sys.simulate f s n = (x, k) := by
  push_neg
  use Bool, Unit, ⟨λ _ _ => none⟩
  use inferInstance, true
  simp
  use (λ _ => ())
  simp [sim_fn_iff, has_tr]
  intro N
  use N + 1
  simp

theorem cntrex₆ : ¬∀ (S T) (sys : System S T) [h₁ : Finite S]
{s} [h₂ : Acyclic sys s] {f} [h₃ : SimFn sys f] {x},
∃ N, ∀ n, N ≤ n → ∃ k, 0 < k ∧ sys.simulate f s n = (x, k) := by
  push_neg
  use Bool, Unit, ⟨λ _ _ => none⟩
  use inferInstance, true
  simp [acyclic_iff]
  use default
  simp [sim_fn_iff, has_tr]
  left
  intro N
  use N, by rfl
  intro k hk
  rw [simulate_eq_of_tr_eq_none] <;> simp

theorem cntrex₇ : ¬∀ (S T) (sys : System S T)
(a ts₁ ts₂ b) (h₁ : ∀ t ∈ ts₁, sys.valid_tr b t),
sys.trs a (ts₁ ++ ts₂) = sys.trs (sys.trs a ts₁).fst ts₂ := by
  push_neg
  use Bool, Unit, ⟨λ b _ => if b then some true else none⟩
  use false, [()], [], true
  simp [valid_tr]

theorem aux₁₄ {a ts₁ ts₂} (h₁ : ∀ a, ∀ t ∈ ts₁, sys.valid_tr a t) :
sys.trs a (ts₁ ++ ts₂) = sys.trs (sys.trs a ts₁).fst ts₂ := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, sys.trs a ts₁ = (b, []) :=
    by
      clear! ts₂
      induction ts₁ generalizing a
      · use a; rfl
      nm t ts ih
      obtain ⟨t₁, h₂⟩ := h₁ a t # by simp
      unfold tr_to at h₂
      simp [h₂]
      apply ih
      intro c t₂ h₃
      exact h₁ c t₂ # by simp [h₃]
  simp [trs_append, hb]

theorem aux₁₅ {f s n} : sys.simulate f s (n + 1) =
match sys.tr s (f s) with
| none => (s, n + 1)
| some s' => sys.simulate f s' n := rfl

theorem aux₁₆ : ∃! (f : ℕ → ℕ), f 0 = 0 ∧ ∀ n, f (n + 1) = f (f n) := by
  use λ _ => 0
  simp
  intro f h₁ h₂
  ext n
  induction n
  · exact h₁
  nm n ih
  simpa [h₂, ih]

set_option linter.unusedVariables true