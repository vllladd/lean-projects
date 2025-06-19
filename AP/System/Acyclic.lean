import AP.System.Basic

namespace System

variable {S T} {sys : System S T}

theorem sim_full_inj_of_acyclic {s} [ha : sys.Acyclic s]
{f} [hf : sys.SimFn f] {n m} :
let (sn, n₁) := sys.simulate f s n
let (sm, m₁) := sys.simulate f s m
n₁ = 0 → m₁ = 0 → sn = sm → n = m := by
  rename' ha => h₁
  rw [acyclic_iff] at h₁
  simp
  intro h₂ h₃ h₄
  replace h₃ : sys.simulate f s m = sys.simulate f s n := by
    ext <;> simp [h₂, h₃, h₄]
  clear h₄
  by_contra h₄
  wlog h₅ : n < m with ih
  · rw [eq_comm] at h₄
    apply @ih S T sys s h₁ f hf m n (by rwa [h₃]) h₃.symm h₄
    simp at h₅
    exact Nat.lt_of_le_of_ne h₅ h₄
  nm x₁ x₂ x₃; clear! x₁ x₂ x₃
  clear h₄
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h₅
  clear h₅
  obtain ⟨a, ha⟩ := hv (sys.simulate f s n).1
  rw [add_assoc] at h₃
  rw [simulate_add] at h₃
  simp [h₂, ←ha] at h₃
  split at h₃
  · simp [←h₃] at h₂
  nm x b h₄
  apply @h₁ a b (f a) (reachable_of_simulate ha) h₄
  apply @reachable_of_simulate S T sys f b a m
  rwa [h₃]

@[simp]
theorem reachable_simulate {f} {s n} : sys.Reachable s (sys.simulate f s n).1 := by
  induction n generalizing s
  · rfl
  nm n ih
  simp
  split
  · rfl
  nm x s₁ h₁; clear x
  trans s₁
  · exact reachable_of_tr h₁
  exact ih

theorem sim_fn_fn_set_of {f} [hf : sys.SimFn f] {s t}
(h : sys.valid_tr s t) : sys.SimFn # fn_set s t f := by
  rw [sim_fn_iff] at hf ⊢
  intro a ha
  unfold fn_set
  split_ifs with h₁
  · rwa [h₁]
  exact hf ha

theorem acyclic_of_reachable {a} [ha : sys.Acyclic a] {b}
(h : sys.Reachable a b) : sys.Acyclic b := by
  rw [acyclic_iff] at ha ⊢
  intro c d t h₁ h₂
  exact @ha c d t (h.trans h₁) h₂

theorem simulate_fn_set_eq_simulate_of {f} [hf : sys.SimFn f] {a b t n}
(h₁ : sys.valid_tr b t) (h₂ : ∀ k < n, (sys.simulate f a k).1 ≠ b) :
sys.simulate (fn_set b t f) a n = sys.simulate f a n := by
  induction n generalizing a
  · rfl
  nm n ih
  simp
  split <;> split; rfl
  · nm x h₃ y c h₄
    exfalso
    rw [fn_set] at h₃
    split_ifs at h₃ with h₅
    · subst h₅
      obtain ⟨d, h₁⟩ := h₁
      simp [h₃] at h₁
    simp [h₃] at h₄
  · nm x c h₃ y h₄
    rw [fn_set] at h₃
    split_ifs at h₃ with h₅
    · subst h₅
      have h₅ := hf.1 # has_tr_of_eq_some h₃
      obtain ⟨d, h₅⟩ := h₅
      simp [h₄] at h₅
    simp [h₃] at h₄
  nm x c h₃ y d h₄; clear x y
  rw [fn_set] at h₃
  split_ifs at h₃ with h₅
  · subst h₅
    specialize h₂ 0 # by linarith
    simp at h₂
  simp [h₃] at h₄
  subst h₄
  apply ih
  intro k hk
  specialize h₂ (k + 1) # by linarith
  simp [h₃] at h₂
  exact h₂

theorem simulate_snd_eq_zero_of_le_of_eq_zero {f a k n}
(h₁ : k ≤ n) (h₂ : (sys.simulate f a n).2 = 0) :
(sys.simulate f a k).2 = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₁
  simp [simulate_add] at h₂
  by_contra h₃
  simp [h₃] at h₂

theorem simulate_snd_eq_zero_of_has_tr {f} [hf : sys.SimFn f] {a n}
(h : sys.has_tr # (sys.simulate f a n).1) : (sys.simulate f a n).2 = 0 := by
  induction n generalizing a; rfl; nm n ih
  simp at h ⊢
  split at h
  · nm x h₁; clear x
    obtain ⟨s, hs⟩ := hf.1 h
    simp [h₁] at hs
  nm x b h₁; clear x
  exact ih h

#check 0 #exit

theorem simulate_snd_eq_zero_of_acyclic_and_trs_eq
{f} [hf : sys.SimFn f] {a} [ha : sys.Acyclic a] {ts}
(h : sys.trs a ts = ((sys.simulate f a ts.length).1, [])) :
(sys.simulate f a ts.length).2 = 0 := by
  induction ts generalizing a
  · rfl
  nm t ts ih
  simp at h ⊢
  split at h <;> split at h <;> try simp at h
  · nm x b h₁ y h₂; clear x y
    exfalso
    obtain ⟨c, hc⟩ := hf.1 # has_tr_of_eq_some h₁
    simp [h₂] at hc
  nm x b h₁ y c h₂; clear x y
  have hb := acyclic_of_reachable # reachable_of_tr h₁
  suffices h₃ : b = c
    by
      subst h₃
      exact ih h
  clear ih

#check 0 #exit

theorem exi_simulate_of_reachable {a b}
[ht : Inhabited T] [ha : sys.Acyclic a] (h : sys.Reachable a b) :
∃ (f : S → T), sys.SimFn f ∧ ∃ (n : ℕ), b = (sys.simulate f a n).1 := by
  classical
  obtain ⟨tr, h⟩ := exi_trs_of_reachable h; nm x; clear x
  
  induction tr generalizing a b
  · use sys.dflt_sim_fn, inferInstance, 0
    simp at h ⊢
    rw [h]
  
  nm t ts ih
  simp at h
  split at h
  · simp at h
  nm x c h₁; clear x
  
  have hc := acyclic_of_reachable # reachable_of_tr h₁
  specialize @ih c b _ h
  obtain ⟨f, h₂, n, rfl⟩ := ih
  use fn_set a t f
  have h₃ := valid_tr_of_eq_some h₁
  use sim_fn_fn_set_of h₃, n + 1
  symm
  congr 1
  simp [h₁]
  have h₄ := reachable_of_tr h₁
  apply simulate_fn_set_eq_simulate_of h₃
  clear h₃
  
  intro k h₆
  have h₅ := @sim_full_inj_of_acyclic (ha := hc)
  specialize @h₅ f _ k n
  simp at h₅
  have hk := h₆
  contrapose! h₆
  apply le_of_eq
  symm
  apply h₅ <;> clear h₅
  · apply simulate_snd_eq_zero_of_has_tr
    rw [h₆]
    exact has_tr_of_eq_some h₁
  · have hn : n = ts.length :=
      by
        sorry
    -- have := @simulate_snd_eq_zero_of_le_of_eq_zero
    --   S T sys f c k n (le_of_lt hk)
    subst hn
    exact simulate_snd_eq_zero_of_acyclic_and_trs_eq h
  
  -- replace ha : ∃ x, sys.Acyclic x ∧ sys.Reachable x a := by use a
  -- obtain ⟨x, hx₁, hx₂⟩ := ha
  -- induction h generalizing x
  -- · clear b
  --   nm b
  --   use sys.dflt_sim_fn, inferInstance, 0
  --   rfl
  -- clear b
  -- nm b c d t h₁ h₂ ih
  -- obtain ⟨f, hf, n, hh⟩ := ih _ _ # reachable_right hx₂ h₁
  -- clear ih h₂
  -- use fn_set b t f
  -- simp at h₁
  -- have h₂ := valid_tr_of_eq_some h₁
  -- use sim_fn_fn_set_of h₂, n + 1
  -- simp [h₁]
  -- symm
  -- congr 1
  -- apply simulate_fn_set_eq_simulate_of h₂
  -- clear h₂
  -- have h₄ := @sim_full_inj_of_acyclic (ha := hx₁)
  -- specialize @h₄ f hf
  -- simp at h₄
  -- intro k hk h₃
  -- specialize @h₄ k n

#check 0 #exit

theorem acyclic_iff_sim_full_inj {s} :
sys.Acyclic s ↔ (∀ f [sys.SimFn f] n m,
let (sn, n₁) := sys.simulate f s n
let (sm, m₁) := sys.simulate f s m
n₁ = 0 → m₁ = 0 → sn = sm → n = m) := by
  constructor
  · intro h₁ f hf n m
    exact sim_full_inj_of_acyclic
  sorry

#check 0 #exit

example {s} :
(∀ f [sys.SimFn f] n m,
  let (sn, n₁) := sys.simulate f s n
  let (sm, m₁) := sys.simulate f s m
  n₁ = 0 → m₁ = 0 → sn = sm → n = m) ↔
(∀ f [sys.SimFn f] n m,
  sys.simulate f s n = sys.simulate f s m → n = m) := by
  symm
  constructor <;> intro h f hf n m <;> specialize h f
  · specialize h n m
    simp
    intro h₁ h₂ h₃
    apply h
    ext1
    · exact h₃
    simp [h₁, h₂]
  intro h₁
  induction n using Nat.strong_induction_on generalizing s m
  nm n ih
  simp [h₁] at h
  have hn : (sys.simulate f s n).2 ≤ n := simulate_snd_le
  have hm : (sys.simulate f s m).2 ≤ m := simulate_snd_le
  obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hm
  specialize @h (sys.simulate f s n).2 (sys.simulate f s m).2
  rw [hx, hy]
  simp [h₁]
  by_cases h₂ : (sys.simulate f s n).2 = 0
  · simp [h₂] at hx
    simp [←h₁, h₂] at hy
    simp [←hx, ←hy]
  specialize ih x _
  · sorry

#check 0 #exit

-- theorem reachable_iff_exi_simulate {s₁ s₂} :
-- sys.Reachable s₁ s₂ ↔ ∃ (f : S → T), sys.SimFn f ∧
-- ∃ n, s₂ = (sys.simulate f s₁ n).1 := by