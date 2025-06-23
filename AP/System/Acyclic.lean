import AP.System.Basic

namespace System

variable {S T} {sys : System S T}

def trs_nodup_states' (a : S) (ts : List T) : Prop :=
  ∀ (xs ys : List T), xs <+: ts → ys <+: ts →
  (sys.trs a xs).1 = (sys.trs a ys).1 → xs = ys

def trs_nodup_states (a : S) (ts : List T) (b : S) : Prop :=
  sys.trs a ts = (b, []) ∧ sys.trs_nodup_states' a ts

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
  apply @h₁ a b (f a) (reachable_of_simulate ha.symm) h₄
  apply @reachable_of_simulate S T sys f b a m
  rw [h₃, ha]

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

theorem simulate_fn_set_eq_of {f} [hf : sys.SimFn f] {a b t n}
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

theorem acyclic_of_tree {a} [ht : sys.Tree a] : sys.Acyclic a := by
  classical
  rw [tree_iff] at ht
  rw [acyclic_iff]
  intro b c t h₁ h₃ h₂
  obtain ⟨ts₁, h₁⟩ := exi_trs_of_reachable h₁
  obtain ⟨ts₂, h₂⟩ := exi_trs_of_reachable h₂
  nm x y; clear x y
  simp at h₃
  specialize @ht ts₁ (ts₁ ++ t :: ts₂) _
  · rw [trs_append]
    simp [h₁, h₂, h₃]
  simp at ht

instance {a} [ht : sys.Tree a] : sys.Acyclic a := acyclic_of_tree

theorem simulate_eq_of_tr_eq_none {f a n}
(h : sys.tr a (f a) = none) : sys.simulate f a n = (a, n) := by
  cases n; rfl; nm n; simp [h]

theorem exi_trs_of_simulate_eq {f a n r} (h₁ : sys.simulate f a n = r) :
∃ ts, sys.trs a ts = (r.1, []) ∧ n = ts.length + r.2 := by
  induction n generalizing a r
  · use []
    subst h₁
    simp
  nm n ih
  simp at h₁
  split at h₁
  · use []
    simp [←h₁]
  nm x b h₂; clear x
  specialize ih h₁
  obtain ⟨ts, h₃, rfl⟩ := ih
  use f a :: ts
  simp [h₂, h₃, Nat.add_one_add]

theorem simulate_snd_eq_zero_of_tree_and_trs_eq {f a} [ht : sys.Tree a] {ts}
(h : sys.trs a ts = ((sys.simulate f a ts.length).1, [])) :
(sys.simulate f a ts.length).2 = 0 := by
  generalize hr : sys.simulate f a ts.length = r at h ⊢
  obtain ⟨ts₁, h₁, h₂⟩ := exi_trs_of_simulate_eq hr
  obtain ⟨rfl⟩ := @ht.1 ts ts₁ # by rwa [h₁]
  linarith

theorem exi_simulate_of_acyclic_and_trs_eq [ht : Inhabited # S → T]
{a} [ha : sys.Acyclic a] {ts r}
(h₁ : sys.trs a ts = r) : ∃ f, sys.SimFn f ∧
∃ n, sys.simulate f a n = (r.1, 0) ∧ ts.length = n + r.2.length := by
  symm at h₁
  classical
  induction ts generalizing a r
  · use sys.dflt_sim_fn, inferInstance, 0
    simp [h₁]
  nm t ts ih
  simp at h₁
  split at h₁
  · nm x h₂; clear x
    use sys.dflt_sim_fn, inferInstance, 0
    simp [h₁]
  nm x b h₂; clear x
  have hb := acyclic_of_reachable # reachable_of_tr h₂
  specialize ih h₁
  obtain ⟨f, hf, n, h₃, h₄⟩ := ih
  have h₅ := valid_tr_of_eq_some h₂
  use fn_set a t f, sim_fn_fn_set_of h₅, n + 1
  simp [Nat.add_one_add, h₂, h₄]
  rw [←h₃]
  apply simulate_fn_set_eq_of h₅
  clear h₅
  intro k hk h₆
  apply @ha.1 a b t (by rfl) h₂
  exact reachable_of_simulate' h₆.symm

theorem eq_of_tree_and_trs_eq {a} [ht : sys.Tree a] {ts₁ ts₂ b}
(hb : sys.trs a ts₁ = (b, [])) (hc : sys.trs a ts₂ = (b, [])) : ts₁ = ts₂ := by
  apply ht.1; rwa [hc]

theorem exi_simulate_of_reachable {a b}
[ht : Inhabited # S → T] [ha : sys.Acyclic a] (h : sys.Reachable a b) :
∃ (f : S → T), sys.SimFn f ∧ ∃ (n : ℕ), (sys.simulate f a n).1 = b := by
  obtain ⟨t, h₁⟩ := exi_trs_of_reachable h; clear h
  obtain ⟨f, hf, n, h₂, h₃⟩ := exi_simulate_of_acyclic_and_trs_eq h₁
  use f, hf, n
  subst h₃
  simp at h₂
  rw [h₂]

theorem trs_snd_eq_nil_of_prefix_and_eq_nil {a xs ys}
(h₁ : xs <+: ys) (h₂ : (sys.trs a ys).2 = []) : (sys.trs a xs).2 = [] := by
  induction xs generalizing a ys
  · rfl
  nm x xs ih
  cases ys; simp at h₁
  nm y ys
  simp at h₁
  rcases h₁ with ⟨rfl, h₁⟩
  simp at h₂ ⊢
  split at h₂
  · simp at h₂
  nm x c h₃; clear x
  exact ih h₁ h₂

theorem exi_trs_nodup_states_of_trs_eq {a b ts} (h : sys.trs a ts = (b, [])) :
∃ ts', sys.trs_nodup_states a ts' b := by
  classical
  obtain ⟨cnd, h_cnd⟩ := hv # λ a ts =>
    ∀ (xs ys : List T), xs <+: ts → ys <+: ts →
    (sys.trs a xs).1 = (sys.trs a ys).1 → xs = ys
  suffices h₁ : ∃ ts', sys.trs a ts' = (b, []) ∧ cnd a ts'
    by
      rw [h_cnd] at h₁
      exact h₁
  obtain ⟨n, hn⟩ := hv ts.length
  induction n using Nat.strong_induction_on generalizing a b ts
  nm n ih
  by_cases h₁ : cnd a ts
  · use ts
  simp [h_cnd] at h₁
  obtain ⟨xs, hx, ys, hy, h₁, h₂⟩ := h₁
  subst hn
  
  wlog hxy : xs.length < ys.length with ih₁
  · simp at hxy
    apply @ih₁ S T sys cnd h_cnd a b ts h ys hy xs hx
      h₁.symm (by rwa [eq_comm]) ih _
    apply lt_of_le_of_ne hxy
    contrapose! h₂
    symm at h₂
    exact List.eq_of_prefix_and_length_eq hx hy h₂
  have h₄ := Nat.lt_of_lt_of_le hxy hy.length_le
  nm x₁ x₂ x₃; clear! x₁ x₂ x₃
  
  have h₃ := List.prefix_of_prefix_length_le hx hy # le_of_lt hxy
  
  obtain ⟨c, hcx⟩ : ∃ c, sys.trs a xs = (c, []) :=
    by
      use (sys.trs a xs).1
      ext1 <;> try rfl
      dsimp
      apply trs_snd_eq_nil_of_prefix_and_eq_nil hx
      simp [h]
  
  have hcy : sys.trs a ys = (c, []) :=
    by
      ext1
      · rw [←h₁, hcx]
      apply trs_snd_eq_nil_of_prefix_and_eq_nil hy
      rw [h]
  
  have h₅ := List.IsPrefix.length_le hy
  
  have h₆ := @ih (ts.length + xs.length - ys.length)
  apply @h₆ _ a b (xs ++ ts.drop ys.length) _ _
  · omega
  · clear h₆
    simp [trs_append, hcx]
    obtain ⟨zs, rfl⟩ := hy
    simp [trs_append, hcy] at h
    simpa
  · clear h₆
    simp
    omega

theorem exi_trs_nodup_states_of_reachable {a b} (h : sys.Reachable a b) :
∃ (ts : List T), sys.trs_nodup_states a ts b := by
  replace h := exi_trs_of_reachable h
  obtain ⟨ts, h₁⟩ := h
  exact exi_trs_nodup_states_of_trs_eq h₁

theorem trs_nodup_states'_of_cons_and_tr_to {a b t ts}
(h₁ : sys.trs_nodup_states' a (t :: ts)) (h₂ : sys.tr_to a t b) :
sys.trs_nodup_states' b ts := by
  reduce at h₁ h₂
  intro xs ys h₃ h₄ h₅
  specialize h₁ (t :: xs) (t :: ys) (by simpa) (by simpa) (by simpa [h₂])
  simp at h₁
  exact h₁

theorem exi_trs_prefix_of_simulate_le {f a b c n m} (h₁ : n ≤ m)
(h₂ : sys.simulate f a n = (b, 0))
(h₃ : sys.simulate f a m = (c, 0)) :
∃ xs ys, xs <+: ys ∧ xs.length = n ∧ ys.length = m ∧
sys.trs a xs = (b, []) ∧ sys.trs a ys = (c, []) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  obtain ⟨xs, hx, rfl⟩ := exi_trs_of_simulate_eq h₂
  dsimp at *
  simp [simulate_add, h₂] at h₃
  obtain ⟨ys, hy, rfl⟩ := exi_trs_of_simulate_eq h₃
  dsimp at *
  use xs, xs ++ ys, (by simp), (by rfl), (by simp), hx
  simpa [trs_append, hx]

theorem has_tr_of_valid_tr {a t} (h : sys.valid_tr a t) : sys.has_tr a := ⟨t, h⟩

@[simp]
theorem valid_tr_iff_of_sim_fn {f} [h : sys.SimFn f] {a} :
sys.valid_tr a (f a) ↔ sys.has_tr a := ⟨has_tr_of_valid_tr, @h.1 a⟩

theorem snd_le_of_simulate_eq {f a b n m}
(h : sys.simulate f a n = (b, m)) : m ≤ n := by
  contrapose! h
  apply ne_of_congr (·.2)
  simp
  apply ne_of_lt
  have h₁ : (sys.simulate f a n).2 ≤ n := simulate_snd_le
  linarith

theorem simulate_eq_of_simulate_add_eq_add {f a b n m k}
(h : sys.simulate f a (n + k) = (b, m + k)) : sys.simulate f a n = (b, m) := by
  induction k generalizing n m
  · exact h
  nm k ih
  rw [←add_assoc] at h
  specialize @ih (n + 1) (m + 1) _
  · ring_nf at h ⊢
    exact h
  clear h
  induction n generalizing m a
  · simp at ih
    split at ih
    · simp at ih
      simp [ih.1, ih.2]
    simp at ih
  nm n ih₁
  simp
  split
  · nm x h₁
    rw [simulate_eq_of_tr_eq_none h₁] at ih
    simp at ih
    simp [ih]
  nm x c h₁
  unfold simulate at ih
  simp only [h₁] at ih
  exact ih₁ ih

theorem simulate_sub_eq_of {f a b n m}
(h : sys.simulate f a n = (b, m)) : sys.simulate f a (n - m) = (b, 0) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le # snd_le_of_simulate_eq h
  simp
  change _ = (b, m + 0) at h
  rw [add_comm] at h
  nth_rewrite 2 [add_comm] at h
  exact simulate_eq_of_simulate_add_eq_add h

theorem simulate_eq_of_iter {f : S → T} {n k}
(hk : k ≤ n) (g : ℕ → S)
(h₁ : ∀ k < n, sys.valid_tr (g k) (f # g k))
(h₂ : ∀ k < n, sys.tr (g k) (f # g k) = g (k + 1)) :
sys.simulate f (g 0) k = (g k, 0) := by
  sorry

-- #check 0 #exit

theorem exi_simulate_of_trs_nodup_states {a b ts} [ht : Inhabited # S → T]
(h : sys.trs_nodup_states a ts b) :
∃ f, sys.SimFn f ∧ sys.simulate f a ts.length = (b, 0) := by
  obtain ⟨f, hf⟩ := hv # sys.mk_sim_fn # λ s =>
    ts[nat_find # λ n => sys.trs a (ts.take n) = (s, [])]?.getD # sys.dflt_sim_fn s
  use f
  constructor
  · rw [hf]; infer_instance
  generalize hn : ts.length = n
  rcases h with ⟨h₁, h₂⟩
  suffices h : ∀ k ≤ n, sys.simulate f a k = ((sys.trs a # ts.take k).1, 0) by
    specialize h _ (by rfl)
    subst hn
    simp [h₁] at h
    exact h
  intro k hk
  apply simulate_eq_of_iter hk # λ k => (sys.trs a # ts.take k).1
    <;> clear! k <;> intro k hk
  · sorry
  · sorry

#check 0 #exit

  induction n generalizing a ts f
  · subst hf
    simp at hn
    subst hn
    simp at h₁
    simpa [mk_sim_fn]
  nm n ih
  cases ts <;> simp at hn
  nm t ts
  simp at h₁
  split at h₁
  · simp at h₁
  nm x c hc; clear x
  have h₃ : f a = t :=
    by
      clear ih
      subst hf
      dsimp [mk_sim_fn]
      rw [nat_find_eq_of (n := 0)]
      rotate_left
      · rfl
      · simp
      simp
      intro h₃
      contrapose! h₃
      exact valid_tr_of_eq_some hc
  simp [h₃, hc]
  specialize @ih c ts (fn_set a t f) _ hn h₁ _
  · ext x
    sorry
  · exact trs_nodup_states'_of_cons_and_tr_to h₂ hc
  rw [←ih]; clear ih
  symm
  haveI hfi : sys.SimFn f := by rw [hf]; infer_instance
  clear hf
  apply simulate_fn_set_eq_of # valid_tr_of_eq_some hc
  intro k hk h₄
  
  replace h₄ : ∃ m, sys.simulate f c k = (a, m) :=
    by
      use (sys.simulate f c k).2
      ext
      use h₄
      rfl
  obtain ⟨m, h₄⟩ := h₄
  replace h₄ : ∃ k < n, sys.simulate f c k = (a, 0) :=
    by
      use k - m
      exact ⟨by omega, simulate_sub_eq_of h₄⟩
  clear! k
  obtain ⟨k, hk, h₄⟩ := h₄
  replace h₄ : ∃ xs, xs.length < n ∧ xs ≠ [t] ∧
    xs <+: t :: ts ∧ sys.trs a xs = (a, []) :=
    by
      cases k
      · simp at h₄
        subst h₄
        use []
        simpa
      nm k
      replace h₄ : sys.simulate f a (k + 2) = (a, 0) := by simpa [h₃, hc]
      have h₅ : sys.simulate f a 1 = (c, 0) := by simp [h₃, hc]
      replace h₄ := exi_trs_prefix_of_simulate_le (by linarith) h₅ h₄
      obtain ⟨xs, ys, h₄, h₆, h₇, h₈, h₉⟩ := h₄
      use ys
      simp [h₉]
      constructor
      · sorry
      constructor
      · rintro rfl
        simp at h₇

#check 0 #exit

theorem acyclic_iff_sim_full_inj {a} :
sys.Acyclic a ↔ (∀ f [sys.SimFn f] n m,
let (sn, n₁) := sys.simulate f a n
let (sm, m₁) := sys.simulate f a m
n₁ = 0 → m₁ = 0 → sn = sm → n = m) := by
  constructor
  · intro h₁ f hf n m
    exact sim_full_inj_of_acyclic
  intro h
  simp at h
  constructor
  intro b c t h₁ h₂ h₃
  obtain ⟨xs, hx⟩ := exi_trs_nodup_states_of_reachable h₁
  obtain ⟨ys, hy⟩ := exi_trs_nodup_states_of_reachable h₃
  clear h₁ h₃

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

-- |.| theorem tr!_eq_of_valid {sys : System S T} {s t} : sys.valid_tr s t → sys.tr! s t = s' → sys.tr s t = some s'
-- |.| theorem tr!_idempotent {sys : System S T} {s t} : ¬sys.valid_tr s t → sys.tr! s t = s
-- |.| theorem trs_termination {sys : System S T} : ∀ s ts, ∃ s' rem, sys.trs s ts = (s', rem) ∧ rem.length ≤ ts.length
-- |.| theorem trs_reachable {sys : System S T} : ∀ s ts s', sys.trs s ts = (s', []) → sys.Reachable s s'
-- |.| theorem simulate_monotonic {sys f s n} : sys.simulate f s n = (s₁, k) → ∀ m < n, ∃ s₂ l, sys.simulate f s m = (s₂, l)
-- |.| theorem simulate_halts {sys f s} : (∀ s', ¬sys.has_tr s') → ∀ n, ∃ k s', sys.simulate f s n = (s', k) ∧ k > 0
-- |.| theorem reachable_trans {sys : System S T} : ∀ {a b c}, sys.Reachable a b → sys.Reachable b c → sys.Reachable a c
-- |.| theorem reachable_via_simulate {sys f s n} : sys.simulate f s n = (s', 0) → sys.Reachable s s'
-- |.| theorem simFn_exists [DecidableHasTr sys] : ∃ f, sys.SimFn f
-- |.| theorem simulate_deterministic {sys f} [SimFn sys f] : ∀ s n, ∃! s' k, sys.simulate f s n = (s', k)
-- |.| theorem SimInj_acyclic {sys s} [SimInj sys s] {f} [SimFn sys f] : ∀ n m, n < m → sys.simulate f s n = (sn, _) → sys.simulate f s m = (sm, _) → sn ≠ sm
-- |.| theorem SimInj_finite_termination [Finite S] {sys s} [SimInj sys s] {f} [SimFn sys f] : ∃ N, ∀ n ≥ N, ∃ k > 0, sys.simulate f s n = (_, k)
-- |.| theorem trs_append_valid {sys s ts₁ ts₂} : (∀ t ∈ ts₁, sys.valid_tr (current_state) t) → sys.trs s (ts₁ ++ ts₂) = sys.trs (sys.trs s ts₁).fst ts₂
-- |.| theorem simulate_step {sys f s n} : sys.simulate f s (n+1) = match sys.tr s (f s) with | none => (s, n+1) | some s' => sys.simulate f s' n
-- |.| f(0)=0 /\ f(n+1)=f(f(n))
-- |.| (ts.inits.map # λ xs => (sys.trs a xs).1).Nodup