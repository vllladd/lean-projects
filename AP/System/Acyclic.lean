import AP.System.Basic

namespace System

variable {S T} {sys : System S T}

theorem sim_full_inj_of_acyclic {s} [ha : sys.Acyclic s]
{f} [hf : sys.SimFn f] {n m} :
(sys.simulate f s n).2 = 0 → (sys.simulate f s m).2 = 0 →
(sys.simulate f s n).1 = (sys.simulate f s m).1 → n = m := by
  rename' ha => h₁
  rw [acyclic_iff] at h₁
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

theorem sim_fn_fn_set_of [DecidableEq S] {f} [hf : sys.SimFn f] {s t}
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

theorem simulate_fn_set_eq_of [DecidableEq S] {f} [hf : sys.SimFn f] {a b t n}
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

theorem simulate_snd_eq_zero_of_le_and_eq_zero {f a k n}
(h₁ : (sys.simulate f a n).2 = 0) (h₂ : k ≤ n) :
(sys.simulate f a k).2 = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₂
  simp [simulate_add] at h₁
  by_contra h₃
  simp [h₃] at h₁

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

theorem eq_of_tree_and_trs_eq {a} [ht : sys.Tree a] {ts₁ ts₂ b}
(hb : sys.trs a ts₁ = (b, [])) (hc : sys.trs a ts₂ = (b, [])) : ts₁ = ts₂ := by
  apply ht.1; rwa [hc]

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

theorem exi_simp_path_of_trs_full_eq {a b ts} (h : sys.trs a ts = (b, [])) :
∃ ts', sys.simp_path a ts' b := by
  classical
  obtain ⟨cnd, h_cnd⟩ := hv # λ a ts =>
    ∀ (xs ys : List T), xs <+: ts → ys <+: ts →
    (sys.trs a xs).1 = (sys.trs a ys).1 → xs = ys
  suffices h₁ : ∃ ts', cnd a ts' ∧ sys.trs a ts' = (b, [])
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

theorem exi_simp_path_of_reachable {a b} (h : sys.Reachable a b) :
∃ (ts : List T), sys.simp_path a ts b := by
  replace h := exi_trs_of_reachable h
  obtain ⟨ts, h₁⟩ := h
  exact exi_simp_path_of_trs_full_eq h₁

theorem simp_path'_of_cons_and_tr_to {a b t ts}
(h₁ : sys.simp_path' a (t :: ts)) (h₂ : sys.tr_to a t b) :
sys.simp_path' b ts := by
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

theorem simulate_eq_of_iter_le {f : S → T} {n k}
(hk : k ≤ n) (g : ℕ → S)
(h₁ : ∀ k < n, sys.valid_tr (g k) (f # g k))
(h₂ : ∀ k < n, sys.tr (g k) (f # g k) = g (k + 1)) :
sys.simulate f (g 0) k = (g k, 0) := by
  induction k
  · rfl
  nm k ih
  specialize ih # by linarith
  cases n <;> simp at hk
  nm n
  specialize h₂ k # by linarith
  rw [simulate_add]
  simp [ih, h₂]

theorem simulate_eq_of_iter {f : S → T} {n} (g : ℕ → S)
(h₁ : ∀ k < n, sys.valid_tr (g k) (f # g k))
(h₂ : ∀ k < n, sys.tr (g k) (f # g k) = g (k + 1)) :
sys.simulate f (g 0) n = (g n, 0) := by
  apply simulate_eq_of_iter_le # by rfl
  all_goals assumption

theorem has_tr_trs_of_prefix {a b xs ys}
(h₁ : sys.trs a ys = (b, [])) (h₂ : xs <+: ys) (h₃ : xs ≠ ys) :
sys.has_tr (sys.trs a xs).1 := by
  classical
  obtain ⟨ys, rfl⟩ := h₂
  cases ys
  · simp at h₃
  nm y ys
  clear h₃
  simp [trs_append] at h₁
  split_ifs at h₁ with h₂
  · split at h₁ <;> simp at h₁
    nm x c h₃; clear x
    exact has_tr_of_eq_some h₃
  simp at h₁

@[simp]
theorem not_valid_tr_iff {a t} : ¬sys.valid_tr a t ↔ sys.tr a t = none := by
  simp [valid_tr, Option.eq_none_iff_forall_ne_some]

theorem tr_trs_list_take_eq_some_of {ts : List T} {a n}
(h₁ : n < ts.length) (h₂ : (sys.trs a ts).2 = []) :
sys.tr (sys.trs a # ts.take n).1 ts[n] = some (sys.trs a # ts.take # n + 1).1 := by
  classical
  induction n generalizing a ts
  · simp
    cases ts
    · simp at h₁
    nm t ts
    simp at h₂
    split at h₂; simp at h₂
    nm x b h₃; clear x
    simp [h₃]
  nm n ih
  cases ts
  · simp at h₁
  nm t ts
  simp at h₂
  split at h₂; simp at h₂
  nm x b h₃; clear x
  simp [h₃]
  exact @ih ts b (by rwa [←Nat.succ_lt_succ_iff]) h₂

theorem valid_tr_trs_list_take_of {ts : List T} {a n}
(h₁ : n < ts.length) (h₂ : (sys.trs a ts).2 = []) :
sys.valid_tr (sys.trs a # ts.take n).1 ts[n] :=
  ⟨_, tr_trs_list_take_eq_some_of h₁ h₂⟩

theorem exi_simulate_of_simp_path {a b ts} [ht : Inhabited # S → T]
(h : sys.simp_path a ts b) : ∃ f, sys.SimFn f ∧ ∀ k ≤ ts.length,
sys.simulate f a k = ((sys.trs a # ts.take k).1, 0) := by
  classical
  obtain ⟨f, hf⟩ := hv # sys.mk_sim_fn # λ s =>
    ts[nat_find # λ n => sys.trs a (ts.take n) = (s, [])]?.getD # sys.dflt_sim_fn s
  use f
  constructor
  · rw [hf]; infer_instance
  generalize hn : ts.length = n
  rcases h with ⟨h₂, h₁⟩
  intro k hk
  apply simulate_eq_of_iter_le hk # λ k => (sys.trs a # ts.take k).1
    <;> clear! k <;> intro k hk
  · rw [hf]
    apply valid_tr_of_sim_fn_and_has_tr
    apply has_tr_trs_of_prefix h₁ # by simp
    apply ne_of_congr (·.length)
    simpa [hn]
  subst hf
  unfold mk_sim_fn
  dsimp
  rw [nat_find_eq_of (n := k)]
  rotate_left
  · ext1
    rfl
    dsimp
    apply trs_snd_eq_nil_of_prefix_and_eq_nil (ys := ts) # by simp
    rw [h₁]
  · intro r hr
    apply ne_of_congr (·.1)
    dsimp
    intro h₃
    specialize h₂ (ts.take r) (ts.take k) (by simp) (by simp) h₃
    simp [hn] at h₂
    omega
  rw [List.getElem?_eq_getElem # by linarith]
  simp
  rw [List.take_succ, List.getElem?_eq_getElem # by linarith, Option.toList_some,
    trs_append]
  simp
  rw [trs_snd_eq_nil_of_prefix_and_eq_nil (ys := ts) (by simp) (by rw [h₁])]
  simp
  split_ifs with h₃
  · obtain ⟨c, h₃⟩ := h₃
    rw [h₃]
  exfalso
  apply h₃; clear h₃
  apply valid_tr_trs_list_take_of
  rw [h₁]

@[simp]
theorem simp_path_self_iff {a xs} : sys.simp_path a xs a ↔ xs = [] := by
  unfold simp_path simp_path'
  cases xs <;> simp
  nm x xs
  intro h₁
  split; simp
  nm x b h₂; clear x
  specialize h₁ [] (x :: xs)
  simp [h₂] at h₁
  contrapose! h₁
  rw [h₁]

@[simp]
theorem simp_path_nil_iff {a b} : sys.simp_path a [] b ↔ a = b := by
  simp [simp_path, simp_path']

@[simp]
theorem simp_path_singleton_iff {a b t} :
sys.simp_path a [t] b ↔ a ≠ b ∧ sys.tr_to a t b := by
  simp [simp_path, simp_path']
  split
  · nm x h₁; clear x
    simp [h₁]
  nm x c h₁; clear x
  simp [h₁]
  rintro rfl
  constructor
  · rintro h₂ rfl
    specialize h₂ [] [t]
    simp [h₁] at h₂
  intro h₂ xs ys hx hy h₃
  cases xs
  · simp at h₃
    cases ys
    · rfl
    nm y ys
    simp at hy
    rcases hy with ⟨rfl, rfl⟩
    simp [h₁, h₂] at h₃
  nm x xs
  simp at hx
  rcases hx with ⟨rfl, rfl⟩
  simp [h₁, h₂] at h₃
  cases ys
  · simp [h₃] at h₂
  nm y ys
  simp at hy
  simp [hy]

theorem simp_path'_snoc_of (b c : S) {a ts t}
(h₁ : sys.simp_path a ts b) (h₂ : sys.tr_to b t c)
(h₃ : ∀ xs, xs <+: ts → (sys.trs a xs).1 ≠ c) :
sys.simp_path' a (ts ++ [t]) := by
  classical
  unfold tr_to at h₂
  rcases h₁ with ⟨ha₁, ha₂⟩
  intro xs ys hx hy h₄
  by_cases h₅ : xs = ts ++ [t]
  · subst h₅; clear hx
    simp [trs_append, ha₂, h₂] at h₄
    symm
    by_contra h₆
    apply h₃ ys (List.prefix_of_prefix_snoc_and_ne hy h₆) h₄.symm
  replace hx := List.prefix_of_prefix_snoc_and_ne hx h₅
  clear h₅
  by_cases h₅ : ys = ts ++ [t]
  · subst h₅; clear hy
    simp [trs_append, ha₂, h₂] at h₄
    by_contra h₆
    exact h₃ xs hx h₄
  replace hy := List.prefix_of_prefix_snoc_and_ne hy h₅
  clear h₅
  exact ha₁ xs ys hx hy h₄

theorem simp_path_snoc_of {a b c ts t}
(h₁ : sys.simp_path a ts b) (h₂ : sys.tr_to b t c)
(h₃ : ∀ xs, xs <+: ts → (sys.trs a xs).1 ≠ c) :
sys.simp_path a (ts ++ [t]) c := by
  classical
  unfold tr_to at h₂
  rcases h₁ with ⟨ha₁, ha₂⟩
  use simp_path'_snoc_of b c (by use ha₁) h₂ h₃
  simp [trs_append, ha₂, h₂]

@[simp]
theorem trs_snd_suffix {a xs} : (sys.trs a xs).2 <:+ xs := by
  induction xs generalizing a
  · rfl
  nm x xs ih
  simp
  split
  · rfl
  apply ih.trans
  simp

theorem trs_snd_suffix_of_eq {a xs r}
(h : sys.trs a xs = r) : r.2 <:+ xs := by simp [←h]

@[simp]
theorem trs_snd_length_le {a xs} : (sys.trs a xs).2.length ≤ xs.length := by
  apply List.IsSuffix.length_le; simp

theorem trs_snd_length_le_of_eq {a xs r}
(h : sys.trs a xs = r) : r.2.length ≤ xs.length := by simp [←h]

theorem exi_trs_nil_of_trs_eq {a ts r} (hr : sys.trs a ts = r) :
∃ xs, xs <+: ts ∧ ∃ b, sys.trs a xs = (b, []) := by
  rcases r with ⟨b, rs⟩
  use ts.take (ts.length - rs.length)
  simp
  use b
  induction ts generalizing a b rs
  · simp at hr; simp [hr.1]
  nm t ts ih
  simp at hr
  split at hr
  · nm x h₁; clear x
    simp at hr
    simp [hr]
  nm x c h₁; clear x
  simp
  rw [Nat.add_one_sub # trs_snd_length_le_of_eq hr]
  simp [h₁]
  apply ih
  exact hr

theorem simp_path'_of_prefix_simp_path' {a ts xs}
(h₁ : sys.simp_path' a ts) (h₂ : xs <+: ts) : sys.simp_path' a xs := by
  intro ys₁ ys₂ h₃ h₄ h₅
  exact h₁ ys₁ ys₂ (h₃.trans h₂) (h₄.trans h₂) h₅

theorem exi_simp_path_of_simp_path' {a ts}
(h : sys.simp_path' a ts) : ∃ xs, xs <+: ts ∧
∃ b, sys.simp_path a xs b ∧ b = (sys.trs a xs).1 := by
  obtain ⟨xs, hx, b, h₁⟩ := exi_trs_nil_of_trs_eq (rfl : sys.trs a ts = _)
  use xs, hx, b
  refine' ⟨_, by rw [h₁]⟩
  use simp_path'_of_prefix_simp_path' h hx

@[simp]
theorem simp_path'_nil {a} : sys.simp_path' a [] := by simp [simp_path']

theorem exi_simp_path_prefix_of_not_simp_path' {a ts}
(h₁ : ¬sys.simp_path' a ts) : ∃ xs t, xs ++ [t] <+: ts ∧
sys.simp_path' a xs ∧ ¬sys.simp_path' a (xs ++ [t]) := by
  induction ts using List.right_induction
  · simp at h₁
  nm ts t ih
  rw [←or_iff_not_imp_left] at ih
  rcases ih with ih | ih
  · use ts, t
  obtain ⟨xs, x, h₂, h₃, h₄⟩ := ih
  use xs, x
  exact ⟨h₂.trans # by simp, h₃, h₄⟩

theorem exi_trs_full_of_simp_path' {a ts}
(h : sys.simp_path' a ts) : ∃ b, sys.trs a ts = (b, []) := by
  classical
  induction ts using List.right_induction
  · use a; rfl
  nm ts t ih
  clear ih
  specialize h ts (ts ++ [t])
  simp at h
  generalize hr : sys.trs a (ts ++ [t]) = r at h ⊢
  rcases r with ⟨b, rs⟩
  dsimp at h
  use b
  simp
  simp [trs_append] at hr
  split_ifs at hr with h₁
  · simp [h₁] at hr
    split at hr <;> simp at hr <;> tauto
  simp at hr
  tauto

theorem trs_snd_eq_nil_of_simp_path'_and_prefix {a xs ts}
(h₁ : sys.simp_path' a ts) (h₂ : xs <+: ts) : (sys.trs a xs).2 = [] := by
  obtain ⟨b, hb⟩ := exi_trs_full_of_simp_path' h₁
  apply trs_snd_eq_nil_of_prefix_and_eq_nil h₂
  rw [hb]

theorem simp_path'_snoc_iff {a ts t} :
sys.simp_path' a (ts ++ [t]) ↔ sys.simp_path' a ts ∧
∀ b, sys.trs a ts = (b, []) → ∀ xs, xs <+: ts →
∃ c, sys.tr b t = some c ∧ sys.trs a xs ≠ (c, []) := by
  classical
  constructor
  · intro h
    constructor
    · apply simp_path'_of_prefix_simp_path' h
      simp
    intro b hb xs hx
    obtain ⟨c, hc⟩ := exi_trs_full_of_simp_path' h
    use c
    simp [trs_append, hb] at hc
    split at hc
    · simp at hc
    nm x d h₁; clear x
    simp at hc
    symm at hc; subst hc
    use h₁
    specialize h xs (ts ++ [t])
    intro h₂
    simp [hx, trs_append, hb, h₁, h₂] at h
    simp [h] at hx
  rintro ⟨h₁, h₂⟩ xs ys h₃ h₄ h₅
  
  wlog hxy : xs <+: ys with ih
  · symm
    apply ih h₁ h₂ ys xs h₄ h₃ h₅.symm
    clear ih
    have h₆ := List.prefix_or_prefix_of_prefix h₃ h₄
    simp [hxy] at h₆
    exact h₆
  nm x₁ x₂ x₃; clear! x₁ x₂ x₃
  
  simp at h₃
  symm at h₃
  rcases h₃ with rfl | h₃
  · exact List.prefix_antisymm hxy h₄
  simp at h₄
  rcases h₄ with h₄ | rfl
  · exact h₁ xs ys h₃ h₄ h₅
  
  clear hxy
  exfalso
  
  obtain ⟨b, hb⟩ := exi_trs_full_of_simp_path' h₁
  
  specialize h₂ b hb xs h₃
  obtain ⟨c, hc, h₂⟩ := h₂
  
  simp [trs_append, hb, hc] at h₅
  apply h₂; clear h₂
  ext1
  use h₅
  dsimp
  exact trs_snd_eq_nil_of_simp_path'_and_prefix h₁ h₃

theorem exi_cyclic_simulate_of_not_simp_path' {a ts}
(h : ¬sys.simp_path' a ts) (hh : (sys.trs a ts).2 = []) :
∃ f, sys.SimFn f ∧ ∃ n m, n ≠ m ∧
(sys.simulate f a n).2 = 0 ∧ (sys.simulate f a m).2 = 0 ∧
(sys.simulate f a n).1 = (sys.simulate f a m).1 := by
  classical
  replace h := exi_simp_path_prefix_of_not_simp_path' h
  obtain ⟨xs, t, h₁, h₂, h₃⟩ := h
  haveI ht : Inhabited T := ⟨t⟩
  
  obtain ⟨b, hb⟩ := exi_trs_full_of_simp_path' h₂
  obtain ⟨c, hc⟩ : ∃ c, sys.tr b t = some c :=
    by
      by_contra! h₄
      rw [←Option.eq_none_iff_forall_ne_some] at h₄
      have h₅ : sys.trs a (xs ++ [t]) = (b, [t]) :=
        by
          simp [trs_append, hb, h₄]
      have h₆ := trs_snd_eq_nil_of_prefix_and_eq_nil h₁ hh
      simp [h₅] at h₆
  clear! ts
  
  rw [simp_path'_snoc_iff] at h₃
  push_neg at h₃
  specialize h₃ h₂
  obtain ⟨b₁, hb₁, ys, hy, h₃⟩ := h₃
  simp [hb] at hb₁
  subst hb₁
  specialize h₃ c hc
  obtain ⟨f, hf, h₄⟩ := exi_simulate_of_simp_path ⟨h₂, hb⟩
  have hc₁ : sys.valid_tr b t := ⟨_, hc⟩
  use fn_set b t f, sim_fn_fn_set_of hc₁
  use ys.length, (xs.length + 1)
  have h₅ := hy.length_le
  use by linarith
  rw [simulate_fn_set_eq_of hc₁]
  rotate_left
  · intro k hk
    specialize h₂ (xs.take k) xs
    simp [hy, hb] at h₂
    rw [h₄ k # by linarith]
    intro h₆
    specialize h₂ h₆
    linarith
  rw [h₄ _ h₅, List.take_length_eq_of_prefix hy, h₃]
  dsimp only
  symm
  rw [simulate_add]
  rw [simulate_fn_set_eq_of hc₁]
  rotate_left
  · intro k hk
    specialize h₂ (xs.take k) xs
    simp [hb] at h₂
    contrapose! h₂
    refine' ⟨_, hk⟩
    rw [h₄ k # by linarith] at h₂
    exact h₂
  rw [h₄ _ # by rfl]
  simp [hb, hc]

theorem exi_simulate_full_of_simulate_eq {f a n r}
(hr : sys.simulate f a n = r) : ∃ k ≤ n, sys.simulate f a k = (r.1, 0) := by
  induction n generalizing a r
  · use 0; simp [←hr]
  nm n ih
  dsimp at hr
  split at hr
  · nm x h₁; clear x
    simp [simulate_eq_of_tr_eq_none h₁, ←hr]
  nm x b h₁; clear x
  specialize @ih b r hr
  obtain ⟨k, hk, ih⟩ := ih
  use k + 1, by linarith
  simpa [h₁]

theorem exi_simulate_full_of_simulate_fst_eq {f a n b}
(hr : (sys.simulate f a n).1 = b) : ∃ k ≤ n, sys.simulate f a k = (b, 0) := by
  generalize h₁ : sys.simulate f a n = r at hr
  obtain ⟨k, hk, h₂⟩ := exi_simulate_full_of_simulate_eq h₁
  subst h₁
  use k, hk
  simpa [h₂]

theorem acyclic_iff_sim_full_inj {a} :
sys.Acyclic a ↔ ∀ f [sys.SimFn f] n m,
(sys.simulate f a n).2 = 0 → (sys.simulate f a m).2 = 0 →
(sys.simulate f a n).1 = (sys.simulate f a m).1 → n = m := by
  classical
  constructor
  · intro h₁ f hf n m
    exact sim_full_inj_of_acyclic
  intro h
  contrapose! h
  simp [acyclic_iff] at h
  obtain ⟨b, h₁, c, ⟨t, hb⟩, h₂⟩ := h
  obtain ⟨xs, hx⟩ := exi_trs_of_reachable h₁
  obtain ⟨ys, hy⟩ := exi_trs_of_reachable h₂
  obtain ⟨zs, hz⟩ := hv # xs ++ t :: ys
  have h₃ : ¬sys.simp_path' a zs :=
    by
      unfold simp_path'
      push_neg
      use xs, zs
      simp [hz]
      rw [trs_append]
      simp [hx, hb, hy]
  have h₄ : (sys.trs a zs).2 = [] :=
    by
      simp [hz]
      rw [trs_append]
      simp [hx, hb, hy]
  obtain ⟨f, hf, n, m, h₅, h₆⟩ := exi_cyclic_simulate_of_not_simp_path' h₃ h₄
  clear h₃ h₄
  use f, hf, n, m
  simpa [h₅]

theorem acyclic_iff_sim_inj {a} :
sys.Acyclic a ↔ ∀ f [sys.SimFn f] n m,
sys.simulate f a n = sys.simulate f a m → n = m := by
  rw [acyclic_iff_sim_full_inj]
  symm; constructor
  · intro h
    intro f hf n m h₁ h₂ h₃
    apply h f n m
    ext
    · exact h₃
    rwa [h₂]
  intro h f hf n m hn
  specialize h f (n - (sys.simulate f a n).2) (m - (sys.simulate f a m).2)
  simp at h
  simp [←hn] at h
  by_contra h₁
  wlog h₂ : n < m with ih
  · apply @ih S T sys a f hf m n hn.symm _ (by omega) (by omega)
    rw [←hn]
    exact h.symm
  nm x₁ x₂ x₃; clear! x₁ x₂ x₃
  clear h₁
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h₂
  have h₁ : (sys.simulate f a n).2 ≤ n := snd_le_of_simulate_eq rfl
  omega

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
  exact reachable_of_simulate h₆

theorem exi_simp_path_of_trs_eq {a ts r} (h : sys.trs a ts = r) :
∃ ts', sys.simp_path a ts' r.1 :=
  exi_simp_path_of_reachable # reachable_of_trs_eq' h

theorem exi_simulate_of_trs_eq [ht : Inhabited # S → T] {a ts r}
(h₁ : sys.trs a ts = r) : ∃ f, sys.SimFn f ∧
∃ n, sys.simulate f a n = (r.1, 0) := by
  obtain ⟨xs, hx⟩ := exi_simp_path_of_trs_eq h₁
  obtain ⟨f, hf, h₂⟩ := exi_simulate_of_simp_path hx
  use f, hf, xs.length
  specialize h₂ _ # by rfl
  simp at h₂
  rw [h₂, hx.2]

theorem exi_simulate_of_reachable {a b}
[ht : Inhabited # S → T] (h : sys.Reachable a b) :
∃ (f : S → T), sys.SimFn f ∧ ∃ (n : ℕ), sys.simulate f a n = (b, 0) := by
  obtain ⟨xs, hx⟩ := exi_trs_of_reachable h
  exact exi_simulate_of_trs_eq hx

theorem reachable_iff_exi_simulate [hi : Inhabited # S → T] {a b} :
sys.Reachable a b ↔ ∃ (f : S → T), sys.SimFn f ∧
∃ n, sys.simulate f a n = (b, 0) := by
  use exi_simulate_of_reachable
  rintro ⟨f, hf, h₁, h₂⟩
  exact reachable_of_simulate # congrArg (·.1) h₂

theorem simulate_fst_eq_fst_of_snd_ne_zero {f a n m}
(h₁ : (sys.simulate f a n).2 ≠ 0) (h₂ : (sys.simulate f a m).2 ≠ 0) :
(sys.simulate f a n).1 = (sys.simulate f a m).1 := by
  wlog h₃ : n ≤ m with ih
  · symm; exact ih h₂ h₁ (by linarith)
  nm x₁ x₂ x₃; clear! x₁ x₂ x₃
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h₃; clear h₃
  generalize hr₁ : sys.simulate f a n = r₁ at h₂ ⊢
  generalize hr₂ : sys.simulate f a (n + m) = r₂ at h₂ ⊢
  rcases r₁ with ⟨b, k₁⟩
  rcases r₂ with ⟨c, k₂⟩
  dsimp at h₁ h₂ ⊢
  simp [hr₁] at h₁
  simp [simulate_add, hr₁, h₁] at hr₂
  exact hr₂.1

theorem simp_path'_iff_nodup {a} {ts : List T} :
sys.simp_path' a ts ↔ (ts.inits.map # λ xs => (sys.trs a xs).1).Nodup := by
  classical
  constructor <;> intro h
  · rw [List.nodup_map_iff_inj_on]
    · intro xs hx ys hy
      simp at hx hy
      apply h <;> assumption
    simp
  intro xs ys hx hy h₁
  rw [List.nodup_iff_injective_getElem] at h
  by_contra! h₂
  have h₃ := hx.length_le
  have h₄ := hy.length_le
  specialize @h ⟨xs.length, by simp; linarith⟩ ⟨ys.length, by simp; linarith⟩
  simp at h
  contrapose! h; clear h
  symm
  constructor
  · contrapose! h₂
    exact List.eq_of_prefix_and_length_eq hx hy h₂
  rwa [List.take_length_eq_of_prefix hx, List.take_length_eq_of_prefix hy]

theorem reachable_of_trs_eq {a ts b} (h : (sys.trs a ts).1 = b) :
sys.Reachable a b := by
  subst h; exact reachable_of_trs_eq' rfl

theorem trs_full_inj_of_acyclic {a} [h : sys.Acyclic a] {xs ys}
(hx : xs <+: ys) (h₁ : (sys.trs a xs).2 = []) (h₂ : (sys.trs a ys).2 = [])
(h₃ : (sys.trs a xs).1 = (sys.trs a ys).1) : xs = ys := by
  classical
  rw [acyclic_iff] at h
  generalize hr₁ : sys.trs a xs = r₁ at h₁ h₃
  generalize hr₂ : sys.trs a ys = r₂ at h₁ h₃
  obtain ⟨b, rs₁⟩ := r₁
  obtain ⟨c, rs₂⟩ := r₂
  subst h₁ h₃
  dsimp at hr₂
  simp [hr₂] at h₂
  subst h₂
  obtain ⟨ys, rfl⟩ := hx
  rename' hr₁ => h₁
  rename' hr₂ => h₂
  cases ys
  · simp
  nm y ys
  exfalso
  rw [List.append_cons] at h₂
  
  obtain ⟨c, hc⟩ : ∃ c, sys.trs a (xs ++ [y]) = (c, []) :=
    by
      simp [Prod.ext_iff]
      exact trs_snd_eq_nil_of_prefix_and_eq_nil
        (by simp : xs ++ [y] <+: xs ++ [y] ++ ys) (by rw [h₂])
  
  rw [trs_append] at h₂
  simp [hc] at h₂
  
  simp [trs_append, h₁] at hc
  split at hc <;> simp at hc
  nm x d h₃; clear x
  symm at hc; subst hc
  
  apply @h b c y _ h₃ _
  · exact reachable_of_trs_eq # congrArg (·.1) h₁
  · exact reachable_of_trs_eq # congrArg (·.1) h₂

theorem acyclic_of_trs_full_inj {a}
(h : ∀ xs ys, xs <+: ys →
(sys.trs a xs).2 = [] → (sys.trs a ys).2 = [] →
(sys.trs a xs).1 = (sys.trs a ys).1 → xs = ys) :
sys.Acyclic a := by
  classical
  rw [acyclic_iff]
  intro b c t h₁ hb h₂
  obtain ⟨xs, hx⟩ := exi_trs_of_reachable h₁
  obtain ⟨ys, hy⟩ := exi_trs_of_reachable h₂
  specialize h xs (xs ++ [t] ++ ys)
  simp [hx] at h
  unfold tr_to at hb
  rw [List.append_cons, trs_append] at h
  simp [trs_append, hx, hb, hy] at h

theorem acyclic_iff_trs_full_inj {a} :
sys.Acyclic a ↔ ∀ xs ys, xs <+: ys →
(sys.trs a xs).2 = [] → (sys.trs a ys).2 = [] →
(sys.trs a xs).1 = (sys.trs a ys).1 → xs = ys := by
  classical
  use by apply trs_full_inj_of_acyclic
  exact acyclic_of_trs_full_inj

@[simp]
theorem trs_take_length_sub_eq {a xs} :
sys.trs a (xs.take (xs.length - (sys.trs a xs).2.length)) =
((sys.trs a xs).1, []) := by
  induction xs generalizing a
  · rfl
  nm x xs ih
  simp
  split
  · simp
  nm y b h₁; clear y
  rw [Nat.add_one_sub trs_snd_length_le]
  simp [h₁]
  exact ih

theorem trs_snd_eq_nil_of_trs_eq_of_prefix_and_and_ne {a xs ys}
(h₁ : sys.trs a xs = sys.trs a ys) (h₂ : xs <+: ys) (h₃ : xs ≠ ys) :
(sys.trs a xs).2 = [] := by
  classical
  obtain ⟨ys, rfl⟩ := h₂
  by_contra h₂
  simp [trs_append, h₂, Prod.ext_iff] at h₁
  simp [h₁] at h₃

theorem trs_inj_of_acyclic {a} [h : sys.Acyclic a] {xs ys}
(hx : xs <+: ys) (h₁ : sys.trs a xs = sys.trs a ys) : xs = ys := by
  classical
  rw [acyclic_iff_trs_full_inj] at h
  specialize h # xs.take (xs.length - (sys.trs a xs).2.length)
  specialize h # ys.take (ys.length - (sys.trs a ys).2.length)
  simp at h
  specialize h _ # by rw [h₁]
  · clear h
    rw [List.prefix_take_iff]
    constructor
    · trans xs
      · simp
      exact hx
    simp [h₁]
    exact hx.length_le
  by_contra h₂
  have h₃ := trs_snd_eq_nil_of_trs_eq_of_prefix_and_and_ne h₁ hx h₂
  obtain ⟨ys, rfl⟩ := hx
  simp [trs_append, h₃] at h
  apply h₂; clear h₂
  symm at h₁
  simp [trs_append, h₃] at h₁
  simp [h₁, h₃] at h
  rw [List.take_of_length_le] at h; exact h
  simp

theorem acyclic_of_trs_inj {a}
(h : ∀ xs ys, xs <+: ys → sys.trs a xs = sys.trs a ys → xs = ys) :
sys.Acyclic a := by
  rw [acyclic_iff_trs_full_inj]
  intro xs ys hx h₁ h₂ h₃
  apply h xs ys hx
  ext1; exact h₃; rwa [h₂]

theorem acyclic_iff_trs_inj {a} :
sys.Acyclic a ↔ ∀ xs ys, xs <+: ys → sys.trs a xs = sys.trs a ys → xs = ys :=
  ⟨by apply trs_inj_of_acyclic, acyclic_of_trs_inj⟩

theorem acyclic_of_tr {a} [ha : sys.Acyclic a] {t b}
(h₁ : sys.tr_to a t b) : sys.Acyclic b :=
  acyclic_of_reachable # reachable_of_tr h₁

theorem simulate_succ_snd_eq_zero_of_tr_and_eq_zero {f a b n}
(h₁ : (sys.simulate f b n).2 = 0) (h₂ : sys.tr_to a (f a) b) :
(sys.simulate f a # n + 1).2 = 0 := by
  unfold tr_to at h₂; simpa [h₂]

theorem simulate_snd_eq_zero_of_tr_and_eq_zero {f a b n}
(h₁ : (sys.simulate f b n).2 = 0) (h₂ : sys.tr_to a (f a) b) :
(sys.simulate f a n).2 = 0 := by
  have h₃ := simulate_succ_snd_eq_zero_of_tr_and_eq_zero h₁ h₂
  exact simulate_snd_eq_zero_of_le_and_eq_zero h₃ # by linarith

theorem simulate_finset_card_eq_of_acyclic
[hs : DecidableEq S] {f} [hf : sys.SimFn f] {a} [ha : sys.Acyclic a] {n}
(h₁ : (sys.simulate f a n).2 = 0) : (mk_finset # λ (k : Fin # n + 1) =>
(sys.simulate f a k).1).card = n + 1 := by
  induction n generalizing a
  · simp
  nm n ih
  dsimp at h₁
  split at h₁; simp at h₁
  nm x b h₂; clear x
  rw [mk_finset_fin_succ_eq_insert]
  simp [h₂]
  have hb := acyclic_of_tr h₂
  have h₃ := simulate_snd_eq_zero_of_tr_and_eq_zero h₁ h₂
  rw [Finset.card_insert_of_notMem]
  · simp [@ih b _ h₁]; exact ih h₃
  simp
  rintro ⟨k, hk⟩
  simp
  rw [Nat.lt_succ_iff] at hk
  rw [acyclic_iff_sim_full_inj] at ha
  intro h₄
  specialize ha f k (n + 1)
    (simulate_snd_eq_zero_of_le_and_eq_zero h₃ hk)
  simp [h₂] at ha
  specialize ha h₁ h₄
  simp [ha] at hk

-- #check 0 #exit

@[simp]
theorem Fintype.elems_eq_empty_iff {α : Type} [ha : Fintype α] :
ha.elems = ∅ ↔ ∀ (_ : α), false := by simp [Finset.ext_iff]

theorem Finset.card_eq_card_iff_equiv {α β : Type}
{sa : Finset α} {sb : Finset β} : sa.card = sb.card ↔ Nonempty (sa ≃ sb) := by
  simp [←Cardinal.eq]

set_option linter.unusedVariables false
@[simp]
theorem Cardinal.mk_subtype_const_true {α : Type} :
Cardinal.mk {x : α // True} = Cardinal.mk α := by
  rw [Cardinal.eq]
  use λ ⟨x, _⟩ => x
  use λ x => ⟨x, trivial⟩
  · intro x; simp
  · intro x; simp
set_option linter.unusedVariables true

set_option linter.unusedVariables false
@[simp]
theorem nonempty_equiv_subtype_const_true_iff {α β : Type} :
Nonempty (α ≃ {x : β // True}) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]
set_option linter.unusedVariables true

theorem nonempty_equiv_comm {α β : Type} :
Nonempty (α ≃ β) ↔ Nonempty (β ≃ α) := by
  apply Nonempty.congr <;> exact λ h => h.symm

theorem mk_finset_toSet_eq {α β : Type} [ha : Fintype α] {f : α → β} :
(mk_finset f).toSet = Set.range f := by ext x; simp

theorem Finset.card_eq_cardinal_mk_to_nat {α : Type} {s : Finset α} :
s.card = (Cardinal.mk s).toNat := by simp

@[simp]
theorem nonempty_equiv_refl {α : Type} : Nonempty (α ≃ α) := ⟨by rfl⟩

theorem Set.nonempty_equiv_empty_empty {α β : Type} :
Nonempty ((∅ : Set α) ≃ (∅ : Set β)) := by
  refine' ⟨⟨_, _, _, _⟩⟩
  all_goals try rintro ⟨x, h⟩; simp at h

@[simp]
theorem Set.nonempty_equiv_empty_iff {α β : Type} {s : Set α} :
Nonempty (s ≃ (∅ : Set β)) ↔ s = ∅ := by
  constructor
  · rintro ⟨h⟩
    ext x
    simp
    intro hx
    exact (h.toFun ⟨_, hx⟩).2
  · rintro rfl
    exact Set.nonempty_equiv_empty_empty

theorem Set.ncard_eq_ncard_iff_nonempty_equiv {α β : Type}
[ha : Fintype α] [hb : Fintype β] {sa : Set α} (sb : Set β) :
sa.ncard = sb.ncard ↔ Nonempty (sa ≃ sb) := by
  classical
  unfold Set.ncard Set.encard ENat.card
  simp [Finset.card_eq_card_iff_equiv]

theorem nonempty_equiv_trans {α γ : Type} (β : Type)
(h₁ : Nonempty (α ≃ β)) (h₂ : Nonempty (β ≃ γ)) : Nonempty (α ≃ γ) := by
  rcases h₁ with ⟨a⟩
  rcases h₂ with ⟨b⟩
  exact ⟨a.trans b⟩

theorem nonempty_equiv_set_univ_self {α : Type} :
Nonempty (α ≃ (Set.univ : Set α)) := by
  simp [←Cardinal.eq]

theorem nonempty_equiv_set_univ_self' {α : Type} :
Nonempty ((Set.univ : Set α) ≃ α) := by
  simp [←Cardinal.eq]

theorem nonempty_equiv_set_univ_set_univ_iff {α β : Type} :
Nonempty ((Set.univ : Set α) ≃ (Set.univ : Set β)) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

@[simp]
theorem nonempty_equiv_set_univ_iff {α β : Type} :
Nonempty (α ≃ (Set.univ : Set β)) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

@[simp]
theorem nonempty_equiv_set_univ_iff' {α β : Type} :
Nonempty ((Set.univ : Set α) ≃ β) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

theorem Finset.card_eq_toSet_ncard {α : Type} {s : Finset α} :
s.card = s.toSet.ncard := by simp

noncomputable
instance {α : Type} [Fintype α] {s : Set α} : Fintype s := by
  exact Fintype.ofFinite ↑s

theorem fintype_card_set_eq_ncard {α : Type} [ha : Fintype α] {s : Set α} :
Fintype.card s = s.ncard := by
  unfold Fintype.card
  rw [Finset.card_eq_cardinal_mk_to_nat]
  unfold Set.ncard Set.encard ENat.card
  apply congrArg (Cardinal.toNat)
  simp

#check 0 #exit

theorem mk_finset_card_eq_set_range_card {α β : Type}
[ha : Fintype α] {f : α → β} :
(mk_finset f).card = (Set.range f).ncard := by
  classical
  simp [Finset.card_eq_cardinal_mk_to_nat]
  have h₁ : Cardinal.mk {x // ∃ a, f a = x} = Cardinal.mk (Set.range f) :=
    by
      rw [Cardinal.eq]
      exact nonempty_equiv_refl
  rw [h₁]
  clear h₁
  simp
  rw [Fintype.card_set_eq_ncard]

-- #check 0 #exit

theorem Set.nonempty_range_equiv_self_iff_injective {α β : Type}
[ha : Fintype α] {f : α → β} : Nonempty (Set.range f ≃ α) ↔ f.Injective := by
  sorry

#check 0 #exit

theorem Set.nonempty_range_equiv_self_iff_injective {α β : Type}
[ha : Fintype α] {f : α → β} : Nonempty (Set.range f ≃ α) ↔ f.Injective := by
  classical
  have h₁ := @Set.ncard_eq_ncard_iff_nonempty_equiv (Set.range f) α _ _
    Set.univ Set.univ
  simp at h₁
  rw [←h₁]; clear h₁
  rw [←mk_finset_card_eq_set_range_card]
  exact?

#check 0 #exit

@[simp]
theorem mk_finset_card_eq_fintype_card_iff {α β} [ha : Fintype α] {f : α → β} :
(mk_finset f).card = Fintype.card α ↔ f.Injective := by
  classical
  
  change _ = (Finset.univ : Finset α).card ↔ _
  symm; constructor <;> intro h
  · rw [Nat.eq_iff_le_and_ge]
    constructor
    · apply mk_finset_card_le
    apply Finset.card_le_card_of_injOn f <;> simp [h]
  
  rw [mk_finset_card_eq_set_range_card] at h
  simp [Fintype.card_eq] at h
  obtain ⟨e⟩ := h
  
  obtain ⟨g, g', h₁, h₂⟩ := h

#check 0 #exit

theorem simulate_exi_snd_pos_of_finite'
[hs : Fintype S] {a} [ha : Acyclic sys a] {f} [hf : SimFn sys f] :
∃ N, ∀ n, N ≤ n → ∃ k, 0 < k ∧ ∃ x, sys.simulate f a n = (x, k) := by
  classical
  generalize hN : hs.card = N
  have h₁ := simulate_finset_card_eq_of_acyclic (ha := ha) (f := f) (n := N)
  by_contra! h₂
  specialize h₂ N
  obtain ⟨n, hn, h₂⟩ := h₂
  specialize h₂ (sys.simulate f a n).2
  simp [Prod.ext_iff] at h₂
  specialize h₁ # simulate_snd_eq_zero_of_le_and_eq_zero h₂ hn
  replace hn : ¬(N + 1 ≤ N) := by linarith
  apply hn; clear hn
  rw [←h₁]
  have := @mk_finset_card_le (Fin # N + 1) S _ _ _
    (λ k => (sys.simulate f a k).1)
  simp at this

#check 0 #exit

theorem simulate_exi_snd_pos_of_finite
[h₁ : Fintype S] {s} [h₂ : Acyclic sys s] {f} [h₃ : SimFn sys f] :
∃ x N, ∀ n, N ≤ n → ∃ k, 0 < k ∧ sys.simulate f s n = (x, k) := by
  classical
  obtain ⟨N, h₄⟩ := @simulate_exi_snd_pos_of_finite' S T sys h₁ s h₂ f h₃
  obtain ⟨m, hm⟩ := hv # nat_find λ n => (sys.simulate f s n).2 ≠ 0
  use (sys.simulate f s m).1, N
  intro n hn
  specialize h₄ n hn
  obtain ⟨k, hk, x, h₄⟩ := h₄
  use k, hk
  symm
  simp [h₄]
  have h₅ : (sys.simulate f s m).2 ≠ 0 :=
    by
      subst hm
      unfold nat_find
      split_ifs with h₅
      · have h₆ := Nat.find_spec h₅
        convert h₆
      contrapose! h₅
      use n
      rw [h₄]
      linarith
  have h₆ : (sys.simulate f s n).1 = (sys.simulate f s m).1 :=
    by
      apply simulate_fst_eq_fst_of_snd_ne_zero _ h₅
      rw [h₄]
      linarith
  rw [←h₆, h₄]