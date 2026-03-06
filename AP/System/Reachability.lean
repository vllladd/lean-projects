import AP.System.Basic

namespace System

universe u
variable {S T : Type u} {sys : System S T}

theorem sim_full_inj_of_acyclic {s} [ha : sys.Acyclic s]
{f} [hf : sys.SimFn f] {n m} :
(sys.simulate f s n).2 = 0 → (sys.simulate f s m).2 = 0 →
(sys.simulate f s n).1 = (sys.simulate f s m).1 → n = m := by
  rename' ha => h₁
  rw [acyclic_def] at h₁
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
  simp [h₂, ←ha, simulate] at h₃
  split at h₃
  · simp [←h₃] at h₂
  nm x b h₄
  apply @h₁.2 a b (f a) (reachable_of_simulate' ha.symm) h₄
  apply @reachable_of_simulate S T sys f b a m
  rw [h₃, ha]

@[simp]
theorem reachable_fst_simulate {f} {s n} : sys.Reachable s (sys.simulate f s n).1 := by
  induction n generalizing s
  · rfl
  nm n ih
  simp [simulate]
  split
  · rfl
  nm x s₁ h₁; clear x
  trans s₁
  · exact reachable_of_tr h₁
  exact ih

theorem simFn_fn_set_of [DecidableEq S] {f} [hf : sys.SimFn f] {s t}
(h : sys.validTr s t) : sys.SimFn # fn_set s t f := by
  rw [simFn_def] at hf ⊢
  intro a ha h₁
  unfold fn_set
  split_ifs with h₂
  · rwa [h₂]
  exact hf h₁

@[grind →, grind <=]
theorem acyclic_of_reachable {a} [ha : sys.Acyclic a] {b}
(h : sys.Reachable a b) : sys.Acyclic b := by
  rw [acyclic_def] at ha ⊢
  rcases ha with ⟨hs, ha⟩
  use by grind
  intro c d t h₁ h₂
  exact @ha c d t (h.trans h₁) h₂

theorem simulate_fn_set_eq_of [DecidableEq S] {f} [hf : sys.SimFn f]
{a b t n} [ha : sys.WF a]
(h₁ : sys.validTr b t) (h₂ : ∀ k < n, (sys.simulate f a k).1 ≠ b) :
sys.simulate (fn_set b t f) a n = sys.simulate f a n := by
  induction n generalizing a
  · rfl
  nm n ih
  simp [simulate]
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
      have h₅ := hf.1 # hasTr_of_eq_some h₃
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
  have hc := wf_of_tr h₃
  apply ih
  intro k hk
  specialize h₂ (k + 1) # by linarith
  simp [h₃, simulate] at h₂
  exact h₂

theorem simulate_snd_eq_zero_of_le_and_eq_zero {f a k n}
(h₁ : (sys.simulate f a n).2 = 0) (h₂ : k ≤ n) :
(sys.simulate f a k).2 = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h₂
  simp [simulate_add] at h₁
  by_contra h₃
  simp [h₃] at h₁

theorem simulate_snd_eq_zero_of_hasTr {f} [hf : sys.SimFn f] {a n} [ha : sys.WF a]
(h : sys.hasTr (sys.simulate f a n).1) : (sys.simulate f a n).2 = 0 := by
  induction n generalizing a; rfl; nm n ih
  simp [simulate] at h ⊢
  split at h
  · nm x h₁; clear x
    obtain ⟨s, hs⟩ := hf.1 h
    simp [h₁] at hs
  nm x b h₁; clear x
  have hb := wf_of_tr h₁
  exact ih h

theorem acyclic_of_tree {a} [ht : sys.Tree a] : sys.Acyclic a := by
  classical
  rw [tree_def] at ht
  rw [acyclic_def]
  rcases ht with ⟨hs, ht⟩; use hs
  intro b c t h₁ h₃ h₂
  obtain ⟨ts₁, h₁⟩ := exi_trs_of_reachable h₁
  obtain ⟨ts₂, h₂⟩ := exi_trs_of_reachable h₂
  nm x y; clear x y
  specialize @ht ts₁ (ts₁ ++ t :: ts₂) _
  · rw [trs_append]
    simp [h₁, h₂, h₃, trs]
  simp at ht

instance {a} [ht : sys.Tree a] : sys.Acyclic a := acyclic_of_tree

theorem simulate_eq_of_tr_eq_none {f a n}
(h : sys.tr a (f a) = none) : sys.simulate f a n = (a, n) := by
  cases n; rfl; nm n; simp [h, simulate]

theorem exi_trs_of_simulate_eq {f a n r} (h₁ : sys.simulate f a n = r) :
∃ ts, sys.trs a ts = (r.1, []) ∧ n = ts.length + r.2 := by
  induction n generalizing a r
  · use []
    subst h₁
    simp
  nm n ih
  simp [simulate] at h₁
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
  obtain ⟨rfl⟩ := @ht.2 ts ts₁ # by rwa [h₁]
  linarith

theorem eq_of_tree_and_trs_eq {a} [ht : sys.Tree a] {ts₁ ts₂ b}
(hb : sys.trs a ts₁ = (b, [])) (hc : sys.trs a ts₂ = (b, [])) : ts₁ = ts₂ := by
  apply ht.2; rwa [hc]

theorem trs_snd_eq_nil_of_prefix_and_eq_nil {a xs ys}
(h₁ : xs <+: ys) (h₂ : (sys.trs a ys).2 = []) : (sys.trs a xs).2 = [] := by
  classical
  induction xs generalizing a ys
  · rfl
  nm x xs ih
  cases ys; simp at h₁
  nm y ys
  simp at h₁
  rcases h₁ with ⟨rfl, h₁⟩
  simp at h₂ ⊢
  choose s₁ h₂ h₃ using h₂
  use s₁, h₂
  exact ih h₁ h₃

theorem exi_simp_path_of_full_trs_eq {a b ts} (h : sys.trs a ts = (b, [])) :
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
  exact exi_simp_path_of_full_trs_eq h₁

theorem simp_path'_of_cons_and_tr_eq_some {a b t ts}
(h₁ : sys.simp_path' a (t :: ts)) (h₂ : sys.tr a t = some b) :
sys.simp_path' b ts := by
  reduce at h₁ h₂
  intro xs ys h₃ h₄ h₅
  specialize h₁ (t :: xs) (t :: ys) (by simpa) (by simpa) (by simpa [trs, h₂])
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

theorem hasTr_of_validTr {a t} (h : sys.validTr a t) : sys.hasTr a := ⟨t, h⟩

@[simp]
theorem validTr_iff_of_simFn {f} [h : sys.SimFn f] {a} [ha : sys.WF a] :
sys.validTr a (f a) ↔ sys.hasTr a := ⟨hasTr_of_validTr, h.1 (s := a)⟩

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
    simp [ih]
  nm n ih₁
  simp [simulate]
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
  nth_rw 2 [add_comm] at h
  exact simulate_eq_of_simulate_add_eq_add h

theorem simulate_eq_of_iter_le {f : S → T} {n k}
(hk : k ≤ n) (g : ℕ → S)
(h₁ : ∀ k < n, sys.validTr (g k) (f # g k))
(h₂ : ∀ k < n, sys.tr (g k) (f # g k) = g (k + 1)) :
sys.simulate f (g 0) k = (g k, 0) := by
  induction k
  · rfl
  nm k ih
  specialize ih # by linarith
  cases n <;> simp at hk
  nm n
  specialize h₂ k # by linarith
  rw [simulate_add_one_full]
  simp_all only [Prod.mk.injEq, and_true, exists_eq_left']

theorem simulate_eq_of_iter {f : S → T} {n} (g : ℕ → S)
(h₁ : ∀ k < n, sys.validTr (g k) (f # g k))
(h₂ : ∀ k < n, sys.tr (g k) (f # g k) = g (k + 1)) :
sys.simulate f (g 0) n = (g n, 0) := by
  apply simulate_eq_of_iter_le # by rfl
  all_goals assumption

theorem hasTr_trs_of_prefix {a b xs ys}
(h₁ : sys.trs a ys = (b, [])) (h₂ : xs <+: ys) (h₃ : xs ≠ ys) :
sys.hasTr (sys.trs a xs).1 := by
  classical
  obtain ⟨ys, rfl⟩ := h₂
  cases ys
  · simp at h₃
  nm y ys
  clear h₃
  rw [List.append_cons] at h₁
  simp at h₁
  choose s₁ h₁ s₂ h₂ h₃ using h₁
  rw [h₁]
  use y, s₂

@[simp]
theorem not_validTr_iff {a t} : ¬sys.validTr a t ↔ sys.tr a t = none := by
  simp [validTr, Option.eq_none_iff_forall_ne_some]

theorem tr_trs_list_take_eq_some_of {ts : List T} {a n}
(h₁ : n < ts.length) (h₂ : (sys.trs a ts).2 = []) :
sys.tr (sys.trs a # ts.take n).1 ts[n] = some (sys.trs a # ts.take # n + 1).1 := by
  classical
  induction n generalizing a ts
  · simp
    cases ts
    · simp at h₁
    nm t ts
    simp at h₂ ⊢
    choose b h₂ h₃ using h₂
    simp [trs, h₂]
  nm n ih
  cases ts
  · simp at h₁
  nm t ts
  simp at h₂
  choose b h₂ h₃ using h₂
  simp [trs, h₂]
  exact @ih ts b (by rwa [←Nat.succ_lt_succ_iff]) h₃

theorem validTr_trs_list_take_of {ts : List T} {a n}
(h₁ : n < ts.length) (h₂ : (sys.trs a ts).2 = []) :
sys.validTr (sys.trs a # ts.take n).1 ts[n] :=
  ⟨_, tr_trs_list_take_eq_some_of h₁ h₂⟩

theorem wf_trs {a} [ha : sys.WF a] {ts} : sys.WF # (sys.trs a ts).1 := by
  rw [wf_def] at ha ⊢
  obtain ⟨s, h₁, h₂⟩ := ha
  use s, h₁
  apply h₂.trans
  simp

instance {a} [ha : sys.WF a] {ts} : sys.WF # (sys.trs a ts).1 := wf_trs

theorem exi_simulate_of_simp_path [ht : Inhabited # S → T] {a b ts} [hs : sys.WF a]
(h : sys.simp_path a ts b) : ∃ f, sys.SimFn f ∧ ∀ k ≤ ts.length,
sys.simulate f a k = ((sys.trs a # ts.take k).1, 0) := by
  classical
  obtain ⟨f, hf⟩ := hv # sys.mkSimFn # λ s =>
    ts[Nat.find! # λ n => sys.trs a (ts.take n) = (s, [])]?.getD # sys.dfltSimFn s
  use f
  constructor
  · rw [hf]; infer_instance
  generalize hn : ts.length = n
  rcases h with ⟨h₂, h₁⟩
  intro k hk
  apply simulate_eq_of_iter_le hk # λ k => (sys.trs a # ts.take k).1
    <;> clear! k <;> intro k hk
  · rw [hf]
    apply validTr_of_simFn_and_hasTr
    apply hasTr_trs_of_prefix h₁ # by simp
    apply ne_of_congr (·.length)
    simpa [hn]
  subst hf
  unfold mkSimFn
  dsimp
  rw! (castMode := .all) [Nat.find!_eq_of (n := k)]
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
  rw! (castMode := .all) [List.getElem?_eq_getElem # by linarith]
  simp
  rw [List.take_add_one, List.getElem?_eq_getElem # by linarith, Option.toList_some,
    trs_append]
  simp
  rw [trs_snd_eq_nil_of_prefix_and_eq_nil (ys := ts) (by simp) (by rw [h₁])]
  simp
  split_ifs with h₃
  · obtain ⟨c, h₃⟩ := h₃
    symm; simp [trs, h₃]
  exfalso
  apply h₃; clear h₃
  apply validTr_trs_list_take_of
  rw [h₁]

@[simp]
theorem simp_path_self_iff {a xs} : sys.simp_path a xs a ↔ xs = [] := by
  unfold simp_path simp_path'
  cases xs <;> simp
  nm x xs
  intro h₁ b h₂
  specialize h₁ [] (x :: xs)
  simp [trs, h₂] at h₁
  contrapose! h₁
  rw [h₁]

@[simp]
theorem simp_path_nil_iff {a b} : sys.simp_path a [] b ↔ a = b := by
  simp [simp_path, simp_path']

@[simp]
theorem simp_path_singleton_iff {a b t} :
sys.simp_path a [t] b ↔ a ≠ b ∧ sys.tr a t = some b := by
  simp [simp_path, simp_path']
  intro h₁
  constructor
  · rintro h₂ rfl
    specialize h₂ [] [t]
    simp [trs, h₁] at h₂
  intro h₂ xs ys hx hy h₃
  cases xs
  · simp at h₃
    cases ys
    · rfl
    nm y ys
    simp at hy
    rcases hy with ⟨rfl, rfl⟩
    simp [trs, h₁, h₂] at h₃
  nm x xs
  simp at hx
  rcases hx with ⟨rfl, rfl⟩
  simp [trs, h₁] at h₃
  cases ys
  · simp [h₃] at h₂
  nm y ys
  simp at hy
  simp [hy]

theorem simp_path'_snoc_of (b c : S) {a ts t}
(h₁ : sys.simp_path a ts b) (h₂ : sys.tr b t = some c)
(h₃ : ∀ xs, xs <+: ts → (sys.trs a xs).1 ≠ c) :
sys.simp_path' a (ts ++ [t]) := by
  classical
  rcases h₁ with ⟨ha₁, ha₂⟩
  intro xs ys hx hy h₄
  by_cases h₅ : xs = ts ++ [t]
  · subst h₅; clear hx
    rw [trs_append] at h₄
    simp [trs, ha₂, h₂] at h₄
    symm
    by_contra h₆
    apply h₃ ys (List.prefix_of_prefix_snoc_and_ne hy h₆) h₄.symm
  replace hx := List.prefix_of_prefix_snoc_and_ne hx h₅
  clear h₅
  by_cases h₅ : ys = ts ++ [t]
  · subst h₅; clear hy
    rw [trs_append] at h₄
    simp [trs, ha₂, h₂] at h₄
    by_contra h₆
    exact h₃ xs hx h₄
  replace hy := List.prefix_of_prefix_snoc_and_ne hy h₅
  clear h₅
  exact ha₁ xs ys hx hy h₄

theorem simp_path_snoc_of {a b c ts t}
(h₁ : sys.simp_path a ts b) (h₂ : sys.tr b t = some c)
(h₃ : ∀ xs, xs <+: ts → (sys.trs a xs).1 ≠ c) :
sys.simp_path a (ts ++ [t]) c := by
  classical
  rcases h₁ with ⟨ha₁, ha₂⟩
  use simp_path'_snoc_of b c (by use ha₁) h₂ h₃
  simp [trs_append, ha₂, h₂]

@[simp]
theorem trs_snd_suffix {a xs} : (sys.trs a xs).2 <:+ xs := by
  induction xs generalizing a
  · rfl
  nm x xs ih
  simp [trs]
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
  simp [trs] at hr
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
  induction ts using List.reverseRecOn
  · simp at h₁
  nm ts t ih
  rw [←or_iff_not_imp_left] at ih
  rcases ih with ih | ih
  · use ts, t
  obtain ⟨xs, x, h₂, h₃, h₄⟩ := ih
  use xs, x
  exact ⟨h₂.trans # by simp, h₃, h₄⟩

theorem exi_full_trs_of_simp_path' {a ts}
(h : sys.simp_path' a ts) : ∃ b, sys.trs a ts = (b, []) := by
  classical
  induction ts using List.reverseRecOn
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
  · simp [trs, h₁] at hr
    split at hr <;> simp at hr <;> tauto
  simp at hr
  tauto

theorem trs_snd_eq_nil_of_simp_path'_and_prefix {a xs ts}
(h₁ : sys.simp_path' a ts) (h₂ : xs <+: ts) : (sys.trs a xs).2 = [] := by
  obtain ⟨b, hb⟩ := exi_full_trs_of_simp_path' h₁
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
    obtain ⟨c, hc⟩ := exi_full_trs_of_simp_path' h
    use c
    rw [trs_append] at hc
    simp [trs, hb] at hc
    split at hc
    · simp at hc
    nm x d h₁; clear x
    simp at hc
    symm at hc; subst hc
    use h₁
    specialize h xs (ts ++ [t])
    intro h₂
    rw [trs_append] at h
    simp [hx, trs, hb, h₁, h₂] at h
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

  obtain ⟨b, hb⟩ := exi_full_trs_of_simp_path' h₁

  specialize h₂ b hb xs h₃
  obtain ⟨c, hc, h₂⟩ := h₂

  rw [trs_append] at h₅
  simp [trs, hb, hc] at h₅
  apply h₂; clear h₂
  ext1
  use h₅
  dsimp
  exact trs_snd_eq_nil_of_simp_path'_and_prefix h₁ h₃

theorem exi_cyclic_simulate_of_not_simp_path' {a ts} [ha : sys.WF a]
(h : ¬sys.simp_path' a ts) (hh : (sys.trs a ts).2 = []) :
∃ f, sys.SimFn f ∧ ∃ n m, n ≠ m ∧
(sys.simulate f a n).2 = 0 ∧ (sys.simulate f a m).2 = 0 ∧
(sys.simulate f a n).1 = (sys.simulate f a m).1 := by
  classical
  replace h := exi_simp_path_prefix_of_not_simp_path' h
  obtain ⟨xs, t, h₁, h₂, h₃⟩ := h
  haveI ht : Inhabited T := ⟨t⟩
  obtain ⟨b, hb⟩ := exi_full_trs_of_simp_path' h₂
  obtain ⟨c, hc⟩ : ∃ c, sys.tr b t = some c :=
    by
      by_contra! h₄
      rw [←Option.eq_none_iff_forall_ne_some] at h₄
      have h₅ : sys.trs a (xs ++ [t]) = (b, [t])
      · rw [trs_append]; simp [trs, hb, h₄]
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
  have hc₁ : sys.validTr b t := ⟨_, hc⟩
  use fn_set b t f, simFn_fn_set_of hc₁
  use ys.length, (xs.length + 1)
  have h₅ := hy.length_le
  use by linarith
  rw [simulate_fn_set_eq_of hc₁]
  rotate_left
  · intro k hk
    specialize h₂ (xs.take k) xs
    simp [hb] at h₂
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
  simp [simulate, hb, hc]

theorem exi_simulate_full_of_simulate_eq' {f a n r}
(hr : sys.simulate f a n = r) : ∃ k ≤ n, sys.simulate f a k = (r.1, 0) := by
  induction n generalizing a r
  · use 0; simp [←hr]
  nm n ih
  simp [simulate] at hr
  split at hr
  · nm x h₁; clear x
    simp [simulate_eq_of_tr_eq_none h₁, ←hr]
  nm x b h₁; clear x
  specialize @ih b r hr
  obtain ⟨k, hk, ih⟩ := ih
  use k + 1, by linarith
  simp_rw [simulate_succ_full']
  simpa [h₁]

theorem exi_simulate_full_of_simulate_eq {f n s s₁ r}
(h : sys.simulate f s n = (s₁, r)) : ∃ k, sys.simulate f s k = (s₁, 0) := by
  have := exi_simulate_full_of_simulate_eq' h; grind

theorem exi_simulate_full_of_simulate_fst_eq {f a n b}
(hr : (sys.simulate f a n).1 = b) : ∃ k ≤ n, sys.simulate f a k = (b, 0) := by
  generalize h₁ : sys.simulate f a n = r at hr
  obtain ⟨k, hk, h₂⟩ := exi_simulate_full_of_simulate_eq' h₁
  subst h₁
  use k, hk
  simpa [h₂]

theorem acyclic_def_sim_full_inj {a} [ha : sys.WF a] :
sys.Acyclic a ↔ ∀ f [sys.SimFn f] n m,
(sys.simulate f a n).2 = 0 → (sys.simulate f a m).2 = 0 →
(sys.simulate f a n).1 = (sys.simulate f a m).1 → n = m := by
  classical
  constructor
  · intro h₁ f hf n m
    exact sim_full_inj_of_acyclic
  intro h
  contrapose! h
  simp [acyclic_def] at h
  obtain ⟨b, h₁, c, ⟨t, hb⟩, h₂⟩ := h ha
  obtain ⟨xs, hx⟩ := exi_trs_of_reachable h₁
  obtain ⟨ys, hy⟩ := exi_trs_of_reachable h₂
  obtain ⟨zs, hz⟩ := hv # xs ++ t :: ys
  have h₃ : ¬sys.simp_path' a zs
  ·
    unfold simp_path'
    push_neg
    use xs, zs
    simp [hz]
    rw [trs_append]
    simp [trs, hx, hb, hy]
  have h₄ : (sys.trs a zs).2 = []
  ·
    simp [hz]
    subst hz
    simp_all only [forall_const, Prod.mk.injEq, and_true, exists_eq_left',
      Option.some.injEq, exists_eq']
  obtain ⟨f, hf, n, m, h₅, h₆⟩ := exi_cyclic_simulate_of_not_simp_path' h₃ h₄
  clear h₃ h₄
  use f, hf, n, m
  simpa [h₅]

theorem acyclic_iff_sim_inj {a} [sys.WF a] :
sys.Acyclic a ↔ ∀ f [sys.SimFn f] n m,
sys.simulate f a n = sys.simulate f a m → n = m := by
  rw [acyclic_def_sim_full_inj]
  symm; constructor
  · intro h f hf n m h₁ h₂ h₃
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
  · apply @ih S T sys a _ f hf m n hn.symm _ (by omega) (by omega)
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
  · use sys.dfltSimFn, inferInstance, 0
    simp [h₁]
  nm t ts ih
  simp [trs] at h₁
  split at h₁
  · nm x h₂; clear x
    use sys.dfltSimFn, inferInstance, 0
    simp [h₁]
  nm x b h₂; clear x
  have hb := acyclic_of_reachable # reachable_of_tr h₂
  specialize ih h₁
  obtain ⟨f, hf, n, h₃, h₄⟩ := ih
  have h₅ := validTr_of_eq_some h₂
  use fn_set a t f, simFn_fn_set_of h₅, n + 1
  simp_rw [simulate_succ_full']
  simp [Nat.add_one_add, h₂, h₄]
  rw [←h₃]
  apply simulate_fn_set_eq_of h₅
  clear h₅
  intro k hk h₆
  apply @ha.2 a b t (by rfl) h₂
  exact reachable_of_simulate' h₆

theorem exi_simp_path_of_trs_eq {a ts r} (h : sys.trs a ts = r) :
∃ ts', sys.simp_path a ts' r.1 :=
  exi_simp_path_of_reachable # reachable_of_trs h

theorem exi_simulate_of_trs_eq [ht : Inhabited # S → T] {a ts r} [ha : sys.WF a]
(h₁ : sys.trs a ts = r) : ∃ f, sys.SimFn f ∧
∃ n, sys.simulate f a n = (r.1, 0) := by
  obtain ⟨xs, hx⟩ := exi_simp_path_of_trs_eq h₁
  obtain ⟨f, hf, h₂⟩ := exi_simulate_of_simp_path hx
  use f, hf, xs.length
  specialize h₂ _ # by rfl
  simp at h₂
  rw [h₂, hx.2]

theorem exi_simulate_of_reachable {a b} [ha : sys.WF a]
[ht : Inhabited # S → T] (h : sys.Reachable a b) :
∃ (f : S → T), sys.SimFn f ∧ ∃ (n : ℕ), sys.simulate f a n = (b, 0) := by
  obtain ⟨xs, hx⟩ := exi_trs_of_reachable h
  exact exi_simulate_of_trs_eq hx

theorem reachable_iff_exi_simulate [hi : Inhabited # S → T] {a b} [ha : sys.WF a] :
sys.Reachable a b ↔ ∃ (f : S → T), sys.SimFn f ∧
∃ n, sys.simulate f a n = (b, 0) := by
  use exi_simulate_of_reachable
  rintro ⟨f, hf, h₁, h₂⟩
  exact reachable_of_simulate' # congrArg (·.1) h₂

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

theorem full_trs_inj_of_acyclic {a} [h : sys.Acyclic a] {xs ys}
(hx : xs <+: ys) (h₁ : (sys.trs a xs).2 = []) (h₂ : (sys.trs a ys).2 = [])
(h₃ : (sys.trs a xs).1 = (sys.trs a ys).1) : xs = ys := by
  classical
  rw [acyclic_def] at h
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
  obtain ⟨c, hc⟩ : ∃ c, sys.trs a (xs ++ [y]) = (c, [])
  · rw [trs_append_full] at h₂
    simp at h₂ ⊢
    obtain ⟨s₁, ⟨s₂, h₂, h₃⟩, h₄⟩ := h₂
    use s₁, s₂, h₂
  rw [trs_append] at h₂
  simp [hc] at h₂
  simp [h₁] at hc
  apply @h.2 b c y _ hc _
  · exact reachable_of_fst_trs # congrArg (·.1) h₁
  · exact reachable_of_fst_trs # congrArg (·.1) h₂

theorem acyclic_of_full_trs_inj {a} [ha : sys.WF a]
(h : ∀ xs ys, xs <+: ys →
(sys.trs a xs).2 = [] → (sys.trs a ys).2 = [] →
(sys.trs a xs).1 = (sys.trs a ys).1 → xs = ys) :
sys.Acyclic a := by
  classical
  rw [acyclic_def]; use ha
  intro b c t h₁ hb h₂
  obtain ⟨xs, hx⟩ := exi_trs_of_reachable h₁
  obtain ⟨ys, hy⟩ := exi_trs_of_reachable h₂
  specialize h xs (xs ++ [t] ++ ys)
  simp [hx] at h
  rw [List.append_cons, trs_append] at h
  rw [trs_append] at h
  simp [trs, hx, hb, hy] at h

theorem acyclic_def_full_trs_inj {a} [ha : sys.WF a] :
sys.Acyclic a ↔ ∀ xs ys, xs <+: ys →
(sys.trs a xs).2 = [] → (sys.trs a ys).2 = [] →
(sys.trs a xs).1 = (sys.trs a ys).1 → xs = ys := by
  classical
  use by apply full_trs_inj_of_acyclic
  exact acyclic_of_full_trs_inj

@[simp]
theorem trs_take_length_sub_eq {a xs} :
sys.trs a (xs.take (xs.length - (sys.trs a xs).2.length)) =
((sys.trs a xs).1, []) := by
  induction xs generalizing a
  · rfl
  nm x xs ih
  simp [trs]
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
  rw [acyclic_def_full_trs_inj] at h
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

theorem acyclic_of_trs_inj {a} [ha : sys.WF a]
(h : ∀ xs ys, xs <+: ys → sys.trs a xs = sys.trs a ys → xs = ys) :
sys.Acyclic a := by
  rw [acyclic_def_full_trs_inj]
  intro xs ys hx h₁ h₂ h₃
  apply h xs ys hx
  ext1; exact h₃; rwa [h₂]

theorem acyclic_def_trs_inj {a} [ha : sys.WF a] :
sys.Acyclic a ↔ ∀ xs ys, xs <+: ys → sys.trs a xs = sys.trs a ys → xs = ys :=
  ⟨by apply trs_inj_of_acyclic, acyclic_of_trs_inj⟩

theorem acyclic_of_tr {a} [ha : sys.Acyclic a] {t b}
(h₁ : sys.tr a t = some b) : sys.Acyclic b :=
  acyclic_of_reachable # reachable_of_tr h₁

theorem simulate_succ_snd_eq_zero_of_tr_and_eq_zero {f a b n}
(h₁ : (sys.simulate f b n).2 = 0) (h₂ : sys.tr a (f a) = some b) :
(sys.simulate f a # n + 1).2 = 0 := by simpa [snd_simulate_add_one_eq_zero_iff', h₂]

theorem simulate_snd_eq_zero_of_tr_and_eq_zero {f a b n}
(h₁ : (sys.simulate f b n).2 = 0) (h₂ : sys.tr a (f a) = some b) :
(sys.simulate f a n).2 = 0 := by
  have h₃ := simulate_succ_snd_eq_zero_of_tr_and_eq_zero h₁ h₂
  exact simulate_snd_eq_zero_of_le_and_eq_zero h₃ # by linarith

theorem simulate_finset_card_eq_of_acyclic
[hs : DecidableEq S] {f} [hf : sys.SimFn f] {a} [ha : sys.Acyclic a] {n}
(h₁ : (sys.simulate f a n).2 = 0) : (Finset.mkRaw # λ (k : Fin # n + 1) =>
(sys.simulate f a k).1).card = n + 1 := by
  induction n generalizing a
  · simp
  nm n ih
  simp [snd_simulate_add_one_eq_zero_iff'] at h₁
  choose b h₂ h₁ using h₁
  rw [Finset.mkRaw_fin_succ_eq_insert]
  have hb := acyclic_of_tr h₂
  have h₃ := simulate_snd_eq_zero_of_tr_and_eq_zero h₁ h₂
  rw [Finset.card_insert_of_notMem]
  · simp; exact ih h₃
  simp
  rintro ⟨k, hk⟩
  simp
  rw [Nat.lt_succ_iff] at hk
  rw [acyclic_def_sim_full_inj] at ha
  intro h₄
  specialize ha f k (n + 1)
    (simulate_snd_eq_zero_of_le_and_eq_zero h₃ hk)
  simp [snd_simulate_add_one_eq_zero_iff', h₂] at ha
  specialize ha h₁ h₄
  simp [ha] at hk

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
  have h₃ : (Finset.mkRaw # λ (k : Fin # N + 1) =>
    (sys.simulate f a k).1).card ≤ N :=
    by
      simp [←hN]
  linarith

theorem simulate_exi_snd_pos_of_finite
[h₁ : Fintype S] {s} [h₂ : Acyclic sys s] {f} [h₃ : SimFn sys f] :
∃ x N, ∀ n, N ≤ n → ∃ k, 0 < k ∧ sys.simulate f s n = (x, k) := by
  classical
  obtain ⟨N, h₄⟩ := @simulate_exi_snd_pos_of_finite' S T sys h₁ s h₂ f h₃
  obtain ⟨m, hm⟩ := hv # Nat.find! λ n => (sys.simulate f s n).2 ≠ 0
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
      rw [Nat.find!_eq]
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

@[simp]
theorem wf_fst_simulate {s f n} [hs : sys.WF s] : sys.WF (sys.simulate f s n).1 :=
  wf_of_reachable reachable_fst_simulate

instance {s f n} [hs : sys.WF s] : sys.WF (sys.simulate f s n).1 :=
  wf_fst_simulate

theorem wf_of_simulate' {s f n r} [hs : sys.WF s]
(h : sys.simulate f s n = r) : sys.WF r.1 := by
  subst r; simp

@[grind →, grind <=]
theorem wf_of_simulate {s s₁ f n r} [hs : sys.WF s]
(h : sys.simulate f s n = (s₁, r)) : sys.WF s₁ :=
  wf_of_simulate' h

theorem simulate_add_eq_left_iff {f} [hf : sys.SimFn f] {a b n m} [ha : sys.WF a] :
sys.simulate f a (n + m) = (b, n) ↔ sys.simulate f a m = (b, 0) ∧
(sys.validTr b (f b) → n = 0) := by
  constructor <;> intro h
  · rw [(by omega : m = n + m - n)]
    use simulate_sub_eq_of h
    intro h₁
    rw [Prod.ext_iff] at h
    rcases h with ⟨rfl, h⟩
    dsimp at h
    rw [←h]
    exact simulate_snd_eq_zero_of_hasTr ⟨_, h₁⟩
  rw [add_comm]
  choose h₁ h₂ using h
  have hb := wf_of_simulate h₁
  simp [simulate_add, h₁] at h₂ ⊢
  tauto

theorem simulate_add_eq_right_iff {f} [hf : sys.SimFn f] {a b n m} [ha : sys.WF a] :
sys.simulate f a (n + m) = (b, m) ↔ sys.simulate f a n = (b, 0) ∧
(sys.validTr b (f b) → m = 0) := by
  rw [add_comm]; exact simulate_add_eq_left_iff

@[simp]
theorem not_hasTr_iff {a} : ¬sys.hasTr a ↔ ∀ t, sys.tr a t = none := by
  simp [hasTr]

theorem tr_eq_none_iff_of_simFn {f a} [hf : sys.SimFn f] [ha : sys.WF a] :
sys.tr a (f a) = none ↔ ¬sys.hasTr a := by
  constructor
  · intro h₁ h₂
    obtain ⟨b, hb⟩ := hf.1 h₂
    simp [hb] at h₁
  · intro h₁
    contrapose! h₁
    rw [Option.ne_none_iff_exists'] at h₁
    rcases h₁ with ⟨b, hb⟩
    exact hasTr_of_eq_some hb

theorem false_of_tr_eq_none_and_some_of_simFn {f g a b}
[hf : sys.SimFn f] [hg : sys.SimFn g] [ha : sys.WF a]
(h₁ : sys.tr a (f a) = none) (h₂ : sys.tr a (g a) = some b) : False := by
  rw [tr_eq_none_iff_of_simFn] at h₁
  rw [←tr_eq_none_iff_of_simFn (f := g)] at h₁
  simp [h₁] at h₂

theorem tree_iff_full_trs {s} : sys.Tree s ↔ sys.WF s ∧ ∀ {ts₁ ts₂ s'},
sys.trs s ts₁ = (s', []) → sys.trs s ts₂ = (s', []) → ts₁ = ts₂ := by
  rw [tree_def]
  constructor
  · rintro ⟨hs, h⟩
    use hs
    intro ts₁ ts₂ s' h₁
    rw [←h₁, eq_comm]
    apply h
  rintro ⟨hs, h⟩
  use hs
  intro ts₁ ts₂ h₁
  generalize h₂ : sys.trs s ts₂ = r at h₁
  rcases r with ⟨s', ts'⟩
  specialize @h (ts₁.take # ts₁.length - ts'.length)
    (ts₂.take # ts₂.length - ts'.length) s'
  have h₃ := congrArg (·.2) h₁.symm
  have h₄ := congrArg (·.2) h₂.symm
  dsimp at h₃ h₄
  nth_rw 1 [h₃] at h
  nth_rw 1 [h₄] at h
  simp at h
  simp [h₁, h₂] at h
  replace h := congrArg (· ++ ts') h
  dsimp at h
  rw [List.append_take_eq_of_suffix # by simp [h₃],
    List.append_take_eq_of_suffix # by simp [h₄]] at h
  exact h

@[simp]
theorem trs_eq_self_nil_iff_of_tree {s ts} [hs : sys.Tree s] :
sys.trs s ts = (s, []) ↔ ts = [] := by
  use @hs.2 ts []; rintro rfl; rfl

theorem simulate_congr_rel {f g} {r : S → S → Prop} {a₁ a₂ n}
[hf : sys.SimFn f] [hg : sys.SimFn g] [ha₁ : sys.WF a₁] [ha₂ : sys.WF a₂]
(h₁ : r a₁ a₂) (h₂ : ∀ k < n, ∀ b₁ b₂, sys.simulate f a₁ k = (b₁, 0) →
sys.simulate g a₂ k = (b₂, 0) → r b₁ b₂ → (sys.hasTr b₁ ↔ sys.hasTr b₂) ∧
∀ c₁ c₂, sys.tr b₁ (f b₁) = some c₁ → sys.tr b₂ (g b₂) = some c₂ → r c₁ c₂) :
∃ b, r (sys.simulate f a₁ n).1 b ∧ sys.simulate g a₂ n = (b, (sys.simulate f a₁ n).2) := by
  induction n generalizing a₁ a₂; use a₂; simpa; nm n ih
  have h₄ : sys.tr a₁ (f a₁) = none ↔ sys.tr a₂ (g a₂) = none
  · specialize h₂ 0 (by simp) a₁ a₂
    simp [h₁] at h₂
    replace h₂ := h₂.1
    simp only [tr_eq_none_iff_of_simFn, h₂]
  simp [simulate]
  split
  · nm x h₃; clear x
    use a₂
    simp [h₁]
    split; rfl
    nm x b h₅; clear x
    simp [h₄, h₅] at h₃
  nm x b₁ h₃; clear x
  split
  · nm x h₅
    simp [←h₄, h₃] at h₅
  nm x b₂ h₅; clear x
  have h₆ := h₂ 0 (by simp) a₁ a₂
  simp [h₁] at h₆
  replace h₆ := h₆.2 _ _ h₃ h₅
  have hb₁ := wf_of_tr h₃
  have hb₂ := wf_of_tr h₅
  apply ih h₆
  intro k hk
  specialize h₂ (k + 1) (by linarith)
  simp_rw [simulate_succ_full'] at h₂
  simp [h₃, h₅] at h₂
  exact h₂

theorem simulate_congr_rel_full {f g} {r : S → S → Prop} {a₁ a₂ b₁ n}
[hf : sys.SimFn f] [hg : sys.SimFn g] [ha₁ : sys.WF a₁] [ha₂ : sys.WF a₂]
(h₂ : sys.simulate f a₁ n = (b₁, 0)) (h₁ : r a₁ a₂)
(h₃ : ∀ k < n, ∀ b₁ b₂ c₁, sys.simulate f a₁ k = (b₁, 0) →
sys.simulate g a₂ k = (b₂, 0) → r b₁ b₂ → sys.tr b₁ (f b₁) = some c₁ →
∃ c₂, sys.tr b₂ (g b₂) = some c₂ ∧ r c₁ c₂) :
∃ b₂, sys.simulate g a₂ n = (b₂, 0) ∧ r b₁ b₂ := by
  have h₄ := @sys.simulate_congr_rel
  specialize @h₄ f g r a₁ a₂ n _ _ _ _ h₁ _
  · intro k hk b₁ b₂ hb₁ hb₂ h₅
    specialize h₃ k hk b₁ b₂
    have h₆ : (sys.simulate f a₁ (k + 1)).2 = 0
    · apply simulate_snd_eq_zero_of_le_and_eq_zero
      rw [h₂]; linarith
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, sys.tr b₁ (f b₁) = some c₁
    · rw [simulate_add] at h₆
      simp [hb₁, snd_simulate_add_one_eq_zero_iff'] at h₆
      exact h₆
    specialize h₃ c₁ hb₁ hb₂ h₅ hc₁
    obtain ⟨c₂, hc₂, h₇⟩ := h₃
    simp [hasTr_of_eq_some hc₁, hasTr_of_eq_some hc₂]
    intro c₁' c₂' hc₁' hc₂'
    simp [hc₁] at hc₁'
    simp [hc₂] at hc₂'
    subst hc₁' hc₂'
    exact h₇
  obtain ⟨b, h₄, h₅⟩ := h₄
  simp [h₂] at h₄ ⊢
  simpa [h₂, h₅]

theorem simulate_congr_rel' {f g} {r : S → S → Prop} {a₁ a₂ n}
[hf : sys.SimFn f] [hg : sys.SimFn g] [ha₁ : sys.WF a₁] [ha₂ : sys.WF a₂]
(h₂ : (sys.simulate f a₁ n).2 = 0) (h₁ : r a₁ a₂)
(h₃ : ∀ k < n, ∀ b₁ b₂ c₁, sys.simulate f a₁ k = (b₁, 0) →
sys.simulate g a₂ k = (b₂, 0) → r b₁ b₂ → sys.tr b₁ (f b₁) = some c₁ →
∃ c₂, sys.tr b₂ (g b₂) = some c₂ ∧ r c₁ c₂) : (sys.simulate g a₂ n).2 = 0 := by
  generalize hr₁ : sys.simulate f a₁ n = r₁ at h₂
  rcases r₁ with ⟨b₁, r₁⟩
  subst h₂
  obtain ⟨b₂, h₂, h₄⟩ := simulate_congr_rel_full hr₁ h₁ h₃
  simp [h₂]

theorem simulate_congr {f g a n}
[hf : sys.SimFn f] [hg : sys.SimFn g] [ha : sys.WF a]
(h : ∀ k < n, ∀ b, sys.simulate f a k = (b, 0) →
sys.simulate g a k = (b, 0) → sys.hasTr b → f b = g b) :
sys.simulate f a n = sys.simulate g a n := by
  have h₄ := @sys.simulate_congr_rel
  specialize @h₄ f g Eq a a n _ _ _ _ rfl _
  · rintro k hk b b' hb₁ hb₂ rfl; simp; intro c₁ c₂ hc₁ hc₂
    specialize h k hk b hb₁ hb₂ # hasTr_of_eq_some hc₁
    simp [h, hc₂] at hc₁; rw [hc₁]
  obtain ⟨b, h₄, h₅⟩ := h₄; simp [h₅]; ext:1 <;> simp [h₄]

theorem not_reachable_of_acyclic_and_simulate_and_lt {a b f k n}
[ha : sys.Acyclic a] (h₁ : sys.simulate f a n = (b, 0)) (h₂ : k < n) :
¬sys.Reachable b (sys.simulate f a k).1 := by
  rcases ha with ⟨ha, h₃⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₂; clear h₂
  rw [add_assoc, add_comm n, simulate_add] at h₁
  simp at h₁
  split_ifs at h₁ with h₂ <;> simp [h₂] at h₁
  grind

theorem not_hasTr_of_snd_simulate_ne_zero {a n f r} [ha : sys.WF a] [hf : sys.SimFn f]
(h₁ : sys.simulate f a n = r) (h₂ : r.2 ≠ 0) : ¬sys.hasTr r.1 := by
  rcases r with ⟨b, r⟩
  dsimp at h₂ ⊢
  induction n generalizing a
  · simp [ne_symm' h₂] at h₁
  nm n ih
  simp [simulate] at h₁
  split at h₁
  · nm x h₃; clear x
    simp at h₁
    rcases h₁ with ⟨rfl, rfl⟩
    contrapose! h₃
    obtain ⟨c, hc⟩ := hf.1 h₃
    simp [hc]
  nm x c h₃; clear x
  have hc := sys.wf_of_tr h₃
  exact ih h₁

theorem false_of_acyclic_and_reachable_and_tr {a b t} [ha : sys.Acyclic a]
(h₁ : sys.Reachable a b) (h₂ : sys.tr b t = some a) : False := by
  rcases ha with ⟨ha, h₃⟩; exact h₃ h₁ h₂ h₁

theorem fst_simulate_ind {f s} {p : S → Prop}
(h : ∀ n s', sys.simulate f s n = (s', 0) → p s')
(n : ℕ) : p # sys.simulate f s n |>.1 := by
  rcases h₁ : sys.simulate f s n with ⟨s', r⟩
  apply h; exact simulate_sub_eq_of h₁