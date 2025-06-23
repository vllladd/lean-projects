import AP.System.Defs

namespace System

variable {S T} {sys : System S T}

noncomputable
def dflt_sim_fn [Inhabited # S → T] : S → T :=
  by classical exact
  λ s => if h : sys.has_tr s then h.choose else (default : S → T) s

instance [Inhabited # S → T] : sys.SimFn sys.dflt_sim_fn := by
  constructor
  intro s h₁
  unfold dflt_sim_fn
  split_ifs
  exact h₁.choose_spec

noncomputable
def mk_sim_fn (f : S → T) : S → T := by
  classical
  intro s
  by_cases h : sys.valid_tr s # f s
  · exact f s
  haveI : Inhabited # S → T := ⟨λ _ => f s⟩
  use sys.dflt_sim_fn s

theorem valid_tr_of_sim_fn_and_has_tr {f} [hf : sys.SimFn f] {s}
(h : sys.has_tr s) : sys.valid_tr s (f s) := hf.h h

instance {f} : sys.SimFn # sys.mk_sim_fn f := by
  constructor
  intro s h₁
  unfold mk_sim_fn
  split_ifs with h₂
  · exact h₂
  exact valid_tr_of_sim_fn_and_has_tr h₁

@[simp, refl]
theorem Reachable.refl' {a} : sys.Reachable a a :=
  Reachable.refl

@[trans]
theorem Reachable.trans {a b c}
(h₁ : sys.Reachable a b) (h₂ : sys.Reachable b c) : sys.Reachable a c := by
  induction h₁; exact h₂
  nm x y z t h₁ h₃ ih
  exact Reachable.step h₁ # ih h₂

theorem valid_tr_of_eq_some {s t s₁}
(h : sys.tr s t = some s₁) : sys.valid_tr s t := ⟨_, h⟩

theorem has_tr_of_eq_some {s t s₁}
(h : sys.tr s t = some s₁) : sys.has_tr s := ⟨_, valid_tr_of_eq_some h⟩

theorem reachable_of_simulate'
{f} {s₁ s₂ n} (h : s₂ = (sys.simulate f s₁ n).1) :
sys.Reachable s₁ s₂ := by
  induction n generalizing s₁ s₂
  · subst h; rfl
  nm n ih
  unfold simulate at h
  split at h
  · nm m h₁
    dsimp at h
    subst h
    rfl
  nm m s h₁
  trans s
  · apply Reachable.step h₁; rfl
  exact ih h

theorem reachable_of_simulate
{f} {s₁ s₂ n} (h : (sys.simulate f s₁ n).1 = s₂) :
sys.Reachable s₁ s₂ := reachable_of_simulate' h.symm

theorem reachable_of_simulate_full
{f} {s₁ s₂ n} (h : sys.simulate f s₁ n = (s₂, 0)) :
sys.Reachable s₁ s₂ := by
  replace h := congrArg (·.1) h
  exact reachable_of_simulate h

theorem reachable_left {a b c t}
(h₁ : sys.tr a t = some b) (h₂ : sys.Reachable b c) : sys.Reachable a c :=
  Reachable.step h₁ h₂

theorem reachable_right {a b c t}
(h₁ : sys.Reachable a b) (h₂ : sys.tr b t = some c) : sys.Reachable a c := by
  induction h₁ generalizing c t
  · nm x
    apply reachable_left h₂
    rfl
  clear a b
  nm a b x t₁ h₁ h₃ ih
  trans b
  · apply reachable_left h₁
    rfl
  exact ih h₂

theorem reachable_of_tr {a b t}
(h : sys.tr a t = some b) : sys.Reachable a b := by
  apply reachable_left h; rfl

theorem has_tr_of_reachable_and_ne {s₁ s₂}
(h₁ : sys.Reachable s₁ s₂) (h₂ : s₁ ≠ s₂) : sys.has_tr s₁ := by
  cases h₁; simp at h₂
  apply has_tr_of_eq_some <;> assumption

theorem eq_of_reachable_and_not_has_tr {s₁ s₂}
(h₁ : sys.Reachable s₁ s₂) (h₂ : ¬sys.has_tr s₁) : s₁ = s₂ := by
  contrapose! h₂; exact has_tr_of_reachable_and_ne h₁ h₂

theorem exi_tr_right_of_reachable_and_ne {a b}
(h₁ : sys.Reachable a b) (h₂ : a ≠ b) :
∃ c t, sys.Reachable a c ∧ sys.tr c t = some b := by
  contrapose! h₂
  induction h₁; rfl
  clear a b
  nm a b c t h₁ h₃ ih
  specialize ih _
  · intro x t₁ h₄
    apply h₂
    exact reachable_left h₁ h₄
  subst ih
  specialize h₂ a t
  reduce at h₁
  simp [h₁] at h₂

theorem reachable_ind_left {P : ∀ a b, sys.Reachable a b → Prop}
(h₁ : ∀ {a}, P a a # by rfl)
(h₂ : ∀ {a b c t}, (hx : sys.tr a t = some b) →
  (hy : sys.Reachable b c) → P b c hy → P a c (Reachable.step hx hy))
{a b} (h : sys.Reachable a b) : P a b h := by
  induction h; exact h₁; apply h₂ <;> assumption

theorem reachable_of_trs {a b ts} (h : (sys.trs a ts).1 = b) :
sys.Reachable a b := by
  induction ts generalizing a b <;> simp at h
  · rw [h]
  nm t ts ih
  split at h
  · simp at h
    rw [h]
  nm m c h₁
  exact reachable_left h₁ # ih h

theorem exi_trs_of_reachable {a b} (h : sys.Reachable a b) :
∃ ts, sys.trs a ts = (b, []) := by
  induction h
  · nm c
    use []
    rfl
  clear a b
  nm a b c t h₁ h₂ ih
  obtain ⟨ts, ih⟩ := ih
  use t :: ts
  reduce at h₁
  simpa [h₁]

theorem exi_trs_nil_of_trs {a b ts} (h : (sys.trs a ts).1 = b) :
∃ ts', sys.trs a ts' = (b, []) := by
  induction ts generalizing a
  · simp at h
    subst h
    use []
    rfl
  nm t ts ih
  simp at h
  split at h
  · nm m h₁
    simp at h
    subst h
    use []
    rfl
  nm m c h₁
  obtain ⟨ts', ih⟩ := ih h
  use t :: ts'
  simpa [h₁]

theorem reachable_of_trs' {a b ts} (h : sys.trs a ts = (b, [])) :
sys.Reachable a b := reachable_of_trs # congrArg (·.1) h

theorem reachable_iff_exi_trs {a b} :
sys.Reachable a b ↔ ∃ ts, sys.trs a ts = (b, []) := by
  use exi_trs_of_reachable
  rintro ⟨ts, h⟩
  exact reachable_of_trs' h

theorem trs_append {s xs ys} [hi : DecidableEq T] :
sys.trs s (xs ++ ys) =
let ⟨s₁, xs'⟩ := sys.trs s xs
let (s₂, ys') := sys.trs s₁ ys
if xs' ≠ [] then (s₁, xs' ++ ys) else (s₂, xs' ++ ys') := by
  dsimp
  induction xs generalizing s
  · simp
  nm x xs ih
  simp
  split
  · simp at ih ⊢
  nm m c h₁
  specialize @ih c
  simp [ih]

theorem reachable_trs_aux {a b ts} (h : sys.Reachable a b) :
sys.Reachable a (sys.trs b ts).1 := by
  induction ts generalizing b
  · exact h
  nm t ts ih
  simp
  split
  · exact h
  nm m c h₁
  exact ih # reachable_right h h₁

@[simp]
theorem reachable_trs {s ts} : sys.Reachable s (sys.trs s ts).1 := by
  apply reachable_trs_aux; rfl

theorem reachable_ind_right {P : ∀ a b, sys.Reachable a b → Prop}
(h₁ : ∀ {a}, P a a # by rfl)
(h₂ : ∀ {a b c t}, (hx : sys.Reachable a b) →
  (hy : sys.tr b t = some c) → P a b hx → P a c (reachable_right hx hy))
{a b} (h : sys.Reachable a b) : P a b h := by
  classical
  obtain ⟨ts, h₃⟩ := exi_trs_of_reachable h
  induction ts using List.reverseRecOn generalizing a b
  · simp at h₃
    simp [h₃]
    exact h₁
  nm ts t ih
  simp only [trs_append] at h₃
  split_ifs at h₃ with h₄
  · simp at h₃
  simp at h₄
  simp only [h₄, List.nil_append, Prod.mk.eta] at h₃
  have h₅ := reachable_of_trs' h₃
  apply @h₂ a (sys.trs a ts).1 b t
  · simp at h₃
    split at h₃ <;> simp at h₃
    nm m s h₆
    rwa [←h₃]
  · apply ih
    ext1; rfl
    simpa
  · simp

theorem simulate_snd_le {f s n} : (sys.simulate f s n).2 ≤ n := by
  induction n generalizing s
  · rfl
  nm n ih
  simp
  split
  · rfl
  nm m s₁ h₁
  specialize @ih s₁
  linarith

theorem simulate_add {f s n m} :
sys.simulate f s (n + m) =
let ⟨s₁, n'⟩ := sys.simulate f s n
let (s₂, m') := sys.simulate f s₁ m
if n' ≠ 0 then (s₁, n' + m) else (s₂, n' + m') := by
  induction n generalizing s
  · simp
  nm n ih
  rw [Nat.add_one_add]
  simp only [System.simulate]
  split; simp [Nat.add_one_add]
  exact ih

theorem simulate_snd_mono {f s n m} (h : n ≤ m) :
(sys.simulate f s n).2 ≤ (sys.simulate f s m).2 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  simp [simulate_add]
  split_ifs with h₁ <;> simp [h₁]

theorem simulate_sub_simulate_snd_snd {f s n} :
(sys.simulate f s (n - (sys.simulate f s n).2)).2 = 0 := by
  induction n generalizing s
  · rfl
  nm n ih
  simp
  split
  · nm x h₁
    simp [h₁]
  nm x s₁ h₁; clear x
  rw [Nat.add_one_sub simulate_snd_le]
  simp [h₁]
  exact ih

theorem sim_fn_iff {f} : sys.SimFn f ↔ ∀ {s}, sys.has_tr s → sys.valid_tr s (f s) :=
  ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

@[simp]
theorem acyclic_iff {s} : sys.Acyclic s ↔
∀ {a b t}, sys.Reachable s a → sys.tr_to a t b → ¬sys.Reachable b a :=
  ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

@[simp]
theorem tree_iff {s} : sys.Tree s ↔
∀ {ts₁ ts₂}, sys.trs s ts₁ = sys.trs s ts₂ → ts₁ = ts₂ :=
  ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩