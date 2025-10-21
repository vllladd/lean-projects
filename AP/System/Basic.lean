import AP.System.Defs

namespace System

universe u
variable {S T : Type u} {sys : System S T}

instance : Inhabited # System S T := ⟨⟨∅, default⟩⟩

noncomputable
def dflt_simFn [Inhabited # S → T] : S → T :=
  by classical exact
  λ s => if h : sys.hasTr s then h.choose else (default : S → T) s

@[simp] instance [Inhabited # S → T] : sys.SimFn sys.dflt_simFn := by
  constructor
  intro s hs h₁
  unfold dflt_simFn
  split_ifs
  exact h₁.choose_spec

noncomputable
def mk_simFn (f : S → T) : S → T := by
  classical
  intro s
  by_cases h : sys.validTr s # f s
  · exact f s
  haveI : Inhabited # S → T := ⟨λ _ => f s⟩
  use sys.dflt_simFn s

theorem validTr_of_simFn_and_hasTr {f} [hf : sys.SimFn f] {s} [hs : sys.WF s]
(h : sys.hasTr s) : sys.validTr s (f s) := hf.h h

@[simp] instance {f} : sys.SimFn # sys.mk_simFn f := by
  constructor
  intro s hs h₁
  unfold mk_simFn
  split_ifs with h₂
  · exact h₂
  exact validTr_of_simFn_and_hasTr h₁

@[simp, refl]
theorem Reachable.refl' {a} : sys.Reachable a a :=
  Reachable.refl

@[trans]
theorem Reachable.trans {a b c}
(h₁ : sys.Reachable a b) (h₂ : sys.Reachable b c) : sys.Reachable a c := by
  induction h₁; exact h₂
  nm x y z t h₁ h₃ ih
  exact Reachable.step h₁ # ih h₂

theorem validTr_of_eq_some {s t s₁}
(h : sys.tr s t = some s₁) : sys.validTr s t := ⟨_, h⟩

theorem hasTr_of_eq_some {s t s₁}
(h : sys.tr s t = some s₁) : sys.hasTr s := ⟨_, validTr_of_eq_some h⟩

theorem reachable_of_simulate
{f} {s₁ s₂ n} (h : (sys.simulate f s₁ n).1 = s₂) :
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

theorem reachable_of_simulate_eq {f} {s₁ s₂ n r}
(h : sys.simulate f s₁ n = (s₂, r)) : sys.Reachable s₁ s₂ :=
  reachable_of_simulate # Prod.fst_eq_of_eq_mk h |>.symm

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

theorem hasTr_of_reachable_and_ne {s₁ s₂}
(h₁ : sys.Reachable s₁ s₂) (h₂ : s₁ ≠ s₂) : sys.hasTr s₁ := by
  cases h₁; simp at h₂
  apply hasTr_of_eq_some <;> assumption

theorem eq_of_reachable_and_not_hasTr {s₁ s₂}
(h₁ : sys.Reachable s₁ s₂) (h₂ : ¬sys.hasTr s₁) : s₁ = s₂ := by
  contrapose! h₂; exact hasTr_of_reachable_and_ne h₁ h₂

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

theorem reachable_of_trs {a ts r} (h : sys.trs a ts = r) :
sys.Reachable a r.1 := by
  rcases r with ⟨b, rs⟩
  replace h := congrArg (·.1) h
  dsimp at h ⊢
  induction ts generalizing a b <;> simp at h
  · rw [h]
  nm t ts ih
  split at h
  · simp at h
    rw [h]
  nm m c h₁
  apply reachable_left h₁
  apply ih
  exact h

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

theorem reachable_iff_exi_trs {a b} :
sys.Reachable a b ↔ ∃ ts, sys.trs a ts = (b, []) := by
  use exi_trs_of_reachable
  rintro ⟨ts, h⟩
  exact reachable_of_trs h

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
  have h₅ := reachable_of_trs h₃
  apply @h₂ a (sys.trs a ts).1 b t
  · simp at h₃
    split at h₃ <;> simp at h₃
    nm m s h₆
    rwa [←h₃]
  · apply ih
    ext1; rfl
    simpa
  · simp

@[simp]
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

@[simp]
theorem simulate_sub_simulate_snd_eq {f s n} :
sys.simulate f s (n - (sys.simulate f s n).2) = ((sys.simulate f s n).1, 0) := by
  induction n generalizing s
  · rfl
  nm n ih
  simp
  split; simp
  nm x s₁ h₁; clear x
  rw [Nat.add_one_sub simulate_snd_le]
  simp [h₁]
  exact ih

theorem simFn_def {f} : sys.SimFn f ↔ ∀ {s} [sys.WF s],
sys.hasTr s → sys.validTr s (f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem acyclic_def {s} : sys.Acyclic s ↔ sys.WF s ∧
∀ {a b t}, sys.Reachable s a → sys.tr a t = some b → ¬sys.Reachable b a :=
  ⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

theorem tree_def {s} : sys.Tree s ↔ sys.WF s ∧
∀ {ts₁ ts₂}, sys.trs s ts₁ = sys.trs s ts₂ → ts₁ = ts₂ :=
  ⟨λ h => ⟨h.1, h.2⟩, λ h => ⟨h.1, h.2⟩⟩

theorem wf_def {b} : sys.WF b ↔ ∃ a, sys.Initial a ∧ sys.Reachable a b := by
  constructor
  · rintro ⟨h⟩; exact h
  · rintro ⟨a, ha, hb⟩; constructor; use a

theorem wf_of_initial {s} [sys.Initial s] : sys.WF s := by
  constructor; use s

@[simp] instance {s} [sys.Initial s] : sys.WF s := wf_of_initial

theorem wf_of_reachable {a b}
[ha : sys.WF a] (hb : sys.Reachable a b) : sys.WF b := by
  rw [wf_def] at ha
  obtain ⟨c, h₁, h₂⟩ := ha
  constructor; use c, h₁, h₂.trans hb

theorem initial_def {a} : sys.Initial a ↔ a ∈ sys.initial :=
  ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem validTr_iff_isSome {s t} : sys.validTr s t ↔ (sys.tr s t).isSome := by
  simp_rw [validTr, Option.isSome_iff_exists]

theorem hasTr_iff {s} : sys.hasTr s ↔ ∃ t s', sys.tr s t = some s' := by rfl

instance {s t} : Decidable (sys.validTr s t) :=
  match h : sys.tr s t with
  | none => .isFalse # by simp [validTr_iff_isSome, h]
  | some _ => .isTrue # by simp [validTr_iff_isSome, h]

theorem reachable_of_fst_trs {a ts b} (h : (sys.trs a ts).1 = b) :
sys.Reachable a b := by subst h; exact reachable_of_trs rfl

theorem wf_of_tr {a b t} [ha : sys.WF a] (h : sys.tr a t = some b) : sys.WF b :=
  wf_of_reachable # reachable_of_tr h

theorem wf_of_trs {a b ts r} [ha : sys.WF a] (h : sys.trs a ts = (b, r)) : sys.WF b :=
  wf_of_reachable # reachable_of_trs h

theorem wf_of_acyclic {a} [ha : sys.Acyclic a] : sys.WF a := by
  rw [acyclic_def] at ha; exact ha.1

theorem wf_of_tree {a} [ha : sys.Tree a] : sys.WF a := by
  rw [tree_def] at ha; exact ha.1

instance {a} [ha : sys.Acyclic a] : sys.WF a := wf_of_acyclic
instance {a} [ha : sys.Tree a] : sys.WF a := wf_of_tree

theorem simulate_eq_of_not_hasTr {f s n}
(h : ¬sys.hasTr s) : sys.simulate f s n = (s, n) := by
  cases n; rfl; nm n
  simp
  split; rfl
  nm x s' h₁; clear x
  exfalso
  apply h
  exact ⟨_, _, h₁⟩

class WFTrans (sys : System S T) (t : T) : Prop where
  h : ∃ s, sys.WF s ∧ sys.validTr s t

theorem WFTrans_def {t} : sys.WFTrans t ↔ ∃ s, sys.WF s ∧ sys.validTr s t := by
  use (·.1), (⟨·⟩)

theorem wfTrans_of_validTr {s t} [hs : sys.WF s]
(h : sys.validTr s t) : sys.WFTrans t := by use s

theorem wfTrans_of_tr {s s' t} [hs : sys.WF s]
(h : sys.tr s t = some s') : sys.WFTrans t := by use s, hs, s'

theorem simulate_snd_le_of_eq {f s s' r n} (h : sys.simulate f s n = (s', r)) : r ≤ n := by
  simp [Prod.snd_eq_of_eq_mk h]

theorem simulate_snd_ne_zero_of {f s s' r n m} (h : sys.simulate f s n = (s', r))
(hr : r ≠ 0) (hm : n ≤ m) : (sys.simulate f s m).2 ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm; rw [simulate_add, h]; simp [hr]