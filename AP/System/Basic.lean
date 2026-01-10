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

@[simp]
theorem trs_empty {s} : sys.trs s [] = (s, []) := rfl

@[simp]
theorem simulate_zero {f s} : sys.simulate f s 0 = (s, 0) := rfl

theorem reachable_of_trs {a ts r} (h : sys.trs a ts = r) :
sys.Reachable a r.1 := by
  rcases r with ⟨b, rs⟩
  replace h := congrArg (·.1) h
  dsimp at h ⊢
  induction ts generalizing a b
  · simp at h
    rw [h]
  nm t ts ih
  simp [trs] at h
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
  simpa [trs, h₁]

theorem reachable_iff_exi_trs {a b} :
sys.Reachable a b ↔ ∃ ts, sys.trs a ts = (b, []) := by
  use exi_trs_of_reachable
  rintro ⟨ts, h⟩
  exact reachable_of_trs h

theorem trs_append {s xs ys} : sys.trs s (xs ++ ys) =
let ⟨s₁, xs'⟩ := sys.trs s xs
let (s₂, ys') := sys.trs s₁ ys
if xs' ≠ [] then (s₁, xs' ++ ys) else (s₂, xs' ++ ys') := by
  dsimp
  induction xs generalizing s
  · simp
  nm x xs ih
  simp [trs]
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
  simp [trs]
  split
  · exact h
  nm m c h₁
  exact ih # reachable_right h h₁

@[simp]
theorem reachable_trs {s ts} : sys.Reachable s (sys.trs s ts).1 := by
  apply reachable_trs_aux; rfl

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

@[simp]
theorem simulate_add_full {f s s₂ n m} : sys.simulate f s (n + m) = (s₂, 0) ↔
∃ s₁, sys.simulate f s n = (s₁, 0) ∧ sys.simulate f s₁ m = (s₂, 0) := by
  rw [simulate_add]
  simp_all only [ne_eq, ite_not, zero_add, Prod.mk.eta]
  apply Iff.intro
  · intro a
    split at a
    rename_i h
    apply Exists.intro
    apply And.intro
    ext : 1
    on_goal 5 => rename_i h
    on_goal 3 => exact a
    · simp_all only
    · simp_all only
    simp_all only [Prod.mk.injEq, Nat.add_eq_zero_iff, false_and, and_false]
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    simp_all only [↓reduceIte]

@[simp]
theorem trs_append_full {s s₂ ts₁ ts₂} : sys.trs s (ts₁ ++ ts₂) = (s₂, []) ↔
∃ s₁, sys.trs s ts₁ = (s₁, []) ∧ sys.trs s₁ ts₂ = (s₂, []) := by
  classical
  rw [trs_append]
  simp_all only [ne_eq, ite_not, List.nil_append, Prod.mk.eta]
  apply Iff.intro
  · intro a
    split at a
    rename_i h
    apply Exists.intro
    apply And.intro
    ext : 1
    on_goal 5 => rename_i h
    on_goal 3 => exact a
    · simp_all only
    · ext i a_1 : 2
      simp_all only [List.length_nil, not_lt_zero', not_false_eq_true, getElem?_neg, reduceCtorEq]
    simp_all only [Prod.mk.injEq, List.append_eq_nil_iff, false_and, and_false]
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    simp_all only [↓reduceIte]

@[simp]
theorem trs_cons_full {s s₂ t ts} : sys.trs s (t :: ts) = (s₂, []) ↔
∃ s₁, sys.tr s t = some s₁ ∧ sys.trs s₁ ts = (s₂, []) := by
  simp [trs]
  apply Iff.intro
  · intro a
    split at a
    next x heq => simp_all only [Prod.mk.injEq, reduceCtorEq, and_false]
    next x s₁ heq => simp_all only [Option.some.injEq, exists_eq_left']
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    simp_all only

@[simp]
theorem trs_snoc_full {s s₂ t ts} : sys.trs s (ts ++ [t]) = (s₂, []) ↔
∃ s₁, sys.trs s ts = (s₁, []) ∧ sys.tr s₁ t = some s₂ := by
  simp [trs]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    simp_all only [Prod.mk.injEq, and_true, exists_eq_left']
    split at right
    next x heq => simp_all only [Prod.mk.injEq, List.cons_ne_self, and_false]
    next x s₁ heq => simp_all only [Prod.mk.injEq, and_true]
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    simp_all only [Prod.mk.injEq, and_true, exists_eq_left']

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
  simp at h₃
  choose s₁ h₃ h₄ using h₃
  have h₅ := reachable_of_trs h₃
  apply h₂ h₅ h₄ # ih h₅ h₃

@[simp]
theorem simulate_snd_le {f s n} : (sys.simulate f s n).2 ≤ n := by
  induction n generalizing s
  · rfl
  nm n ih
  simp [simulate]
  split
  · rfl
  nm m s₁ h₁
  specialize @ih s₁
  linarith

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
  simp [simulate]
  split; simp
  nm x s₁ h₁; clear x
  rw [Nat.add_one_sub simulate_snd_le]
  simp [simulate, h₁]
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
  simp [simulate]
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

@[simp]
theorem snd_simulate_add_eq_zero_iff {f s n m} : (sys.simulate f s (n + m)).2 = 0 ↔
∃ s₁ s₂, sys.simulate f s n = (s₁, 0) ∧ sys.simulate f s₁ m = (s₂, 0) := by
  simp [simulate_add]
  simp_all only [zero_add, Prod.mk.eta]
  apply Iff.intro
  · intro a
    split at a
    rename_i h
    apply Exists.intro
    apply And.intro
    ext : 1
    on_goal 5 => rename_i h
    on_goal 3 => {
      apply Exists.intro
      · ext : 1
        · simp_all only
          rfl
        · simp_all only
          exact a
    }
    · simp_all only
    · simp_all only
    simp_all only [Nat.add_eq_zero_iff, false_and]
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    simp_all only [↓reduceIte]

@[simp]
theorem snd_trs_append_eq_nil_iff {s ts₁ ts₂} : (sys.trs s (ts₁ ++ ts₂)).2 = [] ↔
∃ s₁ s₂, sys.trs s ts₁ = (s₁, []) ∧ sys.trs s₁ ts₂ = (s₂, []) := by
  classical
  simp [trs_append, Prod.ext_iff]
  simp_all only [List.nil_append, Prod.mk.eta]
  apply Iff.intro
  · intro a
    apply And.intro
    · split at a
      next h => simp_all only
      next h => simp_all only [List.append_eq_nil_iff, false_and]
    · split at a
      next h => simp_all only
      next h => simp_all only [List.append_eq_nil_iff, false_and]
  · intro a
    simp_all only [↓reduceIte]

@[simp]
theorem snd_trs_cons_eq_nil_iff {s t ts} : (sys.trs s (t :: ts)).2 = [] ↔
∃ s₁, sys.tr s t = some s₁ ∧ (sys.trs s₁ ts).2 = [] := by
  classical
  simp [trs]
  apply Iff.intro
  · intro a
    split at a
    next x heq => simp_all only [reduceCtorEq]
    next x s₁ heq => simp_all only [Option.some.injEq, exists_eq_left']
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    simp_all only

@[simp]
theorem snd_trs_snoc_eq_nil_iff {s t ts} : (sys.trs s (ts ++ [t])).2 = [] ↔
∃ s₁ s₂, sys.trs s ts = (s₁, []) ∧ sys.tr s₁ t = some s₂ := by
  simp [trs]
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    simp_all only [Prod.mk.injEq, and_true, exists_eq_left']
    split at h
    next x heq => simp_all only [Prod.mk.injEq, List.cons_ne_self, and_false]
    next x s₁ heq => simp_all only [Prod.mk.injEq, and_true, Option.some.injEq, exists_eq']
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    simp_all only [Prod.mk.injEq, and_true, exists_eq_left', exists_eq']

theorem simulate_succ_full' {f s s₂ n} : sys.simulate f s n.succ = (s₂, 0) ↔
∃ s₁, sys.tr s (f s) = some s₁ ∧ sys.simulate f s₁ n = (s₂, 0) := by
  simp [simulate]; split
  · simp_all only [Prod.mk.injEq, Nat.add_eq_zero_iff, one_ne_zero, and_false, reduceCtorEq,
      false_and, exists_false]
  · simp_all only [Option.some.injEq, exists_eq_left']

@[simp high]
theorem simulate_succ_full {f s s₂ n} : sys.simulate f s n.succ = (s₂, 0) ↔
∃ s₁, sys.simulate f s n = (s₁, 0) ∧ sys.tr s₁ (f s₁) = some s₂ := by
  rw [Nat.succ_eq_add_one, simulate_add_full]; simp [simulate_succ_full']

theorem simulate_add_one_full' {f s s₂ n} : sys.simulate f s (n + 1) = (s₂, 0) ↔
∃ s₁, sys.tr s (f s) = some s₁ ∧ sys.simulate f s₁ n = (s₂, 0) :=
  simulate_succ_full'

@[simp high]
theorem simulate_add_one_full {f s s₂ n} : sys.simulate f s (n + 1) = (s₂, 0) ↔
∃ s₁, sys.simulate f s n = (s₁, 0) ∧ sys.tr s₁ (f s₁) = some s₂ :=
  simulate_succ_full

@[simp]
theorem simulate_one_of_snd_succ {f s s' r} :
sys.simulate f s 1 = (s', r.succ) ↔ sys.tr s (f s) = none ∧ s = s' ∧ r = 0 := by
  simp [simulate]
  apply Iff.intro
  · intro a
    apply And.intro
    · split at a
      next x heq => simp_all only [Prod.mk.injEq, Nat.right_eq_add]
      next x s₁ heq => simp_all only [Prod.mk.injEq, Nat.right_eq_add, Nat.add_eq_zero_iff,
        one_ne_zero, and_false]
    · apply And.intro
      · split at a
        next x heq => simp_all only [Prod.mk.injEq, Nat.right_eq_add]
        next x s₁ heq => simp_all only [Prod.mk.injEq, Nat.right_eq_add, Nat.add_eq_zero_iff,
          one_ne_zero, and_false]
      · split at a
        next x heq => simp_all only [Prod.mk.injEq, Nat.right_eq_add]
        next x s₁ heq => simp_all only [Prod.mk.injEq, Nat.right_eq_add, Nat.add_eq_zero_iff,
          one_ne_zero, and_false]
  · intro a
    simp_all only [zero_add]
    obtain ⟨left, right⟩ := a
    obtain ⟨left_1, right⟩ := right
    subst right left_1
    simp_all only

theorem simulate_one_of_snd_add_one {f s s' r} :
sys.simulate f s 1 = (s', r + 1) ↔ sys.tr s (f s) = none ∧ s = s' ∧ r = 0 :=
  simulate_one_of_snd_succ

theorem snd_simulate_add_one_eq_zero_iff' {f s n} : (sys.simulate f s (n + 1)).2 = 0 ↔
∃ s₁, sys.tr s (f s) = some s₁ ∧ (sys.simulate f s₁ n).2 = 0 := by
  simp [add_comm n 1, Prod.ext_iff]

@[simp]
theorem simulate_eq_snd_add_right_iff {f s s' n r} :
sys.simulate f s n = (s', n + r) ↔ r = 0 ∧ s = s' ∧ (n = 0 ∨ sys.tr s (f s) = none) := by
  cases n
  · simp; tauto
  nm n
  simp [simulate]
  split
  · simp; tauto
  nm x s₁ h; clear x
  simp [h]
  intro h₁
  linarith [simulate_snd_le_of_eq h₁]

@[simp]
theorem simulate_eq_snd_add_left_iff {f s s' n r} :
sys.simulate f s n = (s', r + n) ↔ r = 0 ∧ s = s' ∧ (n = 0 ∨ sys.tr s (f s) = none) := by
  simp [add_comm r n]

@[simp]
theorem simulate_eq_same_iff {f s s' n} :
sys.simulate f s n = (s', n) ↔ s = s' ∧ (n = 0 ∨ sys.tr s (f s) = none) := by
  nth_rw 2 [show n = n + 0 by rfl]; rw [simulate_eq_snd_add_right_iff]; simp

@[simp]
theorem tr_simFn_eq_none_iff {f s} [hs : sys.WF s] [hf : sys.SimFn f] :
sys.tr s (f s) = none ↔ ¬sys.hasTr s := by
  constructor
  · intro h₁ h₂
    obtain ⟨s', h₃⟩ := hf.1 h₂
    simp [h₁] at h₃
  · rw [imp_iff_not']
    simp [Option.ne_none_iff_exists']
    intro s' h₁
    use f s, s'

theorem tr_eq_none_of_simulate_eq {f s s' n r}
(h : sys.simulate f s n = (s', r + 1)) : sys.tr s' (f s') = none := by
  induction n generalizing s
  · simp at h
  nm n ih
  by_contra! h₁
  replace h₁ := Option.exists_eq_some_of_ne_none h₁
  choose s₁ h₁ using h₁
  simp [simulate] at h
  split at h
  · nm x h₂; clear x
    simp at h
    rcases h with ⟨rfl, rfl⟩
    simp [h₁] at h₂
  nm x s₂ h₂; clear x
  specialize ih h
  simp [ih] at h₁