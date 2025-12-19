import AP.AP.WF

namespace List

variable {α β : Type*}
variable {xs ys zs : List α}

theorem nodup_of_sorted_lt [ha : LinearOrder α] (h : xs.Sorted (· < ·)) : xs.Nodup := by
  induction h
  · simp
  clear! xs; nm x xs h₁ h₂ ih
  simp [ih]
  intro hx
  specialize h₁ x hx
  simp at h₁

theorem foldl_apply_comm {f : β → α → β} {z x}
(h : ∀ ⦃x y z⦄, f (f x y) z = f (f x z) y) :
xs.foldl f (f z x) = f (xs.foldl f z) x := by
  induction xs generalizing z; simp; nm y xs ih; simp; rw [←ih, h]

-- #check 0 #exit

end List

namespace Set

variable {α β : Type*}
variable {s s₁ s₂ : Set α}

open Classical in noncomputable
def ncard? (s : Set α) : Option ℕ :=
  if s.Finite then some s.ncard else none

def filter (s : Set α) (p : α → Prop) : Set α :=
  {x ∈ s | p x}

@[simp]
theorem mem_filter {p x} : x ∈ s.filter p ↔ x ∈ s ∧ p x := by
  simp [filter]

@[simp]
theorem filter_const_true : s.filter (λ _ => True) = s := by
  simp [filter]

@[simp]
theorem filter_const_false : s.filter (λ _ => False) = ∅ := by
  simp [filter]

@[simp]
theorem ncard?_empty : (∅ : Set α).ncard? = some 0 := by
  simp [ncard?]

theorem ncard?_image_of_injOn {f : α → β} (h : s.InjOn f) : (f '' s).ncard? = s.ncard? := by
  unfold ncard?; rw [finite_image_iff h]
  split_ifs with h₁; on_goal 2 => rfl
  simpa [ncard_image_eq_iff_injOn h₁]

theorem filter_fn_mem : s.filter (· ∈ s₁) = s ∩ s₁ := by
  simp [filter]

theorem forall_not_mem_iff : (∀ x, x ∉ s) ↔ s = ∅ := by
  grind

@[simp]
theorem not_finite_iff_infinite : ¬s.Finite ↔ s.Infinite := by
  rfl

theorem exi_mem_of_infinite (h : s.Infinite) : ∃ x, x ∈ s := by
  contrapose! h; rw [forall_not_mem_iff] at h; simp [h]

theorem exi_min [ha : LinearOrder α]
(h₁ : s.Finite) (h₂ : s.Nonempty) : ∃ x ∈ s, ∀ y ∈ s, x ≤ y :=
  exists_min_image _ id h₁ h₂

theorem exi_max [ha : LinearOrder α]
(h₁ : s.Finite) (h₂ : s.Nonempty) : ∃ x ∈ s, ∀ y ∈ s, y ≤ x :=
  exists_max_image _ id h₁ h₂

-- #check 0 #exit

end Set

section Order

variable {α : Type*}
variable [ha : LinearOrder α]

@[simp]
theorem le_trans_simp {a b c : α} : (a ≤ b → b ≤ c → a ≤ c) = True := by
  simp; exact le_trans

@[simp]
theorem le_total_simp {a b : α} : (a ≤ b ∨ b ≤ a) = True := by
  simp; apply le_total

@[simp]
theorem le_antisymm_simp {a b : α} : (a ≤ b → b ≤ a → a = b) = True := by
  simp; apply le_antisymm

-- #check 0 #exit

end Order

namespace Set'

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable [hb₁ : DecidableEq β] [hb₂ : Hashable β]
variable [hc₁ : DecidableEq γ] [hc₂ : Hashable γ]
variable {s s' s₁ s₂ s₃ : Set' α}

def toFinset (s : Set' α) : Finset α :=
  s.fold (λ s₁ x => insert x s₁) ∅ # by grind

@[simp]
theorem toFinset_empty : (∅ : Set' α).toFinset = ∅ := by
  simp [toFinset]

theorem mem_toFinset_of_mem {x} (hx : x ∈ s) : x ∈ s.toFinset := by
  classical
  unfold toFinset
  rw [fold_eq_foldl_toList]
  rw [←mem_toList] at hx
  generalize s.toList = xs at hx ⊢; clear! s
  induction xs using List.reverseRecOn <;> grind

@[simp]
theorem ofList_cons {xs : List α} {x} : ofList (x :: xs) = (ofList xs).insert x := by
  ext; simp

@[simp]
theorem ofList_append {xs ys : List α} : ofList (xs ++ ys) = ofList xs ∪ ofList ys := by
  ext; simp

theorem ind_ofList' [ha : LinearOrder α] {p : Set' α → Prop}
(h : ∀ (xs : List α), xs.Sorted (· < ·) → p (ofList xs)) (s : Set' α) : p s := by
  induction s using ind_ofList; nm xs h₁ h₂; apply h _ # h₂.lt_of_le h₁

@[simp]
theorem sorted_toList' [ha : LinearOrder α] : s.toList.Sorted (· < ·) :=
  sorted_toList.lt_of_le nodup_toList

theorem toList_ofList_of_nodup [ha : LinearOrder α] {xs : List α}
(h : xs.Nodup) : (ofList xs).toList = xs.mergeSort := by
  induction xs; simp
  nm x xs ih
  simp at h ⊢
  rcases h with ⟨h₁, h₂⟩
  specialize ih h₂
  rw [List.eq_iff_of_nodup_and_sorted (r := (· < ·))] <;> try simp [h₁, h₂]
  · intro y z h₃ h₄ h₅ h₆
    replace h₅ := h₅.trans h₆
    simp at h₅
  · have H := @(x :: xs).sorted_mergeSort α (le := (· ≤ ·))
    simp at H
    apply List.Sorted.lt_of_le _ # by simp [h₁, h₂]
    apply H

theorem toList_ofList_of_sorted [ha : LinearOrder α] {xs : List α}
(h : xs.Sorted (· < ·)) : (ofList xs).toList = xs := by
  rw [toList_ofList_of_nodup h.nodup]
  rw [List.mergeSort_of_sorted]
  simp; exact h.le_of_lt

omit hb₁ hb₂
theorem fold_insert_of_notMem' {f : β → α → β} {z x hh} (hx : x ∉ s) :
(s.insert x).fold f z hh = s.fold f (f z x) hh := by
  classical
  simp_rw [fold_eq_foldl_toList]  
  have h₁ : x ∈ (s.insert x).toList; simp
  have h₂ : s.insert x |>.toList.Nodup; simp
  rw [List.mem_iff_append] at h₁
  choose xs ys h₁ using h₁
  rw [h₁] at h₂ ⊢
  suffices h₃ : s.toList = xs ++ ys
  · rw [h₃]
    simp
    congr
    clear! ys x
    rw [List.foldl_apply_comm]
    apply hh
  have h₅ := s.insert x |>.sorted_toList
  rw [h₁] at h₅
  replace h₅ := h₅.lt_of_le h₂
  induction s using ind_ofList
  nm zs H₁ H₂
  replace H₂ := H₂.lt_of_le H₁
  rw [toList_ofList_of_sorted H₂]
  simp at hx
  have H₃ := h₂.of_append_left
  have H₄ : (xs ++ x :: ys).erase x = (xs ++ ys)
  · grind
  have H₅ : xs ++ ys |>.Nodup
  · rw [←H₄]; exact List.nodup_erase h₂
  have H₆ := List.nodup_append_comm.mp H₅
  apply List.eq_of_perm_of_sorted_loc (r := (· ≤ ·)) <;> try simp
  · symm
    apply List.perm_of_nodup_and_subset_and_length_eq H₁
    · intro y hy
      simp
      replace h₁ := congrArg (y ∈ ·) h₁
      simp at h₁
      grind
    · rw [←H₄, ←h₁]
      simp
      rw [size_insert # by simpa]
      simp
      rw [size_ofList_of_nodup H₁]
  · apply H₂.le_of_lt
  · rw [←H₄, ←h₁]; apply List.sorted_erase; simp

omit hb₁ hb₂
theorem fold_insert_of_notMem {f : β → α → β} {z x hh} (hx : x ∉ s) :
(s.insert x).fold f z hh = f (s.fold f z hh) x := by
  classical
  rw [fold_insert_of_notMem' hx]
  simp_rw [fold_eq_foldl_toList]
  rw [List.foldl_apply_comm]
  apply hh

@[simp]
theorem toFinset_insert {x} : (s.insert x).toFinset = insert x s.toFinset := by
  classical
  by_cases hx : x ∈ s
  · rw [insert_eq_of_mem hx, Finset.insert_eq_of_mem]
    exact mem_toFinset_of_mem hx
  exact fold_insert_of_notMem hx

@[simp]
theorem mem_toFinset {x} : x ∈ s.toFinset ↔ x ∈ s := by
  classical
  refine ⟨?_, mem_toFinset_of_mem⟩
  intro h
  rw [toFinset] at h
  rw [s.fold_eq_foldl_toList] at h
  rw [←mem_toList]
  generalize s.toList = xs at h ⊢; clear! s
  induction xs using List.reverseRecOn <;> grind

theorem toSet_union : (s₁ ∪ s₂).toSet = s₁.toSet ∪ s₂.toSet := by
  ext; simp

theorem toSet_inter : (s₁ ∩ s₂).toSet = s₁.toSet ∩ s₂.toSet := by
  ext; simp

theorem toFinset_union : (s₁ ∪ s₂).toFinset = s₁.toFinset ∪ s₂.toFinset := by
  ext; simp

theorem toFinset_inter : (s₁ ∩ s₂).toFinset = s₁.toFinset ∩ s₂.toFinset := by
  ext; simp

@[simp]
theorem finite_toSet : s.toSet.Finite := by
  apply Set.finite_of_subset_finset s.toFinset; simp

@[simp]
theorem toFinset_coe_set : (s.toFinset : Set α) = s.toSet := by
  ext; simp

@[simp]
theorem card_toFinset : s.toFinset.card = s.size := by
  induction s using ind; simp
  clear! s; nm s x hx ih
  simp
  rw [size_insert hx, Finset.card_insert_of_notMem, ih]
  simpa

@[simp]
theorem ncard_toSet : s.toSet.ncard = s.size := by
  rw [←toFinset_coe_set, Set.ncard_coe_finset]; simp

@[simp]
theorem ofSet_toSet_list {xs : List α} : ofSet xs.toSet = ofList xs := by
  ext; simp; rw [mem_ofSet] <;> simp

@[simp]
theorem list_toSet_ofList {xs : List α} : (ofList xs).toSet = xs.toSet := by
  ext; simp;

-- #check 0 #exit

end Set'

namespace System

universe u
variable {S T : Type u}
variable {sys : System S T}

theorem exi_simulate_full_of_simulate_eq' {f n s s₁ r}
(h : sys.simulate f s n = (s₁, r)) : ∃ k, sys.simulate f s k = (s₁, 0) := by
  have := exi_simulate_full_of_simulate_eq h; grind

-- #check 0 #exit

end System

namespace AP

def State.diff (s₁ s : State) : ℕ :=
  s₁.hist.length - s.hist.length

def State.diffTrs (s₁ s : State) : List PointZ :=
  s₁.hist.take (s₁.diff s) |>.reverse

def State.moveSim (s : State) (st : Strat) (s₁ : State) :
Option # (PointZ × State) ⊕ (PointZ × State) := do
  guard # (sys.simulate st.f s # s₁.diff s).1 = s₁
  let p := st.f s₁
  let s₂ ← sys.tr s₁ p
  pure # ite s₁.aTurn Sum.inr Sum.inl (p, s₂)

def State.aMoveSim (s : State) (st : Strat) (s₁ : State) : Option (PointZ × State) := do
  match ← s.moveSim st s₁ with
  | .inr r => some r
  | _ => none

def State.dMoveSim (s : State) (st : Strat) (s₁ : State) : Option (PointZ × State) := do
  match ← s.moveSim st s₁ with
  | .inl r => some r
  | _ => none

def State.aVisited' (s : State) (ps : List PointZ) : Set' PointZ :=
  match ps with
  | [] => ∅
  | p :: ps =>
    let set := sys.tr s p |>.iget.aVisited' ps
    if s.aTurn then set.insert p else set

def State.aVisited (s s₁ : State) : Set' PointZ :=
  State.aVisited' s (s₁.diffTrs s) |>.insert s.aPos

def State.aPtsSimAt (s : State) (st : Strat) : Set (State × PointZ) :=
  {(s₁, p) | ∃ s₂, s.aMoveSim st s₁ = some (p, s₂)}

def State.aPtsSim (s : State) (st : Strat) : Set PointZ :=
  Prod.snd '' s.aPtsSimAt st

def State.init (s : State) : State :=
  initState s.pw s.aPos₀

def State.prev (s : State) : State :=
  sys.trs s.init (s.diffTrs s.init |>.init) |>.1

def State.lastMove (s : State) : PointZ :=
  s.diffTrs s.prev |>.getLast!

def State.IsInit (s : State) : Prop :=
  sys.Initial s

noncomputable
def State.aPtsSimNcard (s : State) (st : Strat) (set : Set PointZ) : Option ℕ :=
  s.aPtsSimAt st |>.filter (·.2 ∈ set) |>.ncard?

-- #check 0 #exit

-----

theorem State.diff_eq_of_simulate' {s f n s₁ r}
(h : sys.simulate f s n = (s₁, r)) : s₁.diff s + r = n := by
  unfold diff
  rw [length_hist_eq_of_simulate_eq h]
  have h₁ := sys.snd_le_of_simulate_eq h
  omega

theorem State.diff_eq_of_simulate {s f n s₁ r}
(h : sys.simulate f s n = (s₁, r)) : s₁.diff s = n - r := by
  have := diff_eq_of_simulate' h; omega

theorem State.diff_eq_of_simulate_full {s f n s₁}
(h : sys.simulate f s n = (s₁, 0)) : s₁.diff s = n :=
  diff_eq_of_simulate h

@[simp]
theorem State.length_diffTrs {s s₁ : State} : (s₁.diffTrs s).length = s₁.diff s := by
  simp [diffTrs, diff]

@[simp]
theorem State.diff_self {s : State} : s.diff s = 0 := by
  simp [diff]

@[simp]
theorem State.diffTrs_self {s : State} : s.diffTrs s = [] := by
  simp [diffTrs]

@[simp]
theorem State.aVisited'_nil {s : State} : s.aVisited' [] = ∅ := rfl

@[simp]
theorem State.aVisited_self {s : State} : s.aVisited s = Set'.singleton s.aPos := by
  simp [aVisited]

theorem State.diff_eq_of_tr {s s₁ s₂ p} (h : sys.tr s₁ p = some s₂)
(h₁ : sys.Reachable s s₁) : s₂.diff s = s₁.diff s + 1 := by
  simp [diff, length_hist_eq_of_tr h]; have := length_hist_le_of_reachable h₁; omega

theorem State.diffTrs_eq_of_tr {s s₁ s₂ p} (h : sys.tr s₁ p = some s₂)
(h₁ : sys.Reachable s s₁) : s₂.diffTrs s = s₁.diffTrs s ++ [p] := by
  simp [diffTrs, diff_eq_of_tr h h₁, hist_eq_of_tr h]

theorem State.diffTrs_eq_of_trs_full {s ps s₁}
(h : sys.trs s ps = (s₁, [])) : s₁.diffTrs s = ps := by
  induction ps using List.reverseRecOn generalizing s₁
  · simp at h; simp [h]
  nm ps p ih
  simp at h
  choose s' h₁ h₂ using h
  specialize ih h₁
  simpa [diffTrs_eq_of_tr h₂ # sys.reachable_of_trs h₁]

@[simp]
theorem State.aVisited'_singleton {s : State} {p} :
s.aVisited' [p] = if s.aTurn then Set'.singleton p else ∅ := by
  simp [aVisited']

theorem AState.aVisited'_cons {s s' : State} {p ps} [hs : AState s]
(h : sys.tr s p = some s') : s.aVisited' (p :: ps) =
(s'.aVisited' ps).insert p := by
  simp [State.aVisited', h]

theorem DState.aVisited'_cons {s s' : State} {p ps} [hs : DState s]
(h : sys.tr s p = some s') : s.aVisited' (p :: ps) = s'.aVisited' ps := by
  simp [State.aVisited', h]

theorem AState.aVisited'_snoc {s s₁ : State} {ps p} [hs : sys.WF s]
[hs₁ : AState s₁] (h₁ : sys.trs s ps = (s₁, [])) :
s.aVisited' (ps ++ [p]) = (s.aVisited' ps).insert p := by
  induction ps generalizing s
  · simp at h₁; simp [h₁]
  nm p₁ ps ih
  simp at h₁
  choose s' h₁ h₃ using h₁
  have hs' := sys.wf_of_tr h₁
  specialize ih h₃
  replace hs := s.aState_or_dState
  rw [List.cons_append]
  rcases hs with hs | hs
  · simp_rw [AState.aVisited'_cons h₁, ih, Set'.insert_comm]
  · simp_rw [DState.aVisited'_cons h₁, ih]

theorem DState.aVisited'_snoc {s s₁ : State} {ps p} [hs : sys.WF s]
[hs₁ : DState s₁] (h₁ : sys.trs s ps = (s₁, [])) :
s.aVisited' (ps ++ [p]) = s.aVisited' ps := by
  induction ps generalizing s
  · simp at h₁; simp [h₁]
  nm p₁ ps ih
  simp at h₁
  choose s' h₁ h₃ using h₁
  have hs' := sys.wf_of_tr h₁
  specialize ih h₃
  replace hs := s.aState_or_dState
  rw [List.cons_append]
  rcases hs with hs | hs
  · simp_rw [AState.aVisited'_cons h₁, ih]
  · simp_rw [DState.aVisited'_cons h₁, ih]

theorem AState.aVisited_eq_of_tr {s s₁ s₂ p} [hs : sys.WF s] [hs₁ : AState s₁]
(h : sys.tr s₁ p = some s₂) (h₁ : sys.Reachable s s₁) :
s.aVisited s₂ = (s.aVisited s₁).insert p := by
  rw [sys.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  simp [State.aVisited]
  rw [State.diffTrs_eq_of_trs_full h₁]
  have h₂ : sys.trs s (ps ++ [p]) = (s₂, [])
  · simpa [h₁]
  rw [State.diffTrs_eq_of_trs_full h₂, Set'.insert_comm]
  rw [aVisited'_snoc h₁]

theorem DState.aVisited_eq_of_tr {s s₁ s₂ p} [hs : sys.WF s] [hs₁ : DState s₁]
(h : sys.tr s₁ p = some s₂) (h₁ : sys.Reachable s s₁) :
s.aVisited s₂ = s.aVisited s₁ := by
  rw [sys.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  simp [State.aVisited]
  rw [State.diffTrs_eq_of_trs_full h₁]
  have h₂ : sys.trs s (ps ++ [p]) = (s₂, [])
  · simpa [h₁]
  rw [State.diffTrs_eq_of_trs_full h₂]
  rw [aVisited'_snoc h₁]

theorem State.mem_aVisited_iff {s f n s₁ p} [hs : sys.WF s]
(h : sys.simulate f s n = (s₁, 0)) : p ∈ s.aVisited s₁ ↔ p = s.aPos ∨
∃ k < n, ∃ s', AState s' ∧ sys.simulate f s k = (s', 0) ∧ f s' = p := by
  induction n generalizing s₁
  · simp at h; simp [h]
  nm n ih
  simp at h
  choose s' h₁ h₂ using h
  specialize ih h₁
  have hs' : sys.WF s' := sys.wf_of_simulate_eq h₁
  have hs₁ := sys.wf_of_tr h₂
  have h₃ := sys.reachable_of_simulate_eq h₁
  replace hs' := s'.aState_or_dState
  rcases hs' with hs' | hs'
  all_goals simp [hs'.aVisited_eq_of_tr h₂ h₃, ih]; clear ih
  · grind
  apply iff_of_eq; congr 1; apply propext
  apply exists_congr; intro k
  rw [Nat.lt_add_one_iff]
  by_cases h : k ≠ n
  · simp [le_iff_eq_or_lt, h]
  push_neg at h; subst h
  simp
  rintro s₂ hs₂ h₄ rfl
  simp [h₁] at h₄
  contrapose! h₄
  apply ne_of_congr (·.aTurn); simp

theorem State.trs_diffTrs {s s₁ ps ps'} [hs : sys.WF s]
(h : sys.trs s ps = (s₁, ps')) : sys.trs s (s₁.diffTrs s) = (s₁, []) := by
  induction ps using List.reverseRecOn generalizing s s₁ ps'
  · simp at h; simp [h]
  nm ps p ih
  simp [sys.trs_append] at h
  generalize hr : sys.trs s ps = r at h
  rcases r with ⟨s', r⟩
  dsimp at h
  split_ifs at h with h₁
  · subst h₁
    simp at h
    specialize ih hr
    simp [System.trs] at h
    split at h
    · grind
    nm x s₂ h₁; clear x
    simp at h
    rcases h with ⟨rfl, rfl⟩
    rw [diffTrs_eq_of_tr h₁ # sys.reachable_of_trs hr]
    simpa [ih]
  simp at h
  rcases h with ⟨rfl, rfl⟩
  exact ih hr

theorem State.simulate_diff {s s₁ f n r} [hs : sys.WF s]
(h : sys.simulate f s n = (s₁, r)) : sys.simulate f s (s₁.diff s) = (s₁, 0) := by
  induction n generalizing s s₁ r
  · simp at h; simp [h]
  nm n ih
  rw [sys.simulate_add] at h
  simp at h
  generalize hr : sys.simulate f s n = r at h
  rcases r with ⟨s', r⟩
  dsimp at h
  split_ifs at h with h₁
  · subst h₁
    simp at h
    specialize ih hr
    simp [System.simulate] at h
    split at h
    · grind
    nm x s₂ h₁; clear x
    simp at h
    rcases h with ⟨rfl, rfl⟩
    rw [diff_eq_of_tr h₁ # sys.reachable_of_simulate_eq hr]
    rw [sys.simulate_add]
    simpa [ih]
  simp at h
  rcases h with ⟨rfl, rfl⟩
  exact ih hr

theorem State.aPtsSim_eq_setOf {s : State} {st} : s.aPtsSim st =
{p | ∃ s₁ s₂, s.aMoveSim st s₁ = some (p, s₂)} := by
  ext; simp [aPtsSim, aPtsSimAt]

theorem State.mem_aPtsSim_iff_aPtsSimAt {s : State} {st p} :
p ∈ s.aPtsSim st ↔ ∃ s₁, (s₁, p) ∈ s.aPtsSimAt st := by
  simp [aPtsSim]

theorem State.mem_aPtsSimAt_iff_simulate_tr {s s₁ p} {st : Strat} [hs : sys.WF s] :
(s₁, p) ∈ s.aPtsSimAt st ↔ AState s₁ ∧ ∃ n, sys.simulate st.f s n = (s₁, 0) ∧
∃ s₂, sys.tr s₁ (st.a.f s₁) = some s₂ ∧ st.a.f s₁ = p := by
  simp only [aPtsSimAt, aMoveSim, moveSim, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff', Option.guard_eq_some', Option.some.injEq, exists_const, Sum.exists,
    reduceCtorEq, and_false, exists_eq_right, false_or, exists_and_left, Set.mem_setOf_eq,
    exists_and_right]
  constructor
  · rintro ⟨h₁, s₂, s₃, h₂, h₃⟩
    split_ifs at h₃ with ht
    simp at h₃
    rcases h₃ with ⟨rfl, rfl⟩
    apply and_of
    · constructor
      · rw [←h₁]; infer_instance
      exact ht
    intro hs₁
    clear ht
    simp
    generalize hr : sys.simulate st.f s (s₁.diff s) = r at h₁ ⊢
    rcases r with ⟨s₁, r⟩
    dsimp at *
    subst h₁
    simp at h₂ ⊢
    simp [h₂]
    use s₁.diff s - r, sys.simulate_sub_eq_of hr
  · rintro ⟨hs₁, ⟨n, h₁⟩, ⟨s₂, h₂⟩, rfl⟩
    simp [simulate_diff h₁]
    use s₂

theorem State.mem_aPtsSim_iff_simulate_tr {s p} {st : Strat} [hs : sys.WF s] :
p ∈ s.aPtsSim st ↔ ∃ n s₁, AState s₁ ∧ sys.simulate st.f s n = (s₁, 0) ∧
∃ s₂, sys.tr s₁ (st.a.f s₁) = some s₂ ∧ st.a.f s₁ = p := by
  simp_rw [mem_aPtsSim_iff_aPtsSimAt, mem_aPtsSimAt_iff_simulate_tr]; grind

theorem State.mem_aPtsSim_iff_simulate_ge_two {s p} {st : Strat} [hst : st.WF] [hs : sys.WF s] :
p ∈ s.aPtsSim st ↔ ∃ n s₁, 2 ≤ n ∧ sys.simulate st.f s n = (s₁, 0) ∧ s₁.aPos = p := by
  rw [mem_aPtsSim_iff_simulate_tr]
  constructor
  · rintro ⟨n, s₁, hs₁, h₁, s₂, h₂, rfl⟩
    have hs₂ := DState.of_tr h₂
    obtain ⟨s₃, h₃⟩ : sys.validTr s₂ (st.d.f s₂)
    · simp
    use n + 2, by omega
    rw [sys.simulate_add]
    simp [System.simulate, h₁, h₂, h₃]
    rw [DState.aPos_eq_of_tr h₃, AState.aPos_eq_of_tr h₂]
  · rintro ⟨n, s₃, hn, h₁, rfl⟩
    simp only [exists_and_right]
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
    rw [add_comm] at h₁
    simp at h₁
    obtain ⟨s₂, ⟨s₁, h₁, h₂⟩, h₃⟩ := h₁
    have hs₁ : sys.WF s₁ := sys.wf_of_simulate_eq h₁
    replace hs₁ := s₁.aState_or_dState
    rcases hs₁ with hs₁ | hs₁
    · simp at h₂
      have hs₂ := DState.of_tr h₂
      use n, s₁, hs₁, h₁
      refine ⟨⟨s₂, h₂⟩, ?_⟩
      rw [DState.aPos_eq_of_tr h₃, AState.aPos_eq_of_tr h₂]
    · have hs₂ := AState.of_tr h₂
      simp at h₂ h₃
      use n + 1, s₂, hs₂
      rw [sys.simulate_add]
      simp [h₁]
      use h₂
      refine ⟨⟨s₃, h₃⟩, ?_⟩
      rw [AState.aPos_eq_of_tr h₃]

theorem State.aVisited_subset_of_simulate_le  (st : Strat) k n {s s₁ s₂} [hs : sys.WF s]
(hn : k ≤ n) (h₁ : sys.simulate st.f s k = (s₁, 0)) (h₂ : sys.simulate st.f s n = (s₂, 0)) :
s.aVisited s₁ ⊆ s.aVisited s₂ := by
  intro p; rw [mem_aVisited_iff h₁, mem_aVisited_iff h₂]; grind

@[simp]
instance {s : State} : sys.Initial s.init := by
  unfold State.init; infer_instance

@[simp]
theorem State.one_le_hist_length {s} [hs : sys.WF s] : 1 ≤ s.hist.length := by
  simp [Nat.one_le_iff_ne_zero]

theorem State.diff_init_succ {s} [hs : sys.WF s] : s.diff s.init + 1 = s.hist.length := by
  simp [init, diff]

@[simp]
theorem State.diff_init {s} [hs : sys.WF s] : s.diff s.init = s.hist.length - 1 := by
  have := s.diff_init_succ; omega

@[simp]
theorem State.isInit_initial {s} [hs : sys.Initial s] : s.IsInit := hs

theorem State.isInit_of_length_hist_eq_one {s}
[hs : sys.WF s] (h : s.hist.length = 1) : s.IsInit := by
  rw [IsInit, initial_iff]; ext <;> simp_all

theorem State.length_hist_eq_one_of_isInit {s : State}
(h : s.IsInit) : s.hist.length = 1 := by
  rw [IsInit, initial_iff] at h; rw [←h]; rfl

theorem State.isInit_iff_length_hist_eq_one {s}
[hs : sys.WF s] : s.IsInit ↔ s.hist.length = 1 :=
  ⟨length_hist_eq_one_of_isInit, isInit_of_length_hist_eq_one⟩

@[simp]
theorem State.length_hist_init {s : State} : s.init.hist.length = 1 := by
  simp [init]

@[simp]
theorem State.diffTrs_init {s} [hs : sys.WF s] : s.diffTrs s.init = s.hist.init.reverse := by
  simp [diffTrs]

@[simp]
theorem AState.initState_ne {s pw p₀} [ha : AState s] : initState pw p₀ ≠ s := by
  rintro rfl; simp at ha

@[simp]
theorem AState.not_isInit {s} [ha : AState s] : ¬s.IsInit := by
  simp [State.IsInit]

theorem State.wf_prev_and_tr {s} [hs : sys.WF s]
(h : ¬s.IsInit) : sys.WF s.prev ∧ sys.tr s.prev s.lastMove = some s := by
  choose ps h₁ using wf_iff.mp hs
  induction ps using List.reverseRecOn
  · simp at h₁
    rw [←h₁] at h
    simp at h
  nm ps p ih; clear ih
  simp at h₁
  choose s' h₁ h₂ using h₁
  rw [lastMove, prev]
  simp [hist_eq_of_tr h₂, hist_eq_of_trs h₁]
  simp [init, h₁, diffTrs_eq_of_tr h₂, h₂]
  exact sys.wf_of_trs h₁

theorem State.wf_prev {s} [hs : sys.WF s] (h : ¬s.IsInit) : sys.WF s.prev :=
  wf_prev_and_tr h |>.1

theorem State.prev_tr_lastMove {s} [hs : sys.WF s]
(h : ¬s.IsInit) : sys.tr s.prev s.lastMove = some s :=
  wf_prev_and_tr h |>.2

theorem State.length_hist_prev {s} [hs : sys.WF s]
(h : ¬s.IsInit) : s.prev.hist.length = s.hist.length - 1 := by
  simp [length_hist_eq_of_tr # prev_tr_lastMove h]

theorem State.not_isInit_of_tr {s s' p} [hs : sys.WF s]
(h : sys.tr s p = some s') : ¬s'.IsInit := by
  have hs' := sys.wf_of_tr h; simp [isInit_iff_length_hist_eq_one, length_hist_eq_of_tr h]

theorem State.eq_iff_pw_and_hist {s₁ s₂} [hs₁ : sys.WF s₁] [hs₂ : sys.WF s₂] :
s₁ = s₂ ↔ s₁.pw = s₂.pw ∧ s₁.hist = s₂.hist := by
  use by rintro rfl; simp;
  rintro ⟨h₁, h₂⟩
  choose ps₁ h₃ using wf_iff.mp hs₁
  choose ps₂ h₄ using wf_iff.mp hs₂
  rw [←h₁, aPos₀, ←h₂, ←aPos₀] at h₄
  simp [hist_eq_of_trs h₃, hist_eq_of_trs h₄] at h₂
  grind

theorem State.tr_inj {s₁ s₂ s₃ p₁ p₂} [hs₁ : sys.WF s₁] [hs₂ : sys.WF s₂]
(h₁ : sys.tr s₁ p₁ = some s₃) (h₂ : sys.tr s₂ p₂ = some s₃) : s₁ = s₂ ∧ p₁ = p₂ := by
  replace hs₁ := s₁.aState_or_dState
  rcases hs₁ with hs₁ | hs₁
  · have hs₃ := DState.of_tr h₁
    replace hs₂ := AState.of_tr' h₂
    rw [AState.tr_eq_some_iff] at h₁ h₂
    rcases h₂ with ⟨⟨h₄, h₅, h₆⟩, rfl⟩
    rcases h₁ with ⟨⟨h₁, h₂, h₃⟩, h₇⟩
    rw [eq_iff_pw_and_hist]; grind
  · have hs₃ := AState.of_tr h₁
    replace hs₂ := DState.of_tr' h₂
    rw [DState.tr_eq_some_iff] at h₁ h₂
    rcases h₂ with ⟨⟨h₄, h₅⟩, rfl⟩
    rcases h₁ with ⟨⟨h₁, h₂⟩, h₇⟩
    rw [eq_iff_pw_and_hist]; grind

theorem State.lastMove_eq_of_tr {s s' p} [hs : sys.WF s]
(h : sys.tr s p = some s') : s'.lastMove = p := by
  have hs' := sys.wf_of_tr h
  have h₁ := not_isInit_of_tr h
  have h₂ := prev_tr_lastMove h₁
  have H := wf_prev h₁
  obtain ⟨rfl, rfl⟩ := tr_inj h h₂; rfl

theorem State.diffTrs_prev {s} [hs : sys.WF s]
(h : ¬s.IsInit) : s.diffTrs s.prev = [s.lastMove] := by
  simp [diffTrs_eq_of_tr # prev_tr_lastMove h]

theorem State.diff_prev {s} [hs : sys.WF s]
(h : ¬s.IsInit) : s.diff s.prev = 1 := by
  simp [diff_eq_of_tr # prev_tr_lastMove h]

theorem State.prev_eq_of_tr {s s' p} [hs : sys.WF s]
(h : sys.tr s p = some s') : s'.prev = s := by
  have hs' := sys.wf_of_tr h
  have H₁ := not_isInit_of_tr h
  have h₁ := s'.prev_tr_lastMove H₁
  have H₂ := wf_prev H₁
  obtain ⟨rfl, rfl⟩ := tr_inj h h₁; rfl

theorem State.aPtsSimAt_point_eq_of_state_eq {s : State} {s₁ p₁ p₂ st} [hs : sys.WF s]
(h₁ : (s₁, p₁) ∈ s.aPtsSimAt st) (h₂ : (s₁, p₂) ∈ s.aPtsSimAt st) : p₁ = p₂ := by
  rw [mem_aPtsSimAt_iff_simulate_tr] at h₁ h₂; grind

@[simp]
theorem State.aPtsSimNcard_empty {s : State} {st} : s.aPtsSimNcard st ∅ = some 0 := by
  simp [aPtsSimNcard]

@[simp]
theorem State.aPtsSimNcard_eq_zero_iff {s : State} {st set} [hs : sys.WF s] :
s.aPtsSimNcard st set = some 0 ↔ ∀ n s₁ s₂ [AState s₁],
sys.simulate st.f s n = (s₁, 0) → sys.tr s₁ (st.a.f s₁) = some s₂ → s₂.aPos ∉ set := by
  rw [aPtsSimNcard, Set.ncard?]
  split_ifs with h₁; rotate_left
  · simp at h₁ ⊢
    replace h₁ := Set.exi_mem_of_infinite h₁
    rcases h₁ with ⟨⟨s₁, p⟩, h₁⟩
    simp at h₁
    rw [mem_aPtsSimAt_iff_simulate_tr] at h₁
    obtain ⟨⟨hs₁, n, h₁, s₂, h₂, h₃⟩, h₄⟩ := h₁
    use n, s₁, hs₁, h₁, s₂, h₂
    rwa [AState.aPos_eq_of_tr h₂, h₃]
  simp
  rw [Set.ncard_eq_zero # by grind]
  rw [Set.eq_empty_iff]
  simp
  constructor
  · intro h n s₁ s₂ hs₁ h₂ h₃
    specialize h s₁ (st.a.f s₁)
    rw [mem_aPtsSimAt_iff_simulate_tr] at h
    rw [AState.aPos_eq_of_tr h₃]
    apply h; clear h
    use hs₁, n, h₂, s₂
  · intro h s₁ p h₂
    rw [mem_aPtsSimAt_iff_simulate_tr] at h₂
    choose hs₁ n h₂ s₂ h₃ h₄ using h₂
    specialize h n s₁ s₂ h₂ h₃
    rwa [←h₄, ←AState.aPos_eq_of_tr h₃]

theorem State.aPtsSimAt_eq_of_length_hist_eq {s s₁ s₂ p₁ p₂ st} [hs : sys.WF s]
(h₁ : (s₁, p₁) ∈ s.aPtsSimAt st) (h₂ : (s₂, p₂) ∈ s.aPtsSimAt st)
(h₃ : s₁.hist.length = s₂.hist.length) : s₁ = s₂ := by
  rw [mem_aPtsSimAt_iff_simulate_tr] at h₁ h₂
  choose hs₁ n h₁ h₄ h₅ h₆ using h₁
  choose hs₂ k h₂ h₇ h₈ h₉ using h₂
  simp [length_hist_eq_of_simulate_eq h₁, length_hist_eq_of_simulate_eq h₂] at h₃
  subst h₃
  simp [h₁] at h₂
  exact h₂

theorem State.finite_filter_aPtsSimAt_iff_image_length_hist {s : State} {st p}
[hs : sys.WF s] : (s.aPtsSimAt st |>.filter p |>.Finite) ↔
(s.aPtsSimAt st |>.filter p |>.image (·.1.hist.length) |>.Finite) := by
  rw [Set.finite_image_iff]
  rintro ⟨s₂, p₂⟩ h₄ ⟨s₃, p₃⟩ h₅ h₆
  simp at h₄ h₅ h₆ ⊢
  rcases h₄ with ⟨h₄, hp₂⟩
  rcases h₅ with ⟨h₅, hp₃⟩
  apply and_of # aPtsSimAt_eq_of_length_hist_eq h₄ h₅ h₆
  rintro rfl; exact aPtsSimAt_point_eq_of_state_eq h₄ h₅

theorem State.infinite_filter_aPtsSimAt_iff_image_length_hist {s : State} {st p}
[hs : sys.WF s] : (s.aPtsSimAt st |>.filter p |>.Infinite) ↔
(s.aPtsSimAt st |>.filter p |>.image (·.1.hist.length) |>.Infinite) := by
  rw [iff_iff_not']; simp [finite_filter_aPtsSimAt_iff_image_length_hist]

theorem State.nonempty_filter_aPtsSimAt_iff_image_length_hist {s : State} {st p} :
(s.aPtsSimAt st |>.filter p |>.Nonempty) ↔
(s.aPtsSimAt st |>.filter p |>.image (·.1.hist.length) |>.Nonempty) := by
  simp

-- theorem State.exi_aPtsSimNcard_eq_succ_iff.aux₁
-- {s : State} {st : Strat} {set : Set PointZ} [hs : sys.WF s] [hst : st.WF]
-- (h₁ : s.aPtsSimAt st |>.filter (·.2 ∈ set) |>.Finite)
-- (h₂ : s.aPtsSimAt st |>.filter (·.2 ∈ set) |>.Nonempty) :
-- ∃ n s₁, n ≠ 0 ∧ AState s₁ ∧ sys.simulate st.f s n = (s₁, 0) ∧ s₁.aPos ∈ set ∧
-- ∀ k s₂, k ≠ 0 → sys.simulate st.f s₁ k = (s₂, 0) → s₂.aPos ∉ set := by
--   rw [finite_filter_aPtsSimAt_iff_image_length_hist] at h₁
--   rw [nonempty_filter_aPtsSimAt_iff_image_length_hist] at h₂
--   
--   generalize h₃ : (s.aPtsSimAt st |>.filter (·.2 ∈ set)
--     |>.image (·.1.hist.length)) = sn at h₁ h₂
--   
--   choose N h₄ h₅ using Set.exi_max h₁ h₂
--   clear h₁ h₂
--   
--   simp [←h₃] at h₄
--   obtain ⟨s₁, ⟨p, h₁, h₂⟩, rfl⟩ := h₄
--   rw [mem_aPtsSimAt_iff_simulate_tr] at h₁
--   choose hs₁ n h₁ s₂ h₄ h₆ using h₁
--   subst h₆
--   simp [length_hist_eq_of_simulate_eq h₁] at h₅
--   
--   -- cases n
--   -- ·
--     -- exfalso
--     -- simp at h₁
--     -- subst h₁ h₃
--     -- simp at h₅
--     -- 
--     -- let N : ℕ := by sorry
--     -- 
--     -- specialize h₅ N s (st.a.f s) _ h₂
--     -- ·
--     --   rw [mem_aPtsSimAt_iff_simulate_tr]
--     --   use hs₁, 0
--     --   simp [h₄]
--   
--   have hs₂ := DState.of_tr h₄
--   
--   choose s₃ h₆ using st.d.validTr s₂
--   have hs₃ := AState.of_tr h₆
--   
--   use n + 2, s₃, by simp, hs₃
--   split_ands
--   ·
--     simpa [h₁, h₄]
--   ·
--     rwa [DState.aPos_eq_of_tr h₆, AState.aPos_eq_of_tr h₄]
--   
--   intro k s₄ h₇
--   
--   subst h₃
--   simp at h₅
--   
--   -- specialize h₅ (s.hist.length + n + k) s₄
--   
--   sorry
-- 
-- -- #check 0 #exit
-- 
-- theorem State.exi_aPtsSimNcard_eq_succ_iff.aux₂
-- {s : State} {st : Strat} {set : Set PointZ} [hs : sys.WF s] [hst : st.WF]
-- (h₁ : s.aPtsSimAt st |>.filter (·.2 ∈ set) |>.Finite)
-- (h₂ : ∃ n s₁, n ≠ 0 ∧ AState s₁ ∧ sys.simulate st.f s n = (s₁, 0) ∧ s₁.aPos ∈ set ∧
-- ∀ k s₂, k ≠ 0 → sys.simulate st.f s₁ k = (s₂, 0) → s₂.aPos ∉ set) :
-- s.aPtsSimAt st |>.filter (·.2 ∈ set) |>.Nonempty := by
--   choose n s₁ hn hs₁ h₂ h₃ h₄ using h₂
--   clear h₁
--   
--   -- use ⟨s, s₁.aPos⟩
--   -- simp [h₃]
--   -- rw [mem_aPtsSimAt_iff_simulate_tr]
-- 
-- -- #check 0 #exit
-- 
-- theorem State.exi_aPtsSimNcard_eq_succ_iff
-- {s : State} {st : Strat} {set} [hs : sys.WF s] [hst : st.WF] :
-- (∃ n, s.aPtsSimNcard st set = some (n + 1)) ↔ ∃ n s₁, n ≠ 0 ∧ AState s₁ ∧
-- sys.simulate st.f s n = (s₁, 0) ∧ s₁.aPos ∈ set ∧ ∀ k s₂, k ≠ 0 →
-- sys.simulate st.f s₁ k = (s₂, 0) → s₂.aPos ∉ set := by
--   rw [aPtsSimNcard, Set.ncard?]; split_ifs with h₁
--   · simp; rw [Set.ncard_pos # by grind]
--     exact ⟨sorry, exi_aPtsSimNcard_eq_succ_iff.aux₂ h₁⟩
--   simp at h₁ ⊢
--   intro n s₁ hs₁ hn h₂ h₃
--   rw [infinite_filter_aPtsSimAt_iff_image_length_hist] at h₁
--   replace h₁ := h₁.exists_gt # s.hist.length + n
--   choose m h₁ using h₁
--   simp at h₁
--   obtain ⟨⟨sa, ⟨pn, h₁, h₄⟩, h₅⟩, h₆⟩ := h₁
--   rw [mem_aPtsSimAt_iff_simulate_tr] at h₁
--   choose hsa k h₁ sd h₇ h₈ using h₁
--   subst h₈
--   simp [length_hist_eq_of_simulate_eq h₁] at h₅
--   subst h₅
--   simp at h₆
--   replace h₆ := le_of_lt h₆
--   obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₆; clear h₆
--   simp [h₂] at h₁
--   use k, sd
--   simp [h₁, h₇]
--   rwa [AState.aPos_eq_of_tr h₇]