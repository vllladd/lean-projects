import Projects.Esolangs.Cornucopia.Defs

attribute [-simp] List.getElem!_eq_getElem?_getD

section logic

@[simp] theorem or_iff_or_left {p q r : Prop} : (p ∨ q ↔ p ∨ r) ↔ ¬p → (q ↔ r) := by tauto
@[simp] theorem or_iff_or_right {p q r : Prop} : (p ∨ q ↔ r ∨ q) ↔ ¬q → (p ↔ r) := by tauto
@[simp] theorem imp_not_imp_iff {p q : Prop} : p → ¬p → q ↔ True := by tauto
@[simp] theorem not_imp_imp_iff {p q : Prop} : ¬p → p → q ↔ True := by tauto

-- #check 0 #exit

end logic

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

@[simp]
theorem length_mkList {n} {f : ℕ → α} : (mkList n f).length = n := by
  simp [mkList]

@[simp]
theorem mem_mkList {n} {f : ℕ → α} {x} : x ∈ mkList n f ↔ ∃ i < n, f i = x := by
  simp [mkList]

theorem mergeSort_eq_mergeSort_iff {le : α → α → Bool}
(trans : ∀ (a b c : α), le a b → le b c → le a c)
(total : ∀ (a b : α), le a b || le b a)
(antisymm : ∀ (a b : α), le a b → le b a → a = b) :
xs.mergeSort le = ys.mergeSort le ↔ xs.Perm ys := by
  use perm_of_mergeSort_eq_mergeSort
  intro h
  apply eq_of_perm_of_pairwise (r := (le · ·))
  · simpa
  · apply pairwise_mergeSort trans total
  · apply pairwise_mergeSort trans total
  · grind
  · grind
  · grind

@[simp]
theorem map_mkList {n} {f : ℕ → α} {g : α → β} :
(mkList n f).map g = mkList n λ i => g (f i) := by
  simp [mkList]

@[simp]
theorem getElem_mkList {n} {f : ℕ → α} {i}
{h : i < (mkList n f).length} : (mkList n f)[i] = f i := by
  simp [mkList]

@[simp]
theorem mkList_length_getElem! [ha : Inhabited α] : mkList xs.length (xs[·]!) = xs := by
  simp [mkList]

-- #check 0 #exit

end List

namespace Std.ExtDHashMap

open Std

variable {α : Type*} {β : α → Type*} {γ : α → Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp mp₁ mp₂ m m₁ m₂ m₃ : ExtDHashMap α β}
variable [ha : LinearOrder α]
omit ha

attribute [simp] keys_empty

include ha in
theorem toList_insert_of_not_mem {i x} (h : i ∉ m) : (m.insert i x).toList =
(⟨i, x⟩ :: m.toList).mergeSort (·.1 ≤ ·.1) := by
  rw [List.eq_iff_of_nodup_and_pairwise (r := (·.1 ≤ ·.1))]
  rotate_left
  · simp
  · simp [get?_eq_none_of_not_mem h]
  · rintro ⟨j, y⟩ ⟨k, z⟩
    simp; grind
  · simp
  · have h₁ := @List.pairwise_mergeSort
    specialize @h₁ ((i : α) × β i) (le := (·.1 ≤ ·.1))
      (by simp) (by simp) (⟨i, x⟩ :: m.toList)
    grind
  rintro ⟨j, y⟩; simp
  by_cases h₁ : j = i
  · subst h₁; simp [eq_comm, get?_eq_none_of_not_mem h]
  simp [h₁, get?_insert, ne_symm' h₁]

include ha in
theorem keys_insert_of_not_mem {i x} (h : i ∉ m) :
(m.insert i x).keys = (i :: m.keys).mergeSort := by
  simp [keys_eq_map_fst_toList, toList_insert_of_not_mem h]
  apply List.eq_of_sortedLE_and_perm
  · rw [List.map_mergeSort (s := (· ≤ ·)) (by simp)]
    apply List.sortedLE_mergeSort
  · apply List.sortedLE_mergeSort
  simp
  rw [List.perm_iff_mem_iff_of_nodup]; simp
  on_goal 2 => simpa [←keys_eq_map_fst_toList]
  rw [List.nodup_map_iff_inj_on]
  rotate_left
  · simp [get?_eq_none_of_not_mem h]
  simp
  split_ands
  · rintro ⟨j, y⟩ h₁ rfl
    simp [get?_eq_none_of_not_mem h] at h₁
  rintro ⟨j, y⟩ h₁
  dsimp at h₁ ⊢
  split_ands
  · rintro rfl; simp [get?_eq_none_of_not_mem h] at h₁
  · grind

@[simp]
theorem get?_out_inner {i} : m.inner.out.get? i = m.get? i := by
  rcases m with ⟨m⟩
  induction m using Quotient.inductionOn
  simp [get?, lift]

@[simp]
theorem get?_mk {m i} : ({inner := m} : ExtDHashMap α β).get? i = m.out.get? i := by
  simp [get?, lift, Quotient.lift_eq]

@[simp]
theorem insert_mk {m i x} :
({inner := m} : ExtDHashMap α β).insert i x = {inner := ⟦m.out.insert i x⟧} := by
  simp [insert, lift, Quotient.lift_eq]

@[simp]
theorem erase_mk {m i} :
({inner := m} : ExtDHashMap α β).erase i = {inner := ⟦m.out.erase i⟧} := by
  simp [erase, lift, Quotient.lift_eq]

@[simp]
theorem insert_erase_eq_self_iff {i x} :
(m.erase i).insert i x = m ↔ m.get? i = some x := by
  constructor <;> intro h
  · rw [←h]; simp
  rw [ext_iff']
  have h₁ := @DHashMap.insert_erase_equiv
  specialize @h₁ α β _ _ m.inner.out i x _
  · simpa
  symm; apply h₁.symm.trans; symm; clear h₁
  change (_ : DHashMap α β) ≈ _
  rw [←Quotient.eq_mk_iff_out]
  rcases m with ⟨m⟩
  simp at h ⊢
  apply DHashMap.equiv_iff_get?.mpr
  intro j
  ext y
  simp [DHashMap.get?_insert]

include ha in @[simp]
theorem keys_eq_keys_iff {m₁ : ExtDHashMap α β} {m₂ : ExtDHashMap α γ} :
m₁.keys = m₂.keys ↔ ∀ i, i ∈ m₁ ↔ i ∈ m₂ := by
  induction m₂ using ind generalizing m₁
  · simp [eq_empty_iff]
  nm m₂ i x h₁ ih
  simp
  rw [keys_insert_of_not_mem h₁]
  constructor
  · intro h₂ j
    replace h₂ := congrArg (j ∈ ·) h₂
    simp at h₂
    tauto
  intro h₂
  have h₃ : i ∈ m₁; grind
  clear x
  obtain ⟨x, h₄⟩ := get?_eq_some_of_mem h₃
  have h₅ : m₁ = (m₁.erase i).insert i x
  · symm; simpa
  rw [h₅]
  rw [keys_insert_of_not_mem (by simp)]
  rw [List.mergeSort_eq_mergeSort_iff (by simp) (by simp) (by simp)]
  simp; rw [List.perm_iff_mem_iff_of_nodup (by simp) (by simp)]; grind

-- #check 0 #exit

end Std.ExtDHashMap

namespace Map

open Std

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp m m₁ m₂ m₃ : Map α β}
variable [ha : LinearOrder α]
omit ha

theorem get!_insert [hb : Inhabited β] {i x j} :
(mp.insert i x).get! j = if j = i then x else mp.get! j := by
  simp [get!_eq_get!_get?, get?_insert]; grind

theorem get?_ofList_eq_some_iff {xs : List (α × β)} {i x}
(h : (xs.map (·.1)).Nodup) : (ofList xs).get? i = some x ↔ ⟨i, x⟩ ∈ xs := by
  simp [ofList]; rw [ExtDHashMap.get?_ofList_eq_some_iff (by simpa)]; simp

theorem get?_ofList_of_nodup {xs : List (α × β)} {i} (h : (xs.map (·.1)).Nodup) :
(ofList xs).get? i = (xs.find? (·.fst = i)).map (·.2) := by
  unfold Option.map; split
  · nm a x h₁; clear a
    rename' i => j
    rcases x with ⟨i, x⟩
    rw [get?_ofList_eq_some_iff h]
    grind
  nm a h₁; clear a
  simp at h₁ ⊢
  grind

theorem get!_ofList_of_nodup [hb : Inhabited β] {xs : List (α × β)} {i}
(h : (xs.map (·.1)).Nodup) : (ofList xs).get! i =
((xs.find? (·.fst = i)).map (·.2)).get! := by
  rw [get!_eq_get!_get?, get?_ofList_of_nodup h]

@[simp]
theorem mem_union {i} : i ∈ m₁ ∪ m₂ ↔ i ∈ m₁ ∨ i ∈ m₂ := by
  simp [mem_iff_get?_eq_some, get?_union]; grind

include ha in @[simp]
theorem keys_mk {mp} : (⟨mp⟩ : Map α β).keys = mp.keys := rfl

@[simp]
theorem insert_mk {m i x} : (⟨m⟩ : Map α β).insert i x = ⟨m.insert i x⟩ := rfl

@[simp]
theorem erase_mk {m i} : (⟨m⟩ : Map α β).erase i = ⟨m.erase i⟩ := rfl

include ha in
theorem toList_insert_of_not_mem {i x} (h : i ∉ m) : (m.insert i x).toList =
(⟨i, x⟩ :: m.toList).mergeSort (·.1 ≤ ·.1) := by
  rcases m with ⟨m⟩; simp at h ⊢
  rw [ExtDHashMap.toList_insert_of_not_mem h]
  rw [List.map_mergeSort (s := (·.1 ≤ ·.1)) (by simp)]
  simp

include ha in
theorem keys_insert_of_not_mem {i x} (h : i ∉ m) :
(m.insert i x).keys = (i :: m.keys).mergeSort := by
  rcases m with ⟨m⟩; simp at h ⊢
  rw [ExtDHashMap.keys_insert_of_not_mem h]

@[simp]
theorem insert_erase_eq_self_iff {i x} :
(m.erase i).insert i x = m ↔ m.get? i = some x := by
  rcases m with ⟨m⟩; simp

include ha in @[simp]
theorem keys_eq_keys_iff {m₁ : Map α β} {m₂ : Map α γ} :
m₁.keys = m₂.keys ↔ ∀ i, i ∈ m₁ ↔ i ∈ m₂ := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp

theorem union_assoc : (m₁ ∪ m₂) ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) := by
  simp [ext_iff, get?_union]; grind

@[simp]
theorem union_self : m ∪ m = m := by
  simp [ext_iff, get?_union]

@[simp]
theorem union_union_self : m₁ ∪ (m₁ ∪ m₂) = m₁ ∪ m₂ := by
  simp [←union_assoc]

def diff (m₁ m₂ : Map α β) : Map α β :=
  ⟨m₁.1 \ m₂.1⟩

instance : SDiff (Map α β) := ⟨diff⟩
theorem diff_def : m₁ \ m₂ = m₁.diff m₂ := rfl

@[simp]
theorem mk_diff_mk {m₁ m₂} : (⟨m₁⟩ : Map α β) \ ⟨m₂⟩ = ⟨m₁ \ m₂⟩ := rfl

theorem get?_diff {i} : (m₁ \ m₂).get? i = if i ∈ m₂ then none else m₁.get? i := by
  rcases m₁, m₂ with ⟨⟨m₁⟩, ⟨m₂⟩⟩; simp [ExtDHashMap.get?_diff]

@[simp]
theorem union_diff_self : m₁ ∪ (m₂ \ m₁) = m₂ ∪ m₁ := by
  simp [ext_iff, get?_union, get?_diff]
  intro i
  rw! (castMode := .all) [mem_iff_get?_eq_some]
  split_ifs with h; grind
  simp at h
  rw [←Option.eq_none_iff_forall_ne_some] at h
  grind

theorem union_eq_self_left_iff : m₁ ∪ m₂ = m₁ ↔
∀ i x, m₂.get? i = some x → m₁.get? i = some x := by
  simp [ext_iff, get?_union, Option.or]; grind

@[simp]
theorem union_insert_empty {i x} : m₁ ∪ (∅ : Map α β).insert i x = m₁.insert i x := by
  simp [ext_iff, get?_union, get?_insert]; grind

-- #check 0 #exit

end Map

namespace Esolangs.Cornucopia

structure CompatibleDefs (defs : Map String Def) (fs : Map String (List ℕ → ℕ)) : Prop where
  keys_fs : fs.keys = defs.keys
  eval_of_ne_arity ⦃name d⦄ : defs.get? name = some d → ∀ ⦃xs : List ℕ⦄,
    xs.length ≠ d.arity → fs.get! name xs = 0
  eval_eq ⦃name d⦄ : defs.get? name = some d → ∀ ⦃xs : List ℕ⦄,
    xs.length = d.arity → fs.get! name xs = d.expr.eval
    ⟨builtinDefs ∪ .ofList defs.toList⟩ (builtinFs ∪ fs) xs

structure WFDefs (defs : List (String × Def)) : Prop where
  nodup_names : defs.map (·.1) |>.Nodup
  not_isBuiltin_of_mem ⦃name d⦄ : (name, d) ∈ defs → ¬IsBuiltin name
  wf_main : ∃ d, (mainName, d) ∈ defs ∧ d.arity = 1
  wf_def ⦃name d⦄ : (name, d) ∈ defs → d.WF (Prog.ofDefs defs)
  exiu_compatible : ∃! fs, CompatibleDefs (.ofList defs) fs

-- #check 0 #exit

def exprId : Expr :=
  .arg 0

def exprLoop (name : String) : Expr :=
  .call name [.arg 0]

def progId : Prog :=
  .ofDefs [(mainName, ⟨1, exprId⟩)]

def progLoop : Prog :=
  .ofDefs [(mainName, ⟨1, exprLoop mainName⟩)]

-- #check 0 #exit

-----

@[simp]
theorem mem_builtins {b} : b ∈ builtins := by
  cases b <;> decide

instance {name} : Decidable (IsBuiltin name) :=
  decidable_of_bool (name ∈ builtinDefs) # by simp [IsBuiltin, builtinDefs]

@[simp] theorem def_mk {defs name} : (Prog.mk defs).def name = defs.get! name := rfl
@[simp] theorem def?_mk {defs name} : (Prog.mk defs).def? name = defs.get? name := rfl
@[simp] theorem main_mk {defs} : (Prog.mk defs).main = defs.get! mainName := rfl
@[simp] theorem Prog.defs_mk {ds} : defs ⟨ds⟩ = ds := rfl
@[simp] theorem Builtin.arity_succ : Builtin.succ.arity = 1 := rfl
@[simp] theorem Builtin.arity_sub : Builtin.sub.arity = 2 := rfl
@[simp] theorem Prog.arity_mk {defs name} : arity ⟨defs⟩ name = (defs.get! name).arity := rfl
@[simp] theorem Prog.expr_mk {defs name} : expr ⟨defs⟩ name = (defs.get! name).expr := rfl

@[simp]
theorem mem_builtinDefs {name} : name ∈ builtinDefs ↔ IsBuiltin name := by
  simp [builtinDefs, IsBuiltin]

@[simp]
theorem not_isBuiltin_mainName : ¬IsBuiltin mainName := by
  simp [IsBuiltin]; decide

theorem Prog.def_ofDefs {xs name} (h : ¬IsBuiltin name) :
(Prog.ofDefs xs).def name = (Map.ofList xs).get! name := by
  simp [ofDefs]; rw [Map.get!_union_right]; simpa

theorem arity_ofDefs {defs name} (h : ¬IsBuiltin name) :
(Prog.ofDefs defs).arity name = ((Map.ofList defs).get! name).arity := by
  simp [Prog.arity, Prog.def_ofDefs h]

@[simp]
theorem Prog.main_ofDefs {xs} : (Prog.ofDefs xs).main = (Map.ofList xs).get! mainName := by
  simp [ofDefs]; rw [Map.get!_union_right]; simp

@[simp]
theorem main_progId : progId.main = ⟨1, exprId⟩ := by
  simp [progId, Map.get!_insert]

@[simp]
theorem main_progLoop : progLoop.main = ⟨1, exprLoop mainName⟩ := by
  simp [progLoop, Map.get!_insert]

@[simp] theorem wf_exprId {prog} : exprId.WF prog 1 := by simp [Expr.WF, exprId]
@[simp] theorem wf_defId : (Def.mk 1 (.arg 0)).WF progId := wf_exprId

@[simp]
theorem Expr.run_arg {i prog f args} : (arg i).eval prog f args = args[i]! := by
  simp [eval]

@[simp]
theorem Expr.wf_arg {prog n i} : (arg i).WF prog n ↔ i < n := by
  simp [WF]

@[simp]
theorem Builtin.isBuiltin {b : Builtin} : IsBuiltin b.name := by
  simp [IsBuiltin]

@[simp]
theorem nodup_builtins : builtins.Nodup := by
  decide

@[simp]
theorem nodup_map_name_builtins : (builtins.map Builtin.name).Nodup := by
  decide

@[simp]
theorem Builtin.get?_builtinDefs {b : Builtin} : builtinDefs.get? b.name = some b.def := by
  simp [builtinDefs, Map.get?_ofList_eq_some_iff]; use b

@[simp]
theorem Builtin.get!_builtinDefs {b : Builtin} : builtinDefs.get! b.name = b.def := by
  simp [Map.get!_eq_get!_get?]

theorem def?_ofDefs_builtin_eq_of {defs} {b : Builtin}
(h : ∀ d ∈ defs, ¬IsBuiltin d.1) : (Prog.ofDefs defs).def? b.name = some b.def := by
  simp [Prog.ofDefs]; rw [Map.get?_union_left]; simp
  simp; intro d h₁; specialize h _ h₁; simp at h

@[simp]
theorem Prog.defs_ofDefs {defs} : (Prog.ofDefs defs).defs = builtinDefs ∪ .ofList defs := rfl

@[simp]
theorem Prog.hasDef_ofDefs {defs name} :
(Prog.ofDefs defs).HasDef name ↔ IsBuiltin name ∨ name ∈ Map.ofList defs := by
  simp [HasDef]

@[simp]
theorem Builtin.ext_name {b₁ b₂ : Builtin} : b₁.name = b₂.name ↔ b₁ = b₂ := by
  rcases b₁, b₂ with ⟨⟨⟩, ⟨⟩⟩ <;> decide

@[simp] theorem Builtin.arity_def {b : Builtin} : b.def.arity = b.arity := rfl
@[simp] theorem Builtin.expr_def {b : Builtin} : b.def.expr = b.expr := rfl

@[simp]
theorem Builtin.ext_def {b₁ b₂ : Builtin} : b₁.def = b₂.def ↔ b₁ = b₂ := by
  rcases b₁, b₂ with ⟨⟨⟩, ⟨⟩⟩ <;> simp [Def.ext_iff]

@[simp]
theorem get?_builtinDefs_eq_some {name d} :
builtinDefs.get? name = some d ↔ ∃ (b : Builtin), b.name = name ∧ b.def = d := by
  simp [builtinDefs, Map.get?_ofList_of_nodup]
  apply exists_congr; intro b; simp; rintro rfl
  rw [List.find?_eq_some_iff_of_at_most_one]; simp
  simp; rintro b₁ b₂ rfl; simp [eq_comm]

@[simp]
theorem Builtin.wf_expr {prog} {b : Builtin} :
b.expr.WF prog b.arity ↔ ∃ d, prog.def? b.name = some d ∧ d.arity = b.arity := by
  simp [expr, Expr.WF, Prog.HasDef, Map.mem_iff_get?_eq_some,
    Prog.arity, Prog.def, Map.get!_eq_get!_get?, Prog.def?]
  grind

theorem WFDefs.not_mem_of_isBuiltin {defs name d} (H : WFDefs defs)
(h : IsBuiltin name) : (name, d) ∉ defs := by
  grind [H.not_isBuiltin_of_mem]

theorem WFDefs.not_mem_builtin {defs} {b : Builtin} {d}
(H : WFDefs defs) : (b.name, d) ∉ defs := by
  apply H.not_mem_of_isBuiltin; simp

theorem WFDefs.get?_ofList_defs {defs name d} (H : WFDefs defs) :
(Map.ofList defs).get? name = some d ↔ (name, d) ∈ defs :=
  Map.get?_ofList_eq_some_iff H.nodup_names

@[simp]
theorem Builtin.get?_namesMap {b : Builtin} : namesMap.get? b.name = some b := by
  simp [namesMap]; rw [Map.get?_ofList_of_nodup (by simp)]; simp
  rw [List.find?_eq_some_iff_of_at_most_one] <;> simp

@[simp]
theorem Builtin.get!_namesMap {b : Builtin} : namesMap.get! b.name = b := by
  simp [Map.get!_eq_get!_get?]

theorem Builtin.name_get!_namesMap_of_isBuiltin {name} (h : IsBuiltin name) :
(namesMap.get! name).name = name := by
  obtain ⟨b, rfl⟩ := h; simp

theorem WFDefs.isBuiltin_or {defs name d} (H : WFDefs defs)
(h : (builtinDefs ∪ .ofList defs).get? name = some d) :
IsBuiltin name ∨ (name, d) ∈ defs := by
  rw [or_iff_not_imp_left]
  intro h₂
  rw [Map.get?_union_right (by simpa)] at h
  rw [H.get?_ofList_defs] at h
  exact h

theorem WFDefs.hasDef {defs name d} (H : WFDefs defs)
(h : (builtinDefs ∪ .ofList defs).get? name = some d) :
(Prog.ofDefs defs).HasDef name := by
  have := H.isBuiltin_or h; simp; tauto

theorem Prog.def_eq_get!_def? {prog : Prog} {name} :
prog.def name = (prog.def? name).get! := by
  simp [Prog.def, Prog.def?, Map.get!_eq_get!_get?]

theorem Prog.def?_of_get? {defs name d}
(h : (builtinDefs ∪ .ofList defs).get? name = some d) :
(Prog.ofDefs defs).def? name = some d := by
  simpa [Prog.ofDefs]

theorem Prog.def_of_get? {defs name d}
(h : (builtinDefs ∪ .ofList defs).get? name = some d) :
(Prog.ofDefs defs).def name = d := by
  simp [Prog.def_eq_get!_def?, def?_of_get? h]

theorem Prog.arity_of_get? {defs name d}
(h : (builtinDefs ∪ .ofList defs).get? name = some d) :
(Prog.ofDefs defs).arity name = d.arity := by
  simp [arity, def_of_get? h]

theorem Prog.expr_of_get? {defs name d}
(h : (builtinDefs ∪ .ofList defs).get? name = some d) :
(Prog.ofDefs defs).expr name = d.expr := by
  simp [expr, def_of_get? h]

theorem WFDefs.get?_builtin {defs} {b : Builtin} (H : WFDefs defs) :
(builtinDefs ∪ .ofList defs).get? b.name = some b.def := by
  rw [Map.get?_union_left # by simp [H.not_mem_builtin]]; simp

theorem WFDefs.get?_of_mem_defs {defs} (H : WFDefs defs) {name d}
(h : (name, d) ∈ defs) : (builtinDefs ∪ .ofList defs).get? name = some d := by
  rw [Map.get?_union_right # by simp [H.not_isBuiltin_of_mem h]]
  rw [Map.get?_ofList_of_nodup H.nodup_names]
  simp; use name
  rw [List.find?_eq_some_iff_of_at_most_one]; grind
  rintro ⟨name₁, d₁⟩ ⟨name₂, d₂⟩ h₁ h₂
  simp
  rintro rfl rfl
  simp
  have h₃ := H.nodup_names
  rw [List.nodup_map_iff_inj_on # List.Nodup.of_map _ h₃] at h₃
  grind

theorem WFDefs.def?_builtin {defs} {b : Builtin} (H : WFDefs defs) :
(Prog.ofDefs defs).def? b.name = some b.def := by
  simp [Prog.ofDefs, H.get?_builtin]

theorem WFDefs.def_builtin {defs} {b : Builtin} (H : WFDefs defs) :
(Prog.ofDefs defs).def b.name = b.def := by
  simp [Prog.def_eq_get!_def?, H.def?_builtin]

theorem WFDefs.arity_builtin {defs} {b : Builtin} (H : WFDefs defs) :
(Prog.ofDefs defs).arity b.name = b.arity := by
  simp [Prog.arity, H.def_builtin]

theorem WFDefs.expr_builtin {defs} {b : Builtin} (H : WFDefs defs) :
(Prog.ofDefs defs).expr b.name = b.expr := by
  simp [Prog.expr, H.def_builtin]

theorem WFDefs.def?_of_mem_defs {defs name d} (H : WFDefs defs)
(h : (name, d) ∈ defs) : (Prog.ofDefs defs).def? name = some d :=
  H.get?_of_mem_defs h

theorem WFDefs.def_of_mem_defs {defs name d} (H : WFDefs defs)
(h : (name, d) ∈ defs) : (Prog.ofDefs defs).def name = d := by
  simp [Prog.def_eq_get!_def?, H.def?_of_mem_defs h]

theorem WFDefs.arity_of_mem_defs {defs name d} (H : WFDefs defs)
(h : (name, d) ∈ defs) : (Prog.ofDefs defs).arity name = d.arity := by
  simp [Prog.arity, H.def_of_mem_defs h]

theorem WFDefs.expr_of_mem_defs {defs name d} (H : WFDefs defs)
(h : (name, d) ∈ defs) : (Prog.ofDefs defs).expr name = d.expr := by
  simp [Prog.expr, H.def_of_mem_defs h]

@[simp]
theorem mem_builtinFS {name} : name ∈ builtinFs ↔ IsBuiltin name := by
  simp [builtinFs, IsBuiltin]

theorem WFDefs.builtin_not_mem_defs {defs} {b : Builtin} {d}
(H : WFDefs defs) : (b.name, d) ∉ defs := by
  intro h; replace h := H.not_isBuiltin_of_mem h; simp at h

@[simp]
theorem Builtin.get?_builtinFs {b : Builtin} : builtinFs.get? b.name = some b.eval := by
  simp [builtinFs]; rw [Map.get?_ofList_eq_some_iff] <;> simp

@[simp]
theorem Builtin.get!_builtinFs {b : Builtin} : builtinFs.get! b.name = b.eval := by
  simp [Map.get!_eq_get!_get?]

theorem Builtin.eval_of_ne_arity {b : Builtin} {xs}
(h : xs.length ≠ b.arity) : b.eval xs = 0 := by
  simp at h ⊢; simp [Builtin.eval, fn, h]

theorem CompatibleDefs.get?_builtin {defs fs} {b : Builtin} (H : WFDefs defs)
(H₁ : CompatibleDefs (.ofList defs) fs) : (builtinFs ∪ fs).get? b.name = some b.eval := by
  have h₃ := H₁.keys_fs; simp at h₃
  rw [Map.get?_union_left]; simp
  simp [h₃]; intro d; apply H.builtin_not_mem_defs

theorem CompatibleDefs.get!_builtin {defs fs} {b : Builtin} (H : WFDefs defs)
(H₁ : CompatibleDefs (.ofList defs) fs) : (builtinFs ∪ fs).get! b.name = b.eval := by
  simp [Map.get!_eq_get!_get?, H₁.get?_builtin H]

@[simp]
theorem Builtin.eval_mkList {b : Builtin} {xs} :
b.eval (mkList b.arity (xs[·]!)) = b.info.eval xs := by
  simp [eval, fn]; cases b <;> simp [Builtin.info]

@[simp]
theorem get?_builtinFs_eq_some {name f} : builtinFs.get? name = some f ↔
∃ (b : Builtin), b.name = name ∧ b.eval = f := by
  simp [builtinFs, Map.get?_ofList_eq_some_iff]

theorem Prog.WF.def_builtin  {prog : Prog} {b : Builtin} [H : prog.WF] :
prog.def b.name = b.def := by
  simp [def_eq_get!_def?, H.def?_builtin]

@[simp]
theorem Builtin.name_ne_mainName {b : Builtin} : b.name ≠ mainName := by
  cases b <;> decide

@[simp]
theorem Builtin.mainName_ne_name {b : Builtin} : mainName ≠ b.name :=
  ne_symm' b.name_ne_mainName

-- #check 0 #exit

-- theorem Prog.Compatible.get?_builtin_ofDefs {defs} {b : Builtin} {fs}
-- (H₁ : (Prog.ofDefs defs).Compatible fs) : fs.get? b.name = some b.eval := by
--   have h₁ := @H₁.eval_eq b.name
--   specialize @h₁ (by simp) (mkList b.arity id) _
--   ·
--     clear h₁
--     cases H
--     simp [arity, H.def_builtin]

-- #check 0 #exit

-- theorem Prog.Compatible.builtinFs_union {defs fs} (H : (Prog.ofDefs defs).WF)
-- (H₁ : (Prog.ofDefs defs).Compatible fs) : fs ∪ builtinFs = fs := by
--   rw [Map.union_eq_self_left_iff]
--   intro name f h
--   simp at h
--   obtain ⟨b, rfl, rfl⟩ := h
--   exact H₁.get?_builtin H

example : ¬∀ {defs} (H : WFDefs defs),
∃! fs, (Prog.ofDefs defs).Compatible fs := by
  simp [not_exiu_iff]
  use [(mainName, ⟨1, exprId⟩)]
  split_ands
  ·
    constructor <;> simp
    use .ofList [(mainName, fn 1 (·[0]!))]
    simp
    split_ands
    ·
      constructor <;> simp [Map.get?_insert, Map.get!_eq_get!_get?, fn, exprId]
    ·
      intro fs
      rintro ⟨h₁, h₂, h₃⟩
      simp [Map.get?_insert, Map.get!_eq_get!_get?, exprId] at h₁ h₂ h₃
      simp [Map.ext_iff, Map.get?_insert]
      intro name
      rw! (castMode := .all) [eq_comm (a := mainName)]
      split_ifs with h₄
      rotate_left
      ·
        simp [←h₁] at h₄
        simpa
      subst h₄
      specialize h₁ mainName
      simp at h₁
      rw [Map.mem_iff_get?_eq_some] at h₁
      choose f h₁ using h₁
      ext xs
      simp [h₁]
      unfold fn
      simp
      revert xs
      simp
      ext xs
      split_ifs with h₄
      ·
        specialize h₃ h₄
        simp [h₁] at h₃
        rw [h₃]
      ·
        specialize h₂ h₄
        simp [h₁] at h₂
        rw [h₂]
  
  intro fs h
  use fs.insert Builtin.succ.name # fn 1 # λ xs =>
    fs.get! Builtin.succ.name xs + 1
  split_ands
  ·
    obtain ⟨h₂, h₃, h₄⟩ := h
    simp at h₂ h₃ h₄
    constructor <;> simp
    ·
      intro name
      simp [h₂]
      rintro rfl
      simp
    ·
      rintro name (⟨b, rfl⟩ | rfl) xs h
      ·
        specialize @h₃ b.name (by simp) xs h
        simp [Prog.arity, Prog.ofDefs, Map.get!_insert] at h
        simp [Map.get!_insert]
        split_ifs with h₅
        · subst h₅
          simp at h
          simp [fn, h]
        · exact h₃
      ·
        simp [Map.get!_insert]
        exact h₃ (by simp) h
    ·
      rintro name (⟨b, rfl⟩ | rfl) xs h
      ·
        simp [Map.get!_insert, Prog.expr, Prog.ofDefs] at h ⊢
        split_ifs with h₅
        ·
          subst h₅
          simp at h
          simp [fn, h, Builtin.expr, Expr.eval, Map.get!_insert]
          rw [←h]; simp
        ·
          simp [Builtin.expr, Expr.eval, Map.get!_insert, h₅, ←h]
      ·
        specialize @h₄ mainName (by simp) xs h
        simp [Map.get!_insert, Prog.expr, Prog.ofDefs] at h ⊢
        simp [exprId]
        rw [h₄]
        simp [Prog.ofDefs, Map.get!_insert, exprId]
  
  ·
    apply ne_of_congr (·.get! Builtin.succ.name)
    simp [Map.get!_insert, funext_iff]
    use [0]
    simp [fn]

#check 0 #exit

theorem WFDefs.compatible_fs {defs} (H : WFDefs defs) :
∃! fs, (Prog.ofDefs defs).Compatible fs := by
  obtain ⟨fs, H₁, H₂⟩ := H.exiu_compatible
  dsimp at H₂
  use builtinFs ∪ fs
  dsimp; split_ands
  · constructor
    ·
      simp
      intro name h₁
      have h₂ := H₁.keys_fs
      simp at h₂
      apply h₂
    · intro name h₁ xs h₂
      simp at h₁
      have h₃ := H₁.keys_fs
      simp at h₃
      specialize h₃ name
      rw [←h₃] at h₁
      rcases h₁ with ⟨b, rfl⟩ | h₁
      · rw [H₁.get!_builtin H]
        rw [H.arity_builtin] at h₂
        exact b.eval_of_ne_arity h₂
      rw [h₃] at h₁
      choose d h₁ using h₁
      rw [H.arity_of_mem_defs h₁] at h₂
      have h₄ := @H₁.eval_of_ne_arity name
      specialize @h₄ d _ xs h₂
      · rwa [Map.get?_ofList_eq_some_iff H.nodup_names]
      rwa [Map.get!_union_right]
      simp [H.not_isBuiltin_of_mem h₁]
    ·
      intro name h₁ xs h₂
      simp at h₁
      have h₃ := H₁.keys_fs
      simp at h₃
      rcases h₁ with ⟨b, rfl⟩ | ⟨d, h₁⟩
      ·
        rw [H₁.get!_builtin H]
        simp [H.arity_builtin] at h₂
        simp [H.expr_builtin, Builtin.eval, fn, h₂, Builtin.expr, Expr.eval]
        simp [H₁.get!_builtin H]
      rw [Map.get!_union_right # by simp [H.not_isBuiltin_of_mem h₁]]
      rw [H.expr_of_mem_defs h₁]
      rw [H.arity_of_mem_defs h₁] at h₂
      have h₄ := @H₁.eval_eq
      specialize @h₄ name d _ xs h₂
      · rwa [Map.get?_ofList_eq_some_iff H.nodup_names]
      convert h₄
      simp [Prog.ext_iff]
  ·
    intro fs' h₁
    specialize H₂ (fs' \ builtinFs) _
    ·
      sorry
    subst H₂
    symm; simp [Map.union_eq_self_left_iff]
    rintro name b rfl
    have h₂ := @h₁.eval_eq
    specialize @h₂ b.name (by simp) (mkList b.arity id) _
    ·
      clear h₂
      simp

#check 0 #exit

    -- constructor
    -- · simp [H₁.keys_fs]
    -- · intro name h₁ xs h₂
    --   simp at h₁; rcases h₁ with ⟨b, rfl⟩ | ⟨d, h₁⟩
    --   · apply H₁.eval_of_ne_arity (d := b.def) H.get?_builtin
    --     contrapose! h₂
    --     rw [h₂, Prog.arity_of_get? H.get?_builtin]
    --   have h₃ := H.get?_of_mem_defs h₁
    --   apply H₁.eval_of_ne_arity h₃
    --   contrapose! h₂
    --   rw [h₂, Prog.arity_of_get? h₃]
    -- · intro name h₁ xs h₂
    --   simp at h₁; rcases h₁ with ⟨b, rfl⟩ | ⟨d, h₁⟩
    --   · have h₃ := @H₁.eval_eq b.name b.def H.get?_builtin xs
    --     simp [Prog.arity_of_get? H.get?_builtin] at h₂
    --     simp [h₂] at h₃
    --     simp [H.expr_builtin]
    --     convert h₃
    --     simp [Prog.ext_iff]
    --   simp [H.expr_of_mem_defs h₁]
    --   simp [H.arity_of_mem_defs h₁] at h₂
    --   convert @H₁.eval_eq name d (H.get?_of_mem_defs h₁) xs h₂
    --   simp [Prog.ext_iff]

#check 0 #exit

theorem WFDefs.wf {defs} (H : WFDefs defs) : (Prog.ofDefs defs).WF := by
  constructor
  · intro b
    simp [Prog.ofDefs]
    rw [Map.get?_union_left]; simp
    simp [H.not_mem_of_isBuiltin]
  · simp; grind [H.wf_main]
  · obtain ⟨d, h₁, h₂⟩ := H.wf_main
    have h₃ := H.nodup_names
    simp [Map.get!_ofList_of_nodup h₃]
    unfold Option.map
    split
    · nm a x h; clear a
      rw [List.nodup_map_iff_inj_on # List.Nodup.of_map _ h₃] at h₃
      rw [List.find?_eq_some_iff_of_at_most_one] at h
      rotate_left
      · rintro ⟨name₁, d₁⟩ ⟨name₂, d₂⟩ h₄ h₅
        simp
        rintro rfl rfl
        simp
        grind
      simp at h ⊢
      obtain ⟨d₁, h₄⟩ := H.wf_main
      rcases x with ⟨name, x⟩
      dsimp at *
      rcases h with ⟨h, rfl⟩
      grind
    · grind
  · intro name d h₁
    have h := @H.wf_def name d
    simp [Prog.ofDefs] at h₁
    by_cases h₂ : IsBuiltin name
    · clear h
      have h₀ := λ d => H.not_mem_of_isBuiltin h₂ (d := d)
      rw [Map.get?_union_left # by simp [h₀]] at h₁
      simp at h₁
      obtain ⟨b, rfl, rfl⟩ := h₁
      simp [Def.WF]
      use b.def
      simp [Prog.ofDefs]
      rw [Map.get?_union_left # by simp [h₀]]
      simp
    rw [Map.get?_union_right (by simpa)] at h₁
    rw [Map.get?_ofList_of_nodup H.nodup_names] at h₁
    simp at h₁
    choose d' h₁ using h₁
    have h₃ := H.nodup_names
    rw [List.nodup_map_iff_inj_on # List.Nodup.of_map _ h₃] at h₃
    rw [List.find?_eq_some_iff_of_at_most_one] at h₁; grind
    rintro ⟨name₁, d₁⟩ ⟨name₂, d₂⟩ h₄ h₅
    simp
    rintro rfl rfl
    simp
    grind
  · exact H.compatible_fs

theorem wf_of_wfDefs {defs} (H : WFDefs defs) : (Prog.ofDefs defs).WF := H.wf

@[simp, instance]
theorem wf_progId : progId.WF := by
  apply wf_of_wfDefs
  constructor <;> try simp
  use .ofList [(mainName, fn 1 λ xs => xs[0]!)]
  split_ands
  ·
    dsimp
    constructor
    ·
      simp

#check 0 #exit

@[simp]
theorem Expr.run_call {prog fs args t xs} : (Expr.call t xs).eval prog fs args =
t.f fs (xs.map λ x => x.eval prog fs args) := by
  simp [eval]

theorem not_wf_progLoop : ¬progLoop.WF := by
  unfold progLoop exprLoop
  rintro ⟨-, -, -, h⟩; contrapose! h; clear h
  rw [not_exiu_iff_or]; right
  use [fn 1 λ _ => 0], [fn 1 λ _ => 1]; unfold fn
  simp; split_ands <;> try constructor <;> simp
  apply ne_of_congr (· [0]); simp

@[simp]
theorem Prog.compatible_fs {prog : Prog} [H : prog.WF] : prog.Compatible prog.fs :=
  τ_spec H.exiu_compatible.exists

@[simp]
theorem eval_exprId {prog fs xs} : exprId.eval prog fs xs = xs[0]! := by
  simp [exprId]

@[simp]
theorem run_progId {n} : progId.run n = n := by
  simp [Prog.run, Prog.eval]; have h := @progId.compatible_fs.eval_eq
  simp at h; specialize @h [n]; simpa using h

@[simp]
theorem Prog.hasTarget_builtin {prog : Prog} {bn} : prog.HasTarget (.builtin bn) := trivial

@[simp]
theorem Prog.hasTarget_custom {prog : Prog} {i} :
prog.HasTarget (.custom i) ↔ i < prog.defs.length := by rfl

@[simp] theorem Target.arity_builtin {bn} : arity (builtin bn) = bn.arity := rfl
@[simp] theorem Target.f_builtin_succ {bn fs} : f (.builtin bn) fs = bn.f := rfl
@[simp] theorem Builtin.f_succ : f .succ = (·[0]! + 1) := rfl
@[simp] theorem Builtin.f_sub : f .sub = (λ xs => xs[0]! - xs[1]!) := rfl

@[simp]
theorem Expr.wf_call {prog t args n} : (call t args).WF prog n ↔ prog.HasTarget t ∧
args.length = t.arity prog ∧ ∀ e ∈ args, e.WF prog n := by
  simp [WF]

theorem Prog.fs_eq_of_compatible {prog : Prog} {fs} [hp : prog.WF]
(h : prog.Compatible fs) : prog.fs = fs :=
  hp.exiu_compatible.unique prog.compatible_fs h

instance {prog : Prog} {i} : Decidable # prog.HasDef i := by
  unfold Prog.HasDef; infer_instance

instance {prog : Prog} {t} : Decidable # prog.HasTarget t := by
  unfold Prog.HasTarget; cases t <;> infer_instance