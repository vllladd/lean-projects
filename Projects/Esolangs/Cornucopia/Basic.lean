import Projects.Esolangs.Cornucopia.Show

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia

structure CompatibleDefs (defs : Map String Def) (fs : Map String (List ℕ → ℕ)) : Prop where
  keys_fs : fs.keys = defs.keys
  get?_eq' ⦃name d⦄ : defs.get? name = some d → fs.get? name = some (fn d.arity #
    d.expr.eval ⟨builtinDefs ∪ .ofList defs.toList⟩ (builtinFs ∪ fs))

structure CompatibleDefsAlt₁ (defs : Map String Def) (fs : Map String (List ℕ → ℕ)) : Prop where
  keys_fs : fs.keys = defs.keys
  eval_of_ne_arity ⦃name d⦄ : defs.get? name = some d → ∀ ⦃xs : List ℕ⦄,
    xs.length ≠ d.arity → fs.get! name xs = 0
  eval_eq ⦃name d⦄ : defs.get? name = some d → ∀ ⦃xs : List ℕ⦄,
    xs.length = d.arity → fs.get! name xs = d.expr.eval
    ⟨builtinDefs ∪ .ofList defs.toList⟩ (builtinFs ∪ fs) xs

structure WFDefs' (defs : List (String × Def)) : Prop where
  nodup_names : defs.map (·.1) |>.Nodup
  not_isBuiltin_of_mem ⦃name d⦄ : (name, d) ∈ defs → ¬IsBuiltin name
  wf_main : ∃ d, (mainName, d) ∈ defs ∧ d.arity = 1
  wf_def ⦃name d⦄ : (name, d) ∈ defs → d.WF (Prog.ofDefs defs)

def CompatibleCnd (defs : List (String × Def)) (fs : Map String (List ℕ → ℕ)) : Prop :=
  CompatibleDefs (.ofList defs) fs ∧ ∀ fs', CompatibleDefs (.ofList defs) fs' →
  ∀ name d f, (name, d) ∈ defs → fs'.get? name = some f → fs.get! name = f

structure WFDefs defs extends WFDefs' defs where
  compatible : ∃ fs, CompatibleCnd defs fs

def isBuiltin (name : String) : Bool :=
  builtins.any (·.name = name)

def findBuiltin (name : String) : Builtin :=
  builtins.find? (·.name = name) |>.get!

def Expr.decideEq : Expr → Expr → Bool
| .arg i, .arg j => i == j
| .call name₁ es₁, .call name₂ es₂ =>
  name₁ == name₂ && es₁.length = es₂.length &&
  (es₁.zip es₂).attach.all λ ⟨⟨x, y⟩, _h⟩ => x.decideEq y
| _, _ => false
termination_by a _ => a
decreasing_by
  rename' _h => h; simp [List.mem_zip_iff] at h
  obtain ⟨i, ⟨h₁, rfl⟩, h₂, rfl⟩ := h; simp
  induction es₁ generalizing i <;> grind

-- #check 0 #exit

-----

attribute [simp] BuiltinC.name_eq

theorem isBuiltin_iff {name} : IsBuiltin name ↔ ∃ (b : Builtin), b.name = name :=
  ⟨(·.1), (⟨·⟩)⟩

@[simp]
theorem mem_builtins {b} : b ∈ builtins := by
  cases b <;> decide

instance {name} : Decidable (IsBuiltin name) :=
  decidable_of_bool (isBuiltin name) # by simp [isBuiltin_iff, isBuiltin]

-- #check 0 #exit

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
  simp [builtinDefs, isBuiltin_iff]

@[simp]
theorem mem_builtinFs {name} : name ∈ builtinFs ↔ IsBuiltin name := by
  simp [builtinFs, isBuiltin_iff]

@[simp]
theorem not_isBuiltin_mainName : ¬IsBuiltin mainName := by
  decide

theorem Prog.def_ofDefs {xs name} (h : ¬IsBuiltin name) :
(Prog.ofDefs xs).def name = (Map.ofList xs).get! name := by
  simp [ofDefs]; rw [Map.get!_union_right]; simpa using h

theorem arity_ofDefs {defs name} (h : ¬IsBuiltin name) :
(Prog.ofDefs defs).arity name = ((Map.ofList defs).get! name).arity := by
  simp [Prog.arity, Prog.def_ofDefs h]

@[simp]
theorem BuiltinC.name_ne_mainName {name} [h : BuiltinC name] : name ≠ mainName := by
  obtain ⟨⟨⟩, rfl⟩ := h <;> decide

@[simp]
theorem BuiltinC.mainName_ne_name {name} [h : BuiltinC name] : mainName ≠ name :=
  ne_symm' h.name_ne_mainName

@[instance, simp]
instance {b : Builtin} : BuiltinC b.name where
  b := b
  name_eq := rfl

@[simp]
theorem Prog.main_ofDefs {xs} : (Prog.ofDefs xs).main = (Map.ofList xs).get! mainName := by
  simp [ofDefs]; rw [Map.get!_union_right]; simp

@[simp]
theorem Expr.run_arg {i prog f args} : (arg i).eval prog f args = args[i]! := by
  simp [eval]

@[simp]
theorem Expr.wf_arg {prog n i} : (arg i).WF prog n ↔ i < n := by
  simp [WF]

@[simp]
theorem nodup_builtins : builtins.Nodup := by
  decide

@[simp]
theorem nodup_map_name_builtins : (builtins.map Builtin.name).Nodup := by
  decide

@[simp]
theorem IsBuiltin.get?_builtinDefs {name} [h : BuiltinC name] :
builtinDefs.get? name = some h.b.def := by
  simp [builtinDefs, Map.get?_ofList_eq_some_iff]; use h.b; simp

@[simp]
theorem Builtin.ext_name {b₁ b₂ : Builtin} : b₁.name = b₂.name ↔ b₁ = b₂ := by
  rcases b₁, b₂ with ⟨⟨⟩, ⟨⟩⟩ <;> decide

@[simp] theorem Builtin.arity_def {b : Builtin} : b.def.arity = b.arity := rfl
@[simp] theorem Builtin.expr_def {b : Builtin} : b.def.expr = b.expr := rfl

@[simp]
theorem Builtin.ext_def {b₁ b₂ : Builtin} : b₁.def = b₂.def ↔ b₁ = b₂ := by
  rcases b₁, b₂ with ⟨⟨⟩, ⟨⟩⟩ <;> simp [Def.ext_iff]

@[simp]
theorem BuiltinC_builtin_of_name {b : Builtin} [h : BuiltinC b.name] : h.b = b := by
  obtain ⟨b, h⟩ := h; simpa using h

@[simp]
theorem Builtin.get!_builtinDefs {b : Builtin} : builtinDefs.get! b.name = b.def := by
  simp [Map.get!_eq_get!_get?]

theorem def?_ofDefs_builtin_eq_of {defs} {b : Builtin}
(h : ∀ d ∈ defs, ¬IsBuiltin d.1) : (Prog.ofDefs defs).def? b.name = some b.def := by
  simp [Prog.ofDefs]; rw [Map.get?_union_left]; simp
  simp; intro d h₁; specialize h _ h₁; simp [isBuiltin_iff] at h

@[simp]
theorem Prog.defs_ofDefs {defs} : (Prog.ofDefs defs).defs = builtinDefs ∪ .ofList defs := rfl

@[simp]
theorem Prog.hasDef_ofDefs {defs name} :
(Prog.ofDefs defs).HasDef name ↔ IsBuiltin name ∨ name ∈ Map.ofList defs := by
  simp [HasDef]

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

theorem WFDefs'.builtin_not_mem {defs name d} (H : WFDefs' defs)
[h : BuiltinC name] : (name, d) ∉ defs := by
  obtain ⟨b, rfl⟩ := h
  have h₁ := H.not_isBuiltin_of_mem
  simp [isBuiltin_iff] at h₁; grind

theorem WFDefs'.get?_ofList_defs {defs name d} (H : WFDefs' defs) :
(Map.ofList defs).get? name = some d ↔ (name, d) ∈ defs :=
  Map.get?_ofList_eq_some_iff H.nodup_names

@[simp]
theorem Builtin.get?_namesMap {b : Builtin} : namesMap.get? b.name = some b := by
  simp [namesMap]; rw [Map.get?_ofList_of_nodup (by simp)]; simp
  rw [List.find?_eq_some_iff_of_at_most_one] <;> simp

@[simp]
theorem Builtin.get!_namesMap {b : Builtin} : namesMap.get! b.name = b := by
  simp [Map.get!_eq_get!_get?]

theorem Builtin.builtin_get!_namesMap {name} [h : BuiltinC name] :
(namesMap.get! name).name = name := by
  obtain ⟨b, rfl⟩ := h; simp

theorem WFDefs'.isBuiltin_or {defs name d} (H : WFDefs' defs)
(h : (builtinDefs ∪ .ofList defs).get? name = some d) :
IsBuiltin name ∨ (name, d) ∈ defs := by
  rw [or_iff_not_imp_left]
  intro h₂; simp [isBuiltin_iff] at h₂
  rw [Map.get?_union_right (by simpa [isBuiltin_iff])] at h
  rw [H.get?_ofList_defs] at h
  exact h

theorem WFDefs'.hasDef {defs name d} (H : WFDefs' defs)
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

theorem WFDefs'.not_mem_builtinDefs {defs name d} (H : WFDefs' defs)
(h : (name, d) ∈ defs) : name ∉ builtinDefs := by
  simp [isBuiltin_iff]; rintro b rfl; simp [H.builtin_not_mem] at h

theorem WFDefs'.not_mem_builtinFs {defs name d} (H : WFDefs' defs)
(h : (name, d) ∈ defs) : name ∉ builtinFs := by
  simp [isBuiltin_iff]; rintro b rfl; simp [H.builtin_not_mem] at h

theorem WFDefs'.get?_builtin {defs} {b : Builtin} (H : WFDefs' defs) :
(builtinDefs ∪ .ofList defs).get? b.name = some b.def := by
  rw [Map.get?_union_left # by simp [H.builtin_not_mem]]; simp

theorem WFDefs'.get?_of_mem_defs {defs} (H : WFDefs' defs) {name d}
(h : (name, d) ∈ defs) : (builtinDefs ∪ .ofList defs).get? name = some d := by
  rw [Map.get?_union_right # H.not_mem_builtinDefs h]
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

theorem WFDefs'.def?_builtin {defs} {b : Builtin} (H : WFDefs' defs) :
(Prog.ofDefs defs).def? b.name = some b.def := by
  simp [Prog.ofDefs, H.get?_builtin]

theorem WFDefs'.def_builtin {defs} {b : Builtin} (H : WFDefs' defs) :
(Prog.ofDefs defs).def b.name = b.def := by
  simp [Prog.def_eq_get!_def?, H.def?_builtin]

theorem WFDefs'.arity_builtin {defs} {b : Builtin} (H : WFDefs' defs) :
(Prog.ofDefs defs).arity b.name = b.arity := by
  simp [Prog.arity, H.def_builtin]

theorem WFDefs'.expr_builtin {defs} {b : Builtin} (H : WFDefs' defs) :
(Prog.ofDefs defs).expr b.name = b.expr := by
  simp [Prog.expr, H.def_builtin]

theorem WFDefs'.def?_of_mem_defs {defs name d} (H : WFDefs' defs)
(h : (name, d) ∈ defs) : (Prog.ofDefs defs).def? name = some d :=
  H.get?_of_mem_defs h

theorem WFDefs'.def_of_mem_defs {defs name d} (H : WFDefs' defs)
(h : (name, d) ∈ defs) : (Prog.ofDefs defs).def name = d := by
  simp [Prog.def_eq_get!_def?, H.def?_of_mem_defs h]

theorem WFDefs'.arity_of_mem_defs {defs name d} (H : WFDefs' defs)
(h : (name, d) ∈ defs) : (Prog.ofDefs defs).arity name = d.arity := by
  simp [Prog.arity, H.def_of_mem_defs h]

theorem WFDefs'.expr_of_mem_defs {defs name d} (H : WFDefs' defs)
(h : (name, d) ∈ defs) : (Prog.ofDefs defs).expr name = d.expr := by
  simp [Prog.expr, H.def_of_mem_defs h]

@[simp]
theorem mem_builtinFS {name} : name ∈ builtinFs ↔ IsBuiltin name := by
  simp [builtinFs, isBuiltin_iff]

theorem WFDefs'.builtin_not_mem_defs {defs} {b : Builtin} {d}
(H : WFDefs' defs) : (b.name, d) ∉ defs := by
  intro h; replace h := H.not_isBuiltin_of_mem h; simp [isBuiltin_iff] at h

theorem Builtin.eval_of_ne_arity {b : Builtin} {xs}
(h : xs.length ≠ b.arity) : b.eval xs = 0 := by
  simp at h ⊢; simp [Builtin.eval, fn, h]

theorem compatibleDefs_iff_alt₁ {defs fs} :
CompatibleDefs defs fs ↔ CompatibleDefsAlt₁ defs fs := by
  constructor
  · rintro ⟨h₁, h₂⟩
    use h₁
    all_goals
      intro name d h₃ xs h₄
      specialize @h₂ name d h₃
      simp [Map.get!_eq_get!_get?] at h₂ ⊢
      rw [h₂]
      simp [fn, h₄]
  · rintro ⟨h₁, h₂, h₃⟩
    simp [Map.get!_eq_get!_get?] at h₂ h₃ ⊢
    use h₁
    intro name d h₄
    simp
    obtain ⟨f, h₅⟩ : ∃ f, fs.get? name = some f
    · simp [Map.mem_iff_get?_eq_some] at h₁; simp [h₁, h₄]
    specialize h₂ h₄
    specialize h₃ h₄
    simp [h₅] at h₂ h₃ ⊢
    ext; simp [fn]; grind

theorem CompatibleDefs.alt₁ {defs fs}
(h : CompatibleDefs defs fs) : CompatibleDefsAlt₁ defs fs :=
  compatibleDefs_iff_alt₁.mp h

@[simp]
theorem Builtin.get?_builtinFs {name} [h : BuiltinC name] :
builtinFs.get? name = some h.b.eval := by
  obtain ⟨b, rfl⟩ := h; simp [builtinFs]; rw [Map.get?_ofList_eq_some_iff] <;> simp

@[simp]
theorem Builtin.get!_builtinFs {name} [h : BuiltinC name] :
builtinFs.get! name = h.b.eval := by
  simp [Map.get!_eq_get!_get?]

theorem CompatibleDefs.get?_builtin {defs fs name} [H₀ : BuiltinC name] (H : WFDefs' defs)
(H₁ : CompatibleDefs (.ofList defs) fs) :
(builtinFs ∪ fs).get? name = some H₀.b.eval := by
  obtain ⟨b, rfl⟩ := H₀
  have h₃ := H₁.keys_fs; simp at h₃
  rw [Map.get?_union_left]; simp
  simp [h₃]; intro d; apply H.builtin_not_mem_defs

theorem CompatibleDefs.get!_builtin {defs fs name} [H₀ : BuiltinC name] (H : WFDefs' defs)
(H₁ : CompatibleDefs (.ofList defs) fs) :
(builtinFs ∪ fs).get! name = H₀.b.eval := by
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

theorem Prog.Compatible.builtinFs_union {defs fs}
(H : (Prog.ofDefs defs).Compatible fs) : fs ∪ builtinFs = fs := by
  rw [Map.union_eq_self_left_iff]
  intro name f h
  simp at h
  obtain ⟨b, rfl, rfl⟩ := h
  apply H.get?_builtin'

theorem WFDefs'.get?_fs_of_mem_defs {defs fs name d} (H : WFDefs' defs)
(h : (name, d) ∈ defs) : (builtinFs ∪ fs).get? name = fs.get? name := by
  simp only [mem_builtinFS, H.not_isBuiltin_of_mem h, not_false_eq_true, Map.get?_union_right]

theorem WFDefs'.get!_fs_of_mem_defs {defs fs name d} (H : WFDefs' defs)
(h : (name, d) ∈ defs) : (builtinFs ∪ fs).get! name = fs.get! name := by
  simp [Map.get!_eq_get!_get?, H.get?_fs_of_mem_defs h]

theorem WFDefs'.get?_of_mem_defs' {defs} (H : WFDefs' defs) {name d}
(h : (name, d) ∈ defs) : (Map.ofList defs).get? name = some d := by
  rwa [Map.get?_ofList_eq_some_iff H.nodup_names]

theorem WFDefs'.toList_defs {defs} (H : WFDefs' defs) :
(Map.ofList defs).toList = defs.mergeSort (·.1 ≤ ·.1) :=
  Map.toList_ofList H.nodup_names

theorem Prog.Compatible.union_builtinFs {prog : Prog} {fs}
(H : prog.Compatible fs) : fs ∪ builtinFs = fs := by
  have h₁ := @H.get?_builtin'
  ext name : 1
  rw [Map.get?_union_ite]
  simp [isBuiltin_iff]
  rintro b rfl
  simp [h₁]

theorem Prog.Compatible.fs_eq_union {prog : Prog} {fs} (H : prog.Compatible fs) :
∃ fs', fs = builtinFs ∪ fs' ∧ ∀ (b : Builtin), b.name ∉ fs' := by
  use fs \ builtinFs; simp [H.union_builtinFs, isBuiltin_iff]

theorem CompatibleDefs.builtin_not_mem {defs fs} (H : WFDefs' defs)
(H₁ : CompatibleDefs (.ofList defs) fs) (b : Builtin) : b.name ∉ fs := by
  have h₁ := congrArg (b.name ∈ ·) H₁.keys_fs
  simp at h₁; simp [h₁]; intro d; exact H.builtin_not_mem

@[simp] theorem Builtin.eval_succ : Builtin.succ.eval = fn 1 (·[0]! + 1) := rfl
@[simp] theorem Builtin.eval_sub : Builtin.sub.eval = fn 2 (λ xs => xs[0]! - xs[1]!) := rfl

theorem WFDefs'.compatible_fs_aux₁ {defs fs} (H : WFDefs' defs)
(H₁ : CompatibleDefs (Map.ofList defs) fs) :
(Prog.ofDefs defs).Compatible (builtinFs ∪ fs) := by
  constructor
  · simp
    intro name h₁
    have h₂ := H₁.keys_fs
    simp at h₂
    apply h₂
  · intro b; simp [H₁.get?_builtin H]
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
    have h₄ := @H₁.alt₁.eval_of_ne_arity name
    specialize @h₄ d (H.get?_of_mem_defs' h₁) xs h₂
    rwa [Map.get!_union_right # H.not_mem_builtinFs h₁]
  · intro name h₁ xs h₂
    simp at h₁
    have h₃ := H₁.keys_fs
    simp at h₃
    rcases h₁ with ⟨b, rfl⟩ | ⟨d, h₁⟩
    · rw [H₁.get!_builtin H]
      simp [H.arity_builtin] at h₂
      rw [H.expr_builtin]
      simp [Builtin.eval, fn, h₂, Builtin.expr, Expr.eval, H₁.get!_builtin H]
      simp [←h₂]
    · symm
      rw [H.get!_fs_of_mem_defs h₁, H.expr_of_mem_defs h₁]
      have h₄ := @H₁.alt₁.eval_eq
      rw [H.arity_of_mem_defs h₁] at h₂
      specialize @h₄ name d (H.get?_of_mem_defs' h₁) xs h₂
      rw [h₄]; clear h₄
      congr 1
      simp [Prog.ofDefs]

theorem WFDefs'.compatible_fs_aux₂ {defs fs'} (H : WFDefs' defs)
(H₂ : (Prog.ofDefs defs).Compatible (builtinFs ∪ fs'))
(h : ∀ (b : Builtin), b.name ∉ fs') :
CompatibleDefs (.ofList defs) fs' := by
  rw [compatibleDefs_iff_alt₁]; constructor
  · have h₁ := H₂.keys_fs
    simp [isBuiltin_iff] at h₁
    simp
    intro name
    specialize h₁ name
    use by grind
    rintro ⟨d, h₂⟩
    specialize h₁ _
    · rintro b rfl
      replace h₂ := H.not_isBuiltin_of_mem h₂
      simp [isBuiltin_iff] at h₂
    grind
  · intro name d h₁ xs h₂
    rw [Map.get?_ofList_eq_some_iff H.nodup_names] at h₁
    have h₃ := @H₂.eval_of_ne_arity
    specialize @h₃ name (by simp; tauto) xs (by simpa [H.arity_of_mem_defs h₁])
    rwa [Map.get!_union_right # H.not_mem_builtinFs h₁] at h₃
  · intro name d h₁ xs h₂
    rw [Map.get?_ofList_eq_some_iff H.nodup_names] at h₁
    have h₃ := @H₂.eval_eq
    specialize @h₃ name (by simp; tauto) xs (by simpa [H.arity_of_mem_defs h₁])
    rw [Map.get!_union_right # H.not_mem_builtinFs h₁] at h₃
    rw [h₃]; clear h₃
    simp [H.expr_of_mem_defs h₁]
    congr 1

theorem CompatibleDefs.exi_mem_defs_of_get? {defs fs name f}
(H : CompatibleDefs (.ofList defs) fs)
(h : fs.get? name = some f) : ∃ d, (name, d) ∈ defs := by
  have h₁ := H.keys_fs; simp at h₁
  replace h := Map.mem_of_get?_eq_some h
  simpa [h₁] using h

theorem CompatibleDefs.exi_get?_defs_of_get? {defs fs name f}
(H : CompatibleDefs defs fs)
(h : fs.get? name = some f) : ∃ d, defs.get? name = some d := by
  have h₁ := H.keys_fs; simp at h₁
  replace h := Map.mem_of_get?_eq_some h
  rw [h₁] at h; simpa [Map.mem_iff_get?_eq_some] using h

theorem WFDefs.exiu_compatible {defs} (H : WFDefs defs) :
∃! fs, CompatibleDefs (.ofList defs) fs := by
  obtain ⟨fs, h₁, h₂⟩ := H.compatible
  use fs, h₁
  intro fs' h₃
  ext name f
  have h₄ : fs.keys = fs'.keys
  · grind [h₁.keys_fs, h₃.keys_fs]
  simp [Map.mem_iff_get?_eq_some] at h₄
  specialize h₄ name
  simp [Map.get!_eq_get!_get?] at h₂
  constructor <;> intro h₅ <;> simp [h₅] at h₄
  · rename' f => f'
    choose f h₄ using h₄
    specialize h₂ fs' h₃ name (Map.ofList defs |>.get? name |>.get!) f'
    simp [h₄]; choose d h₆ using h₁.exi_get?_defs_of_get? h₄
    grind [h₂ # by simp [←H.get?_ofList_defs, h₆]]
  · choose f' h₄ using h₄
    specialize h₂ fs' h₃ name (Map.ofList defs |>.get? name |>.get!) f'
    simp [h₄]
    choose d h₆ using h₁.exi_get?_defs_of_get? h₅
    grind [h₂ # by simp [←H.get?_ofList_defs, h₆]]

theorem WFDefs.compatible_fs {defs} (H : WFDefs defs) :
∃! fs, (Prog.ofDefs defs).Compatible fs := by
  obtain ⟨fs, H₁, H₂⟩ := H.exiu_compatible
  dsimp at H₂
  use builtinFs ∪ fs
  use H.compatible_fs_aux₁ H₁
  intro fs' h
  obtain ⟨fs', rfl, h₁⟩ := h.fs_eq_union
  rw [Map.union_eq_union_iff_right # by simpa [isBuiltin_iff]]
  rotate_left
  · simp [isBuiltin_iff]; exact H₁.builtin_not_mem H.toWFDefs'
  apply H₂; exact H.compatible_fs_aux₂ h h₁

@[simp]
theorem IsBuiltin.name_findBuiltin {name} [h : IsBuiltin name] :
(findBuiltin name).name = name := by
  obtain ⟨b, h⟩ := h
  unfold findBuiltin Option.get!
  split
  rotate_left
  · nm x h₁; clear x
    simp at h₁
    specialize h₁ b
    contradiction
  nm x b' h₁; clear x
  rw [List.find?_eq_some_iff_of_at_most_one] at h₁
  rotate_left
  · simp
    rintro b₁ b₂ rfl
    simp [eq_comm]
  simpa using h₁

@[simp]
instance BuiltinC.isBuiltin {name} [h : BuiltinC name] : IsBuiltin name where
  h := ⟨h.b, by simp⟩

instance IsBuiltin.BuiltinC {name} [h : IsBuiltin name] : BuiltinC name where
  b := findBuiltin name
  name_eq := h.name_findBuiltin

theorem WFDefs'.wf' {defs} (H : WFDefs' defs) : (Prog.ofDefs defs).WF' := by
  have : (Prog.ofDefs defs).WFBuiltins
  · constructor
    intro b
    simp [Prog.ofDefs]
    rw [Map.get?_union_left]; simp
    simp [H.builtin_not_mem]
  constructor
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
      have h₀ := λ d => H.builtin_not_mem (name := name) (d := d)
      rw [Map.get?_union_left # by simp [h₀]] at h₁
      simp at h₁
      obtain ⟨b, rfl, rfl⟩ := h₁
      simp [Def.WF]
      obtain ⟨b, rfl⟩ := h₂
      use b.def
      simp [Prog.ofDefs]
      rw [Map.get?_union_left # by simp [h₀]]
      simp
    rw [Map.get?_union_right (by simpa using h₂)] at h₁
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

theorem WFDefs.wf {defs} (H : WFDefs defs) : (Prog.ofDefs defs).WF := by
  haveI := H.wf'; constructor; exact H.compatible_fs

@[simp]
theorem Expr.run_call {prog fs args t xs} : (Expr.call t xs).eval prog fs args =
fs.get! t (xs.map λ x => x.eval prog fs args) := by
  simp [eval]

@[simp]
theorem Prog.compatible_fs {prog : Prog} [H : prog.WF] : prog.Compatible prog.fs :=
  τ_spec H.exiu_compatible.exists

@[simp]
theorem Expr.wf_call {prog t args n} : (call t args).WF prog n ↔ prog.HasDef t ∧
args.length = prog.arity t ∧ ∀ e ∈ args, e.WF prog n := by
  simp [WF]

theorem Prog.fs_eq_of_compatible {prog : Prog} {fs} [hp : prog.WF]
(h : prog.Compatible fs) : prog.fs = fs :=
  hp.exiu_compatible.unique prog.compatible_fs h

instance {prog : Prog} {i} : Decidable # prog.HasDef i := by
  unfold Prog.HasDef; infer_instance

instance {prog : Prog} {t} : Decidable # prog.HasDef t := by
  unfold Prog.HasDef; infer_instance

@[simp]
theorem fn_eq_fn_iff {n f g} : fn n f = fn n g ↔
∀ (xs : List ℕ), xs.length = n → f xs = g xs := by
  simp [funext_iff, fn]

theorem CompatibleDefs.eval_eq {defs : List (String × Def)} {fs name d}
(H : CompatibleDefs (.ofList defs) fs) (h : (name, d) ∈ defs)
(hh : defs.map (·.1) |>.Nodup := by simp) : fs.get? name = some (fn d.arity #
  d.expr.eval ⟨builtinDefs ∪ .ofList defs⟩ (builtinFs ∪ fs)) := by
  have h₁ := @H.get?_eq' name d # by rwa [Map.get?_ofList_eq_some_iff hh]
  convert h₁ using 3; simp

theorem WFDefs'.compatible {defs fs} (H : WFDefs' defs)
(H₁ : CompatibleDefs (Map.ofList defs) fs) :
(Prog.ofDefs defs).Compatible (builtinFs ∪ fs) :=
  H.compatible_fs_aux₁ H₁

theorem WFDefs'.wfDefs {defs} (H : WFDefs' defs)
(h : ∃ fs, CompatibleCnd defs fs) : WFDefs defs where
  toWFDefs' := H
  compatible := h

theorem WFDefs'.wf {defs} (H : WFDefs' defs)
(h : ∃ fs, CompatibleCnd defs fs) : (Prog.ofDefs defs).WF :=
  H.wfDefs h |>.wf

instance BuiltinC.succ : BuiltinC succName := ⟨Builtin.succ, rfl⟩
instance BuiltinC.sub : BuiltinC subName := ⟨.sub, rfl⟩

instance BuiltinC.succ_lit : BuiltinC "succ" := ⟨Builtin.succ, rfl⟩
instance BuiltinC.sub_lit : BuiltinC "sub" := ⟨.sub, rfl⟩

@[simp]
theorem BuiltinC.b_succ [h : BuiltinC succName] : h.b = .succ := by
  obtain ⟨b', h⟩ := h; change b' = _; rw [←Builtin.ext_name, h]; rfl

@[simp]
theorem BuiltinC.b_sub [h : BuiltinC subName] : h.b = .sub := by
  obtain ⟨b', h⟩ := h; change b' = _; rw [←Builtin.ext_name, h]; rfl

@[simp]
theorem BuiltinC.b_succ_lit [h : BuiltinC "succ"] : h.b = .succ := by
  obtain ⟨b', h⟩ := h; change b' = _; rw [←Builtin.ext_name, h]; rfl

@[simp]
theorem BuiltinC.b_sub_lit [h : BuiltinC "sub"] : h.b = .sub := by
  obtain ⟨b', h⟩ := h; change b' = _; rw [←Builtin.ext_name, h]; rfl

@[simp]
theorem BuiltinC.exi_eq_name {name} [h : BuiltinC name] :
∃ (b : Builtin), b.name = name := ⟨_, h.name_eq⟩

@[simp]
theorem BuiltinC.not_forall_ne_name {name} [h : BuiltinC name] :
¬∀ (b : Builtin), b.name ≠ name := by simp

@[simp] theorem Builtin.name_succ : Builtin.succ.name = succName := rfl
@[simp] theorem Builtin.name_sub : Builtin.sub.name = subName := rfl

@[simp] theorem subName_ne_succName : subName ≠ succName := by decide
@[simp] theorem succName_ne_subName : succName ≠ subName := by decide

@[simp]
theorem Builtin.name_eq_succName {b : Builtin} : b.name = succName ↔ b = .succ := by
  rw [←ext_name]; rfl

@[simp]
theorem Builtin.name_eq_subName {b : Builtin} : b.name = subName ↔ b = .sub := by
  rw [←ext_name]; rfl

@[simp]
theorem BuiltinC.builtin_succName [h : BuiltinC succName] : h.b = .succ := by
  obtain ⟨b', h⟩ := h; change b' = _; simpa using h

@[simp]
theorem BuiltinC.builtin_subName [h : BuiltinC subName] : h.b = .sub := by
  obtain ⟨b', h⟩ := h; change b' = _; simpa using h

@[simp]
theorem get?_succName_builtinDefs : builtinDefs.get? succName = some Builtin.succ.def := by
  simp [builtinDefs, builtins, Map.ofList_eq_foldl, Map.get?_insert]

@[simp]
theorem get?_subName_builtinDefs : builtinDefs.get? subName = some Builtin.sub.def := by
  simp [builtinDefs, builtins, Map.ofList_eq_foldl, Map.get?_insert]

@[simp]
theorem get!_succName_builtinDefs : builtinDefs.get! succName = Builtin.succ.def := by
  simp [Map.get!_eq_get!_get?]

@[simp]
theorem get!_subName_builtinDefs : builtinDefs.get! subName = Builtin.sub.def := by
  simp [Map.get!_eq_get!_get?]

@[simp]
theorem Prog.arity_main {prog} [H : WF' prog] : prog.main.arity = 1 :=
  H.arity_main

@[simp]
theorem Prog.arity_mainName {prog} [H : WF' prog] : prog.arity mainName = 1 :=
  H.arity_main

@[simp]
theorem Prog.hasDef_mainName {prog} [H : WF' prog] : prog.HasDef mainName :=
  H.has_main

@[simp]
theorem Prog.Compatible.get?_builtin {prog : Prog} {fs name} [h : BuiltinC name]
(H : prog.Compatible fs) : fs.get? name = some h.b.eval := by
  simpa using @H.get?_builtin' h.b

@[simp]
theorem Prog.Compatible.get!_builtin {prog : Prog} {fs name} [h : BuiltinC name]
(H : prog.Compatible fs) : fs.get! name = h.b.eval := by
  simp [Map.get!_eq_get!_get?, H.get?_builtin]

theorem Prog.wfBuiltins_ofDefs {defs} (h : defs.all (·.1 ∉ builtins.map (·.name))) :
(Prog.ofDefs defs).WFBuiltins := by
  constructor
  intro b
  simp at h
  simp [ofDefs]
  rw [Map.get?_union_ite]
  split_ifs with h₁; on_goal 2 => simp
  rw [Map.mem_iff_get?_eq_some] at h₁
  choose d h₁ using h₁
  simp [h₁]
  cases h b.name d (Map.mem_of_get?_ofList h₁) b rfl

attribute [simp] Prog.WFBuiltins.def?_builtin

@[simp]
theorem Prog.WFBuiltins.hasDef_builtin {prog : Prog} {name}
[h₁ : prog.WFBuiltins] [h₂ : BuiltinC name] : prog.HasDef name := by
  rcases h₂ with ⟨b, rfl⟩; simp [HasDef, Map.mem_of_get?_eq_some # @h₁.1 b]

@[simp]
theorem Prog.WFBuiltins.mem_defs_builtin {prog : Prog} {name}
[h₁ : prog.WFBuiltins] [h₂ : BuiltinC name] : name ∈ prog.defs :=
  h₁.hasDef_builtin

@[simp]
theorem Prog.WFBuiltins.def?_builtin_eq {prog : Prog} {name}
[h₁ : prog.WFBuiltins] [h₂ : BuiltinC name] : prog.def? name = some h₂.b.def := by
  rcases h₂ with ⟨b, rfl⟩; simp

@[simp]
theorem Prog.WFBuiltins.def_builtin_eq {prog : Prog} {name}
[h₁ : prog.WFBuiltins] [h₂ : BuiltinC name] : prog.def name = h₂.b.def := by
  simp [def_eq_get!_def?]

@[simp]
theorem Prog.WFBuiltins.arity_builtin_eq {prog : Prog} {name}
[h₁ : prog.WFBuiltins] [h₂ : BuiltinC name] : prog.arity name = h₂.b.arity := by
  simp [arity]

@[simp]
theorem Prog.WFBuiltins.expr_builtin_eq {prog : Prog} {name}
[h₁ : prog.WFBuiltins] [h₂ : BuiltinC name] : prog.expr name = h₂.b.expr := by
  simp [expr]

theorem Prog.mem_defs_of_def? {prog : Prog} {name d}
(h : prog.def? name = some d) : name ∈ prog.defs :=
  Map.mem_of_get?_eq_some h

theorem Prog.hasDef_of_def? {prog : Prog} {name d}
(h : prog.def? name = some d) : prog.HasDef name :=
  mem_defs_of_def? h

theorem Prog.def_of_def? {prog : Prog} {name d}
(h : prog.def? name = some d) : prog.def name = d := by
  simp [Prog.def_eq_get!_def?, h]

theorem Prog.arity_of_def? {prog : Prog} {name d}
(h : prog.def? name = some d) : prog.arity name = d.arity := by
  simp [arity, def_of_def? h]

theorem Prog.expr_of_def? {prog : Prog} {name d}
(h : prog.def? name = some d) : prog.expr name = d.expr := by
  simp [expr, def_of_def? h]

theorem Expr.ind {p : Expr → Prop} (h₁ : ∀ i, p (.arg i))
(h₂ : ∀ name (es : List Expr), (∀ e ∈ es, p e) → p (.call name es)) : ∀ e, p e :=
  @Expr.rec p (λ es => ∀ e ∈ es, p e) h₁ h₂ (by simp) (by grind)

theorem Expr.eq_iff_decideEq {a b : Expr} : a = b ↔ a.decideEq b := by
  induction a using Expr.ind generalizing b
  · nm i; cases b <;> simp [decideEq]
  nm name₁ es₁ ih
  cases b <;> simp [decideEq]
  nm name₂ es₂
  simp [List.mem_zip_iff]
  use by grind
  rintro ⟨⟨rfl, h₁⟩, h₂⟩
  simp [List.ext_getElem_iff, h₁]
  intro i hi
  specialize h₂ es₁[i] es₂[i] i (by omega) rfl hi rfl
  rwa [←ih _ (by simp)] at h₂

instance : DecidableEq Expr :=
  λ _ _ => decidable_of_bool _ Expr.eq_iff_decideEq.symm

deriving instance DecidableEq for Def, Prog

theorem Builtin.all {p : Builtin → Prop} : (∀ b, p b) ↔ p .succ ∧ p .sub := by
  use by grind;; rintro h ⟨⟩ <;> tauto

theorem Builtin.exi {p : Builtin → Prop} : (∃ b, p b) ↔ p .succ ∨ p .sub := by
  contrapose!; simp [Builtin.all]

theorem Prog.def?_ofDefs {defs : List (String × Def)} {name} (h : defs.map (·.1) |>.Nodup) :
(Prog.ofDefs defs).def? name = (defs.find? (Prod.fst · = name) |>.map Prod.snd |>.or #
builtins.find? (·.name = name) |>.map Builtin.def) := by
  simp [ofDefs]
  rw [Map.get?_union_ite]
  symm; split_ifs with h₁
  · simp at h₁
    choose d h₁ using h₁
    rw [Map.get?_ofList_of_nodup_and_mem h h₁]
    simp
    left
    use name
    simpa [List.find?_eq_some_iff_of_nodup h]
  · rw [List.find?_eq_none_of (by simp at h₁ ⊢; grind)]
    simp
    ext d
    simp [List.find?_eq_some_iff_of_nodup nodup_map_name_builtins]

theorem Prog.eq_ofDefs {defs : List (String × Def)} :
(⟨builtinDefs ∪ .ofList (Map.ofList defs).toList⟩ : Prog) = .ofDefs defs := by
  simp [ofDefs]

theorem CompatibleDefs.get?_fs {defs fs name f} (H : WFDefs' defs)
(H₁ : CompatibleDefs (.ofList defs) fs) (h : fs.get? name = some f) :
(builtinFs ∪ fs).get? name = if IsBuiltin name then builtinFs.get? name else fs.get? name := by
  rw [Map.get?_union_ite]; simp [isBuiltin_iff]; split_ifs with h₃ h₄ h₄ <;> try rfl
  · obtain ⟨b, rfl⟩ := h₄; simp [H₁.builtin_not_mem H] at h₃
  · iterate 2 rw [Map.get?_eq_none_of_not_mem # by simp_all [isBuiltin_iff]]

theorem CompatibleDefs.get!_fs {defs fs name f} (H : WFDefs' defs)
(H₁ : CompatibleDefs (.ofList defs) fs) (h : fs.get? name = some f) :
(builtinFs ∪ fs).get! name = if IsBuiltin name then builtinFs.get! name else fs.get! name := by
  simp [Map.get!_eq_get!_get?, H₁.get?_fs H h, isBuiltin_iff]
  unfold Option.get!
  split; on_goal 2 => split <;> grind
  split; on_goal 2 => simp_all
  simp_all only [↓reduceIte, get?_builtinFs_eq_some]
  nm heq h_1 h_3 h_4
  simp_all only [Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq, Pi.default_def,
    Nat.default_eq_zero]
  obtain ⟨w, h_2⟩ := h_3
  obtain ⟨w_1, h_3⟩ := h_4
  obtain ⟨left, right⟩ := h_2
  subst h_3 right
  simp_all only [Builtin.ext_name, Builtin.get?_builtinFs, BuiltinC_builtin_of_name]

@[simp]
theorem sort_map_builtins : (builtins.map (·.name)).mergeSort = [subName, succName] := by
  simp [builtins, succName, subName]

@[simp]
theorem keys_builtinDefs : builtinDefs.keys = [subName, succName] := by
  simp [builtinDefs, Map.keys_ofList]

@[simp]
theorem keys_builtinFs : builtinFs.keys = [subName, succName] := by
  simp [builtinFs, Map.keys_ofList]

@[simp]
theorem fn_eq_fn_iff' {n f g xs} :
fn n f xs = fn n g xs ↔ xs.length = n → f xs = g xs := by
  simp [fn]

theorem Expr.wf_of_le {prog : Prog} {e : Expr} {k n}
(h₁ : e.WF prog k) (h₂ : k ≤ n) : e.WF prog n := by
  induction e using ind <;> simp at h₁ ⊢; omega; tauto

theorem isBuiltin_lit {name} : IsBuiltin name ↔ name = "succ" ∨ name = "sub" := by
  simp [isBuiltin_iff, Builtin.exi, succName, subName]; tauto

theorem isBuiltin_iff_decide {name} : IsBuiltin name ↔ isBuiltin name := by
  rw [show IsBuiltin name = (decide (IsBuiltin name) = true) by simp]
  rw [decide_decidable_of_bool_eq_true_eq]

theorem imp_fs_and_of {fs : Map String (List ℕ → ℕ)} {name}
{y z : List ℕ → ℕ} {p : List ℕ → Prop} {n}
(h₁ : fs.get? name = some (fn n y)) (h₂ : ∀ xs, xs.length = n → z xs = y xs)
(h₃ : (builtinFs ∪ fs).get! name = fn n z → ∀ xs, p xs)
(h₀ : ¬IsBuiltin name := by decide) :
∀ xs, (xs.length = n → fs.get? name = some (fn n y) → y xs = z xs) ∧ p xs := by
  intro xs; rw [Map.get!_union_right (by simpa)] at h₃
  simp [funext_iff, Map.get!_eq_get!_get?, h₁] at h₃; grind

@[simp]
theorem Builtin.forall_imp_iff {p : String → Prop} :
(∀ name, IsBuiltin name → p name) ↔ ∀ (b : Builtin), p b.name := by
  simp [isBuiltin_iff]

@[simp]
theorem Builtin.exists_and_iff {p : String → Prop} :
(∃ name, IsBuiltin name ∧ p name) ↔ ∃ (b : Builtin), p b.name := by
  simp [isBuiltin_iff]

@[simp high]
theorem fn_fn_same {f n} : fn n (fn n f) = fn n f := by
  ext; simp [fn]