import Projects.Esolangs.Cornucopia.Defs

attribute [-simp] List.getElem!_eq_getElem?_getD

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

theorem CompatibleDefs.get?_builtin {defs fs} (H : WFDefs defs)
(H₁ : CompatibleDefs (.ofList defs) fs) (b : Builtin) :
(builtinFs ∪ fs).get? b.name = some b.eval := by
  have h₃ := H₁.keys_fs; simp at h₃
  rw [Map.get?_union_left]; simp
  simp [h₃]; intro d; apply H.builtin_not_mem_defs

theorem CompatibleDefs.get!_builtin {defs fs} (H : WFDefs defs)
(H₁ : CompatibleDefs (.ofList defs) fs) (b : Builtin) :
(builtinFs ∪ fs).get! b.name = b.eval := by
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

theorem Prog.Compatible.builtinFs_union {defs fs}
(H : (Prog.ofDefs defs).Compatible fs) : fs ∪ builtinFs = fs := by
  rw [Map.union_eq_self_left_iff]
  intro name f h
  simp at h
  obtain ⟨b, rfl, rfl⟩ := h
  exact H.get?_builtin

theorem WFDefs.get?_fs_of_mem_defs {defs fs name d} (H : WFDefs defs)
(h : (name, d) ∈ defs) : (builtinFs ∪ fs).get? name = fs.get? name := by
  simp [Map.get?_union_right, H.not_isBuiltin_of_mem h]

theorem WFDefs.get!_fs_of_mem_defs {defs fs name d} (H : WFDefs defs)
(h : (name, d) ∈ defs) : (builtinFs ∪ fs).get! name = fs.get! name := by
  simp [Map.get!_eq_get!_get?, H.get?_fs_of_mem_defs h]

theorem WFDefs.get?_of_mem_defs' {defs} (H : WFDefs defs) {name d}
(h : (name, d) ∈ defs) : (Map.ofList defs).get? name = some d := by
  rwa [Map.get?_ofList_eq_some_iff H.nodup_names]

theorem WFDefs.toList_defs {defs} (H : WFDefs defs) :
(Map.ofList defs).toList = defs.mergeSort (·.1 ≤ ·.1) :=
  Map.toList_ofList H.nodup_names

theorem Prog.Compatible.union_builtinFs {prog : Prog} {fs}
(H : prog.Compatible fs) : fs ∪ builtinFs = fs := by
  have h₁ := @H.get?_builtin
  ext name : 1
  rw [Map.get?_union_ite]
  simp
  rintro ⟨b, rfl⟩
  simp [h₁]

theorem Prog.Compatible.fs_eq_union {prog : Prog} {fs} (H : prog.Compatible fs) :
∃ fs', fs = builtinFs ∪ fs' ∧ ∀ (b : Builtin), b.name ∉ fs' := by
  use fs \ builtinFs; simp [H.union_builtinFs]

theorem CompatibleDefs.builtin_not_mem {defs fs} (H : WFDefs defs)
(H₁ : CompatibleDefs (.ofList defs) fs) (b : Builtin) : b.name ∉ fs := by
  have h₁ := congrArg (b.name ∈ ·) H₁.keys_fs
  simp at h₁; simp [h₁]; intro d; exact H.not_mem_builtin

@[simp] theorem Builtin.eval_succ : Builtin.succ.eval = fn 1 (·[0]! + 1) := rfl
@[simp] theorem Builtin.eval_sub : Builtin.sub.eval = fn 2 (λ xs => xs[0]! - xs[1]!) := rfl

theorem WFDefs.compatible_fs_aux₁ {defs fs} (H : WFDefs defs)
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
    have h₄ := @H₁.eval_of_ne_arity name
    specialize @h₄ d (H.get?_of_mem_defs' h₁) xs h₂
    rwa [Map.get!_union_right]
    simp [H.not_isBuiltin_of_mem h₁]
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
      have h₄ := @H₁.eval_eq
      rw [H.arity_of_mem_defs h₁] at h₂
      specialize @h₄ name d (H.get?_of_mem_defs' h₁) xs h₂
      rw [h₄]; clear h₄
      congr 1
      simp [Prog.ofDefs]

theorem WFDefs.compatible_fs_aux₂ {defs fs'} (H : WFDefs defs)
(H₂ : (Prog.ofDefs defs).Compatible (builtinFs ∪ fs'))
(h : ∀ (b : Builtin), b.name ∉ fs') :
CompatibleDefs (.ofList defs) fs' := by
  constructor
  · have h₁ := H₂.keys_fs
    simp [IsBuiltin] at h₁
    simp
    intro name
    specialize h₁ name
    use by grind
    rintro ⟨d, h₂⟩
    specialize h₁ _
    · rintro b rfl
      replace h₂ := H.not_isBuiltin_of_mem h₂
      simp at h₂
    grind
  · intro name d h₁ xs h₂
    rw [Map.get?_ofList_eq_some_iff H.nodup_names] at h₁
    have h₃ := @H₂.eval_of_ne_arity
    specialize @h₃ name (by simp; tauto) xs (by simpa [H.arity_of_mem_defs h₁])
    rwa [Map.get!_union_right # by simp [H.not_isBuiltin_of_mem h₁]] at h₃
  · intro name d h₁ xs h₂
    rw [Map.get?_ofList_eq_some_iff H.nodup_names] at h₁
    have h₃ := @H₂.eval_eq
    specialize @h₃ name (by simp; tauto) xs (by simpa [H.arity_of_mem_defs h₁])
    rw [Map.get!_union_right # by simp [H.not_isBuiltin_of_mem h₁]] at h₃
    rw [h₃]; clear h₃
    simp [H.expr_of_mem_defs h₁]
    congr 1

theorem WFDefs.compatible_fs {defs} (H : WFDefs defs) :
∃! fs, (Prog.ofDefs defs).Compatible fs := by
  obtain ⟨fs, H₁, H₂⟩ := H.exiu_compatible
  dsimp at H₂
  use builtinFs ∪ fs
  use H.compatible_fs_aux₁ H₁
  intro fs' h
  obtain ⟨fs', rfl, h₁⟩ := h.fs_eq_union
  rw [Map.union_eq_union_iff_right # by simpa [IsBuiltin]]
  rotate_left
  · simp [IsBuiltin]; exact H₁.builtin_not_mem H
  apply H₂; exact H.compatible_fs_aux₂ h h₁

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

-- example : ¬∀ {defs} (H : WFDefs defs),
-- ∃! fs, (Prog.ofDefs defs).Compatible fs := by
--   simp [not_exiu_iff]
--   use [(mainName, ⟨1, exprId⟩)]
--   split_ands
--   ·
--     constructor <;> simp
--     use .ofList [(mainName, fn 1 (·[0]!))]
--     simp
--     split_ands
--     ·
--       constructor <;> simp [Map.get?_insert, Map.get!_eq_get!_get?, fn, exprId]
--     ·
--       intro fs
--       rintro ⟨h₁, h₂, h₃⟩
--       simp [Map.get?_insert, Map.get!_eq_get!_get?, exprId] at h₁ h₂ h₃
--       simp [Map.ext_iff, Map.get?_insert]
--       intro name
--       rw! (castMode := .all) [eq_comm (a := mainName)]
--       split_ifs with h₄
--       rotate_left
--       ·
--         simp [←h₁] at h₄
--         simpa
--       subst h₄
--       specialize h₁ mainName
--       simp at h₁
--       rw [Map.mem_iff_get?_eq_some] at h₁
--       choose f h₁ using h₁
--       ext xs
--       simp [h₁]
--       unfold fn
--       simp
--       revert xs
--       simp
--       ext xs
--       split_ifs with h₄
--       ·
--         specialize h₃ h₄
--         simp [h₁] at h₃
--         rw [h₃]
--       ·
--         specialize h₂ h₄
--         simp [h₁] at h₂
--         rw [h₂]

-----
-----
-----

-- def exprId : Expr :=
--   .arg 0
-- 
-- def exprLoop (name : String) : Expr :=
--   .call name [.arg 0]
-- 
-- def progId : Prog :=
--   .ofDefs [(mainName, ⟨1, exprId⟩)]
-- 
-- def progLoop : Prog :=
--   .ofDefs [(mainName, ⟨1, exprLoop mainName⟩)]

-- @[simp]
-- theorem main_progId : progId.main = ⟨1, exprId⟩ := by
--   simp [progId, Map.get!_insert]
-- 
-- @[simp]
-- theorem main_progLoop : progLoop.main = ⟨1, exprLoop mainName⟩ := by
--   simp [progLoop, Map.get!_insert]
-- 
-- @[simp] theorem wf_exprId {prog} : exprId.WF prog 1 := by simp [Expr.WF, exprId]
-- @[simp] theorem wf_defId : (Def.mk 1 (.arg 0)).WF progId := wf_exprId

-- theorem not_wf_progLoop : ¬progLoop.WF := by
--   unfold progLoop exprLoop
--   rintro ⟨-, -, -, h⟩; contrapose! h; clear h
--   rw [not_exiu_iff_or]; right
--   use [fn 1 λ _ => 0], [fn 1 λ _ => 1]; unfold fn
--   simp; split_ands <;> try constructor <;> simp
--   apply ne_of_congr (· [0]); simp
-- 
-- @[simp]
-- theorem eval_exprId {prog fs xs} : exprId.eval prog fs xs = xs[0]! := by
--   simp [exprId]
-- 
-- @[simp]
-- theorem run_progId {n} : progId.run n = n := by
--   simp [Prog.run, Prog.eval]; have h := @progId.compatible_fs.eval_eq
--   simp at h; specialize @h [n]; simpa using h

-- @[simp, instance]
-- theorem wf_progId : progId.WF := by
--   apply wf_of_wfDefs
--   constructor <;> try simp
--   use .ofList [(mainName, fn 1 λ xs => xs[0]!)]
--   split_ands
--   ·
--     dsimp
--     constructor
--     ·
--       simp