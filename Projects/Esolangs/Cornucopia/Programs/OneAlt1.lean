import Projects.Esolangs.Cornucopia.Programs.Common

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia.OneAlt₁

def exprOneAlt : Expr :=
  .call subName
  [ .call succName [.call "1" []]
  , .call "1" []
  ]

def defOneAlt : Def :=
  ⟨0, exprOneAlt⟩

def defMain : Def :=
  ⟨1, .call "1" []⟩

def defs : List (String × Def) :=
  [ (mainName, defMain)
  , ("1", defOneAlt)
  ]

def fs : List (String × (List ℕ → ℕ)) :=
  [ (mainName, fn 1 λ _ => 1)
  , ("1", fn 0 λ _ => 1)
  ]

def fsMap : Map String (List ℕ → ℕ) :=
  builtinFs ∪ .ofList fs

def prog : Prog :=
  .ofDefs defs

-- #check 0 #exit

-----

@[simp]
theorem nodup_defs : defs.map (·.1) |>.Nodup := by
  decide

@[simp]
theorem nodup_fs : fs.map (·.1) |>.Nodup := by
  decide

@[instance, simp]
theorem wfBuiltins_prog : prog.WFBuiltins := by
  apply Prog.wfBuiltins_ofDefs; decide

@[simp] theorem arity_oneAlt : defOneAlt.arity = 0 := rfl

-- #check 0 #exit

@[simp]
theorem hasDef_prog_iff {name} : prog.HasDef name ↔ IsBuiltin name ∨ defs.any (·.1 = name) := by
  simp [prog]

@[simp]
theorem def?_oneAlt : prog.def? "1" = some defOneAlt := by
  simp [prog]; rw [Prog.def?_ofDefs (by simp)]; simp [defs, mainName]

-- #check 0 #exit

@[simp]
theorem wfDefs' : WFDefs' defs := by
  use nodup_defs
  · simp [defs]; decide
  · simp [defs, defMain]
  intro name d
  rw [←prog]
  simp [defs]
  revert name d
  simp [defOneAlt, exprOneAlt, defs, Prog.arity, Prog.def_eq_get!_def?, defMain]

-- #check 0 #exit

@[instance, simp]
theorem wf' : prog.WF' :=
  wfDefs'.wf'

@[simp]
theorem union_fs : builtinFs ∪ .ofList fs = fsMap := rfl

theorem builtin_not_name_of_mem_fs {name₁ name d} [H : BuiltinC name₁]
(h : (name, d) ∈ fs) : name₁ ≠ name := by
  replace h : name ∈ Map.ofList fs; simp; tauto
  clear d; simp [fs] at h; revert name; simp
  obtain ⟨⟨⟩, rfl⟩ := H <;> decide

theorem get!_fsMap {name} : fsMap.get! name = match fs.find? (·.1 = name) with
| .some p => p.2 | .none => builtinFs.get! name := by
  split
  · nm x p h; clear x
    rcases p with ⟨name₁, d⟩
    simp [List.find?_eq_some_iff_of_nodup] at h
    rcases h with ⟨h₁, rfl⟩
    unfold fsMap
    rw [Map.get!_union_right # by simp [isBuiltin_iff, builtin_not_name_of_mem_fs h₁]]
    rw [Map.get!_eq_get!_get?, Map.get?_ofList_of_nodup_and_mem (by simp) h₁]
    rfl
  · nm x h; clear x
    simp at h ⊢
    unfold fsMap
    rw [Map.get!_union_left]
    simp; grind

@[simp]
theorem not_builtin_mem_fs {name f} [H : BuiltinC name] : (name, f) ∉ fs := by
  obtain ⟨b, rfl⟩ := H
  suffices h : fs.map (·.1) |>.all (isBuiltin · = false)
  · simp at h
    intro h₁
    specialize h _ _ h₁
    have h₂ : IsBuiltin b.name; simp
    rw [isBuiltin_iff_decide] at h₂
    grind
  unfold isBuiltin builtins; simp [fs]; decide

@[simp]
theorem get!_fsMap_builtin {name} [H : BuiltinC name] : fsMap.get! name = H.b.eval := by
  rw [fsMap, Map.get!_union_left (by simp)]; simp

@[simp]
theorem get!_fsMap_oneAlt : fsMap.get! "1" = fn 0 (λ _ => 1) := by
  simp [get!_fsMap, fs, mainName]

-- #check 0 #exit

@[simp]
theorem compatibleDefs : CompatibleDefs (.ofList defs) (.ofList fs) := by
  use by simp [defs, fs, ExiVarC.exi_iff]
  intro name d
  rw [Prog.eq_ofDefs, ←prog]
  intro h
  rw [Map.get?_ofList_eq_some_iff (by simp)] at h
  simp [defs] at h
  revert name d
  simp [Map.get?_ofList_eq_some_iff]
  simp [fs, mainName]
  simp [defOneAlt, exprOneAlt, defMain, fn]

-- #check 0 #exit

@[simp]
theorem compatible : prog.Compatible fsMap :=
  wfDefs'.compatible compatibleDefs

theorem fs₁_get!_of {fs₁ name} (h : CompatibleDefs (.ofList defs) fs₁)
(d : Def) (h₁ : (name, d) ∈ defs)
(h₂ : ∀ f, (Map.ofList defs).get! name = d → (builtinFs ∪ fs₁).get! name = f →
fs₁.get? name = some (fn d.arity (d.expr.eval prog (builtinFs ∪ fs₁))) →
fs₁.get? name = some f → f = fn d.arity (d.expr.eval prog (builtinFs ∪ fs₁)) →
fn d.arity f = Map.get! name (Map.ofList fs)) :
(builtinFs ∪ fs₁).get! name = Map.get! name (Map.ofList fs) := by
  have h₃ : (Map.ofList defs).get? name = d
  · rwa [Map.get?_ofList_eq_some_iff (by simp)]
  obtain ⟨f, h₄⟩ : ∃ f, fs₁.get? name = some f
  · rw [←Map.mem_iff_get?_eq_some]
    have h₄ := congrArg (name ∈ ·) h.keys_fs
    simp at h₄
    tauto
  have h₅ : (builtinFs ∪ fs₁).get? name = some f
  · rwa [Map.get?_union_right # by simp [wfDefs'.not_isBuiltin_of_mem h₁]]
  have h₆ := h.get?_eq' h₃
  simp [h₄] at h₆
  rw [←Prog.ofDefs, ←prog] at h₆
  rw [Map.get!_eq_get!_get?, h₅]; dsimp
  rw [←h₂ f]; simp [h₆]
  · exact Map.get!_ofList_of_nodup_and_mem (by simp) h₁
  · simp [Map.get!_eq_get!_get?, h₅]
  · simpa [h₄]
  · exact h₄
  · exact h₆

@[simp]
theorem get!_defs_main : (Map.ofList defs).get! mainName = defMain := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_defs_oneAlt : (Map.ofList defs).get! "1" = defOneAlt := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

-- #check 0 #exit

@[simp]
theorem get!_fs_main : (Map.ofList fs).get! mainName = fn 1 (λ _ => 1) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_fs_oneAlt : (Map.ofList fs).get! "1" = fn 0 (λ _ => 1) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

-- #check 0 #exit

theorem fs₁_get?_builtin {fs₁ name} [H : BuiltinC name]
(h : CompatibleDefs (.ofList defs) fs₁) : (builtinFs ∪ fs₁).get? name = some H.b.eval := by
  simp [h.get?_builtin]

theorem fs₁_get?_main {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? mainName = some (fn 1 # defMain.expr.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) mainName defMain (by simp [defs])]; rw [←Prog.ofDefs, ←prog]; rfl

theorem fs₁_get?_oneAlt {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? "1" = some (fn 0 # exprOneAlt.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) "1" defOneAlt (by simp [defs])]; rw [←Prog.ofDefs, ←prog]; rfl

-- #check 0 #exit

theorem fs₁_get!_builtin {fs₁ name} [H : BuiltinC name]
(h : CompatibleDefs (.ofList defs) fs₁) : (builtinFs ∪ fs₁).get! name = H.b.eval := by
  rw [Map.get!_union_left]; simp
  intro h₁
  have h₂ := congrArg (H.b.name ∈ ·) h.keys_fs
  simp [h₁] at h₂
  choose d h₂ using h₂
  have h₃ := wfDefs'.not_isBuiltin_of_mem h₂
  simp at h₃

theorem fs₁_get!_oneAlt {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! "1" = (Map.ofList fs).get! "1" := by
  apply fs₁_get!_of h defOneAlt (by simp [defs])
  intro f h₁ h₂ h₃ h₄ h₅
  simp [h₂, h₄, fn, funext_iff, defOneAlt, exprOneAlt, fs₁_get!_builtin h, fn] at h₃
  have h₆ := forall_imp_of_forall (λ (xs : List _) => xs.length = 0) h₃
  simp at h₆; clear h₁ h₂ h₃ h₄ h₅; rename' h₆ => h₁
  ext xs; simp [fn]; grind

theorem fs₁_get!_main {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! mainName = (Map.ofList fs).get! mainName := by
  rw [Map.get!_union_right # by simp]
  rw [Map.get!_eq_get!_get?, fs₁_get?_main h]; simp
  simp [defMain, fs₁_get!_oneAlt h, fn]

-- #check 0 #exit

@[instance, simp]
theorem wf_prog : prog.WF := by
  apply wfDefs'.wf; use .ofList fs, compatibleDefs
  intro fs₁ h name d f h₂ h₃
  have h₅ := h.eval_eq h₂ |>.symm
  rw [←Prog.ofDefs, ←prog] at h₅
  simp [h₃] at h₅
  subst h₅
  simp [funext_iff]
  intro xs
  simp [defs] at h₂
  revert h₃
  revert name d h₂
  revert xs
  simp [fs₁_get?_main h, fn, defMain, fs₁_get?_oneAlt h, fs₁_get!_oneAlt h,
    exprOneAlt, fs₁_get!_builtin h]
    
-- #check 0 #exit

instance : ProgInfo prog where
  name := "OneAlt₁"
  defNames := ["main", "1"]
  has_model := true
  has_unique_model := true
  h_defNames := by
    dsimp [prog, Prog.ofDefs]
    rw [Map.keys_union # by simp [isBuiltin_iff, Builtin.all, defs, mainName, succName, subName]]
    simp only [builtinDefs, List.map_map, Function.comp_def, nodup_map_name_builtins,
      Map.keys_ofList, nodup_defs, List.mergeSort_perm_iff, List.append_mergeSort_perm,
      List.mergeSort_append_perm, List.perm_append_left_iff]
    simp [defs]; decide
  h_wf' := by simp
  h_has_model := by
    simp [Prog.HasModel]; use prog.fs; apply τ_spec; use builtinFs ∪ .ofList fs; simp
  h_has_unique_model := by have := wf_prog.exiu_compatible; simp [Prog.HasUniqueModel]; tauto