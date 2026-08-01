import Projects.Esolangs.Cornucopia.Programs.Common

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia.Prog₁

def defNot : Def :=
  ⟨1, .call subName [one, .arg 0]⟩

def defBool : Def :=
  ⟨1, .call "not" [.call "not" [.arg 0]]⟩

def exprAdd : Expr :=
  .call subName
  [ .call subName
    [ .call subName
      [ .call succName [.call succName [
          .call "add"
            [ .call subName [.arg 0, one]
            , .call subName [.arg 1, one]
            ]
        ]]
      , .call "not" [.arg 0]
      ]
    , .call "not" [.arg 1]
    ]
  , .call "add" [zero, zero]
  ]

def defAdd : Def :=
  ⟨2, exprAdd⟩

def exprIte : Expr :=
  .call subName
  [ .call subName
    [ .call subName
      [ .call succName
        [ .call "ite"
          [ .arg 0
          , .call subName [.arg 1, one]
          , .call subName [.arg 2, one]
          ]
        ]
      , .call subName
        [ .call "bool" [.arg 0]
        , .arg 1
        ]
      ]
    , .call subName
      [ .call "not" [.arg 0]
      , .arg 2
      ]
    ]
  , .call "ite" [.arg 0, zero, zero]
  ]

def defIte : Def :=
  ⟨3, exprIte⟩

def defs : List (String × Def) :=
  [ (mainName, defId)
  , ("0", defZero)
  , ("1", defOne)
  , ("not", defNot)
  , ("bool", defBool)
  , ("add", defAdd)
  , ("ite", defIte)
  ]

def fs : List (String × (List ℕ → ℕ)) :=
  [ (mainName, fn 1 (·[0]!))
  , ("0", fn 0 λ _ => 0)
  , ("1", fn 0 λ _ => 1)
  , ("not", fn 1 λ xs => if xs[0]! = 0 then 1 else 0)
  , ("bool", fn 1 λ xs => if xs[0]! = 0 then 0 else 1)
  , ("add", fn 2 λ xs => xs[0]! + xs[1]!)
  , ("ite", fn 3 λ xs => if xs[0]! = 0 then xs[2]! else xs[1]!)
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

@[simp] theorem arity_defNot : defNot.arity = 1 := rfl
@[simp] theorem arity_defBool : defBool.arity = 1 := rfl
@[simp] theorem arity_defAdd : defAdd.arity = 2 := rfl
@[simp] theorem arity_defIte : defIte.arity = 3 := rfl

-- #check 0 #exit

@[simp]
theorem hasDef_prog_iff {name} : prog.HasDef name ↔ IsBuiltin name ∨ defs.any (·.1 = name) := by
  simp [prog]

@[simp]
theorem def?_zero : prog.def? "0" = some defZero := by
  simp [prog]; rw [Prog.def?_ofDefs (by simp)]; simp [defs, mainName]

@[simp]
theorem def?_one : prog.def? "1" = some defOne := by
  simp [prog]; rw [Prog.def?_ofDefs (by simp)]; simp [defs, mainName]

@[simp]
theorem def?_not : prog.def? "not" = some defNot := by
  simp [prog]; rw [Prog.def?_ofDefs (by simp)]; simp [defs, mainName]

@[simp]
theorem def?_bool : prog.def? "bool" = some defBool := by
  simp [prog]; rw [Prog.def?_ofDefs (by simp)]; simp [defs, mainName]

@[simp]
theorem def?_add : prog.def? "add" = some defAdd := by
  simp [prog]; rw [Prog.def?_ofDefs (by simp)]; simp [defs, mainName]

@[simp]
theorem def?_ite : prog.def? "ite" = some defIte := by
  simp [prog]; rw [Prog.def?_ofDefs (by simp)]; simp [defs, mainName]

-- #check 0 #exit

@[simp]
theorem wfDefs' : WFDefs' defs := by
  use nodup_defs
  · simp [defs]; decide
  · simp [defs]
  intro name d
  rw [←prog]
  simp [defs]
  revert name d
  simp
  have h_zero : ∀ k, zero.WF prog k := λ _ => wf_zero # by simp
  have h_one : ∀ k, one.WF prog k := λ _ => wf_one # by simp
  apply and_of
  · simp [exprZero, h_zero]
  intro h_zero'
  apply and_of
  · simp [exprOne, h_zero]
  intro h_one'
  apply and_of
  · simp [defNot, h_one]
  intro h_not
  apply and_of
  · simp [defBool, isBuiltin_lit, defs, Prog.arity, Prog.def_eq_get!_def?]
  intro h_bool
  apply and_of
  · simp [defAdd, exprAdd, isBuiltin_lit]
    simp [defs, Prog.arity, Prog.def_eq_get!_def?, h_zero, h_one]
  intro h_add
  apply And.left (b := True)
  apply and_of
  · simp [defIte, exprIte, isBuiltin_lit]
    simp [defs, Prog.arity, Prog.def_eq_get!_def?, h_zero, h_one]
  intro h_ite
  trivial

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
theorem get!_fsMap_zero : fsMap.get! "0" = fn 0 (λ _ => 0) := by
  simp [get!_fsMap, fs, mainName]

@[simp]
theorem get!_fsMap_one : fsMap.get! "1" = fn 0 (λ _ => 1) := by
  simp [get!_fsMap, fs, mainName]

@[simp]
theorem get!_fsMap_not : fsMap.get! "not" = fn 1 (λ xs => if xs[0]! = 0 then 1 else 0) := by
  simp [get!_fsMap, fs, mainName]

@[simp]
theorem get!_fsMap_bool : fsMap.get! "bool" = fn 1 (λ xs => if xs[0]! = 0 then 0 else 1) := by
  simp [get!_fsMap, fs, mainName]

@[simp]
theorem get!_fsMap_add : fsMap.get! "add" = fn 2 (λ xs => xs[0]! + xs[1]!) := by
  simp [get!_fsMap, fs, mainName]

@[simp]
theorem get!_fsMap_ite : fsMap.get! "ite" = fn 3 (λ xs =>
if xs[0]! = 0 then xs[2]! else xs[1]!) := by
  simp [get!_fsMap, fs, mainName]

-- #check 0 #exit

@[simp]
theorem eval_zero {xs} : zero.eval prog fsMap xs = 0 := by
  simp [zero, fn]

@[simp]
theorem eval_one {xs} : one.eval prog fsMap xs = 1 := by
  simp [one, fn]

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
  apply and_of
  · simp [exprId]
  intro h_main
  apply and_of
  · simp [exprZero, fn]
  intro h_zero
  apply and_of
  · simp [exprOne, fn]
  intro h_one
  apply and_of
  · simp [defNot, fn]; grind
  intro h_not
  apply and_of
  · simp [defBool, fn]
  intro h_bool
  apply and_of
  · intro a b; simp [defAdd, exprAdd, fn]; grind
  intro h_add
  apply And.left (b := True)
  apply and_of
  · intro a b; simp [defIte, exprIte, fn]; grind
  intro h_ite
  trivial

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
theorem get!_defs_main : (Map.ofList defs).get! mainName = ⟨1, exprId⟩ := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_defs_zero : (Map.ofList defs).get! "0" = defZero := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_defs_one : (Map.ofList defs).get! "1" = defOne := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_defs_not : (Map.ofList defs).get! "not" = defNot := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_defs_bool : (Map.ofList defs).get! "bool" = defBool := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_defs_add : (Map.ofList defs).get! "add" = defAdd := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_defs_ite : (Map.ofList defs).get! "ite" = defIte := by
  simp [defs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

-- #check 0 #exit

@[simp]
theorem get!_fs_main : (Map.ofList fs).get! mainName = fn 1 (·[0]!) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_fs_zero : (Map.ofList fs).get! "0" = fn 0 (λ _ => 0) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_fs_one : (Map.ofList fs).get! "1" = fn 0 (λ _ => 1) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_fs_not : (Map.ofList fs).get! "not" =
fn 1 (λ xs => if xs[0]! = 0 then 1 else 0) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_fs_bool : (Map.ofList fs).get! "bool" =
fn 1 (λ xs => if xs[0]! = 0 then 0 else 1) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_fs_add : (Map.ofList fs).get! "add" =
fn 2 (λ xs => xs[0]! + xs[1]!) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

@[simp]
theorem get!_fs_ite : (Map.ofList fs).get! "ite" =
fn 3 (λ xs => if xs[0]! = 0 then xs[2]! else xs[1]!) := by
  simp [fs, Map.ofList_eq_foldl, Map.get!_insert, mainName]

-- #check 0 #exit

theorem fs₁_get?_builtin {fs₁ name} [H : BuiltinC name]
(h : CompatibleDefs (.ofList defs) fs₁) : (builtinFs ∪ fs₁).get? name = some H.b.eval := by
  simp [h.get?_builtin]

theorem fs₁_get?_main {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? mainName = some (fn 1 # exprId.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) mainName defId (by simp [defs])]; rw [←Prog.ofDefs, ←prog]; simp

theorem fs₁_get?_zero {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? "0" = some (fn 0 # exprZero.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) "0" defZero (by simp [defs])]; rw [←Prog.ofDefs, ←prog]

theorem fs₁_get?_one {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? "1" = some (fn 0 # exprOne.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) "1" defOne (by simp [defs])]; rw [←Prog.ofDefs, ←prog]

theorem fs₁_get?_not {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? "not" = some (fn 1 # defNot.expr.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) "not" defNot (by simp [defs])]; rw [←Prog.ofDefs, ←prog]; simp

theorem fs₁_get?_bool {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? "bool" = some (fn 1 # defBool.expr.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) "bool" defBool (by simp [defs])]; rw [←Prog.ofDefs, ←prog]; simp

theorem fs₁_get?_add {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? "add" = some (fn 2 # defAdd.expr.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) "add" defAdd (by simp [defs])]; rw [←Prog.ofDefs, ←prog]; simp

theorem fs₁_get?_ite {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
fs₁.get? "ite" = some (fn 3 # defIte.expr.eval prog (builtinFs ∪ fs₁)) := by
  simp [(@h.eval_eq) "ite" defIte (by simp [defs])]; rw [←Prog.ofDefs, ←prog]; simp

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

theorem fs₁_get!_main {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! mainName = (Map.ofList fs).get! mainName := by
  rw [Map.get!_union_right # by simp]
  rw [Map.get!_eq_get!_get?, fs₁_get?_main h]; simp
  simp [exprId]

theorem fs₁_get!_zero {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! "0" = (Map.ofList fs).get! "0" := by
  rw [Map.get!_union_right # by simp; decide]
  rw [Map.get!_eq_get!_get?, fs₁_get?_zero h]; simp
  simp [exprZero, fs₁_get!_builtin h, fn]

theorem fs₁_zero {fs₁ xs} (h : CompatibleDefs (.ofList defs) fs₁) :
zero.eval prog (builtinFs ∪ fs₁) xs = 0 := by
  simp [zero, fs₁_get!_zero h, fn]

theorem fs₁_get!_one {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! "1" = (Map.ofList fs).get! "1" := by
  rw [Map.get!_union_right # by simp; decide]
  rw [Map.get!_eq_get!_get?, fs₁_get?_one h]; simp
  simp [exprOne, fs₁_get!_builtin h, fn, fs₁_zero h]

theorem fs₁_one {fs₁ xs} (h : CompatibleDefs (.ofList defs) fs₁) :
one.eval prog (builtinFs ∪ fs₁) xs = 1 := by
  simp [one, fs₁_get!_one h, fn]

theorem fs₁_get!_not {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! "not" = (Map.ofList fs).get! "not" := by
  rw [Map.get!_union_right # by simp; decide]
  rw [Map.get!_eq_get!_get?, fs₁_get?_not h]; simp
  simp [defNot]; intro n; simp [fs₁_get!_builtin h, fn, fs₁_one h]; grind

theorem fs₁_get!_bool {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! "bool" = (Map.ofList fs).get! "bool" := by
  rw [Map.get!_union_right # by simp; decide]
  rw [Map.get!_eq_get!_get?, fs₁_get?_bool h]; simp
  simp [defBool]; intro n; simp [fn, fs₁_get!_not h]

theorem exprAdd_aux (f : ℕ → ℕ → ℕ) (h : ∀ x y, f x y = f (x - 1) (y - 1) + 2 -
(if x = 0 then 1 else 0) - (if y = 0 then 1 else 0) - f 0 0) : f = (· + ·) := by
  ext x y
  have h₁ : f 0 0 = 0
  · specialize h 0 0
    simpa using h
  induction x generalizing y
  · specialize h 0
    simp at h
    induction y
    · specialize h 0
      simpa using h
    nm y ih
    specialize h (y + 1)
    simp_all
  nm x ih
  specialize h (x + 1) y
  simp_all
  specialize ih (y + 1)
  grind

theorem fs₁_get!_add {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! "add" = (Map.ofList fs).get! "add" := by
  apply fs₁_get!_of h defAdd (by simp [defs])
  intro f h₁ h₂ h₃ h₄ h₅
  simp [h₄, defAdd, exprAdd, funext_iff, fn, fs₁_get!_builtin h, h₂,
    fs₁_zero h, fs₁_one h, fs₁_get!_not h] at h₃
  have h₆ := forall_imp_of_forall (λ (xs : List _) => xs.length = 2) h₃
  simp at h₆; clear h₁ h₂ h₃ h₄ h₅; rename' h₆ => h₁
  have h₂ := exprAdd_aux (f [·, ·]); specialize h₂ _
  on_goal 2 => simpa [funext_iff] using h₂;; clear h₂; exact h₁

theorem exprIte_aux (f : ℕ → ℕ → ℕ → ℕ) (h : ∀ a b c, f a b c =
f a (b - 1) (c - 1) + 1 - ((if a = 0 then 0 else 1) - b) -
((if a = 0 then 1 else 0) - c) - f a 0 0) :
f = λ a b c => if a = 0 then c else b := by
  classical
  ext a b c
  simp [Nat.ite_eq_ofProp, Nat.ite_eq_ofProp'] at h
  have h₁ : ∀ a, f a 0 0 = 0
  · clear a b c; intro a; rw [h]; simp
  simp [h₁] at h
  by_cases ha : a = 0 <;> simp [ha]
  · clear! a
    induction c generalizing b
    · induction b
      · rw [h₁]
      nm b ih
      rw [h]
      simpa
    nm c ih
    rw [h]
    simp [ih]
  · induction c generalizing b
    · induction b
      · rw [h₁]
      nm b ih
      rw [h]
      simpa [ha]
    nm c ih
    rw [h]
    simp [ha, ih]
    cases b <;> simp

theorem fs₁_get!_ite {fs₁} (h : CompatibleDefs (.ofList defs) fs₁) :
(builtinFs ∪ fs₁).get! "ite" = (Map.ofList fs).get! "ite" := by
  apply fs₁_get!_of h defIte (by simp [defs])
  intro f h₁ h₂ h₃ h₄ h₅
  simp [h₄, defIte, exprIte, funext_iff, fn, fs₁_get!_builtin h, h₂,
    fs₁_zero h, fs₁_one h, fs₁_get!_not h, fs₁_get!_bool h] at h₃
  have h₆ := forall_imp_of_forall (λ (xs : List _) => xs.length = 3) h₃
  simp at h₆; clear h₁ h₂ h₃ h₄ h₅; rename' h₆ => h₁
  have h₂ := exprIte_aux (f [·, ·, ·]); specialize h₂ _
  on_goal 2 => simpa [funext_iff] using h₂;; clear h₂; exact h₁

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
  simp [eq_comm (b := Expr.eval _ _ _ _)]
  simp [fs₁_get?_main h, fs₁_get?_zero h, fs₁_get?_one h]
  revert xs
  simp only [imp_comm_left (b := List.length _ = _)]
  intro xs; apply and_of
  · simp [exprId]
  rintro -; revert xs
  intro xs; apply and_of
  · simp [exprZero, fs₁_get!_builtin h, fn]
  rintro -; revert xs
  intro xs; apply and_of
  · simp [exprOne, fs₁_get!_builtin h, fn, fs₁_zero h]
  rintro -; revert xs
  apply imp_fs_and_of # fs₁_get?_not h
  · simp; intro n; simp [defNot, fs₁_get!_builtin h, fs₁_one h, fn]; grind
  intro h_not
  apply imp_fs_and_of # fs₁_get?_bool h
  · simp; intro n; simp [defBool, h_not, fn]
  intro h_bool
  apply imp_fs_and_of # fs₁_get?_add h
  · simp; intro n m
    simp [defAdd, exprAdd, fs₁_get!_builtin h, fn, fs₁_get!_add h,
      fs₁_one h, fs₁_zero h, h_not]; grind
  intro h_add
  apply forall_and_true
  apply imp_fs_and_of # fs₁_get?_ite h
  · simp; intro a b c
    simp [defIte, exprIte, fs₁_get!_builtin h, fn, fs₁_get!_ite h,
      fs₁_zero h, fs₁_one h, h_bool, h_not]; grind
  intro h_ite
  simp
    
-- #check 0 #exit

instance : ProgInfo prog where
  name := "Prog₁"
  defNames := ["main", "0", "1", "not", "bool", "add", "ite"]
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