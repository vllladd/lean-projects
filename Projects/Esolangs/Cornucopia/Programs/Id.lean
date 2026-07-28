import Projects.Esolangs.Cornucopia.Basic

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia.Programs.Id

def exprId : Expr :=
  .arg 0

def defs : List (String × Def) :=
  [(mainName, ⟨1, exprId⟩)]

def fs : Map String (List ℕ → ℕ) :=
  .ofList [(mainName, fn 1 (·[0]!))]

def prog : Prog :=
  .ofDefs defs

-----

@[simp]
theorem nodup_defs : defs.map (·.1) |>.Nodup := by
  simp [defs]

@[simp]
theorem wfDefs' : WFDefs' defs := by
  constructor <;> simp [defs, exprId]

@[instance, simp]
theorem wf' : prog.WF' :=
  wfDefs'.wf'

@[simp]
theorem compatibleDefs : CompatibleDefs (.ofList defs) fs := by
  use by simp [defs, fs]
  intro name d; simp [defs, fs, Map.get?_insert]
  rintro rfl rfl; simp [exprId]

@[simp]
theorem compatible : prog.Compatible (builtinFs ∪ fs) :=
  wfDefs'.compatible compatibleDefs

@[instance, simp]
theorem wf_prog : prog.WF := by
  apply wfDefs'.wf; use fs, compatibleDefs
  intro fs' h₁ name d f h₂ h₃
  simp [fs, Map.get!_insert]
  have h₅ := h₁.eval_eq h₂ |>.symm
  simp [h₃] at h₅
  subst h₅
  simp [funext_iff, fn]
  intro xs
  simp [defs] at h₂
  rcases h₂ with ⟨rfl, rfl⟩
  simp [fn, exprId]

@[simp]
theorem fs_prog : prog.fs = builtinFs ∪ fs :=
  prog.fs_eq_of_compatible compatible

@[simp]
theorem run_prog {n} : prog.run n = n := by
  simp [Prog.run, Prog.eval, fs, Map.get!_insert, fn]

instance : ProgInfo prog where
  name := "Id"
  defNames := ["main"]
  has_model := true
  has_unique_model := true
  h_defNames := by
    simp [prog, defs, builtinDefs, builtins, Map.ofList_eq_foldl, Map.keys_insert]; decide
  h_wf' := by simp
  h_has_model := by simp [Prog.HasModel]; use prog.fs; simp
  h_has_unique_model := by simp [Prog.HasUniqueModel]; exact wf_prog.exiu_compatible