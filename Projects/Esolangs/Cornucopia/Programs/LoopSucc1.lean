import Projects.Esolangs.Cornucopia.Programs.Common

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia.ProgLoopSucc₁

def defs : List (String × Def) :=
  [(mainName, defLoopSucc₁ mainName)]

def prog : Prog :=
  .ofDefs defs

-----

@[simp]
theorem nodup_defs : defs.map (·.1) |>.Nodup := by
  simp [defs]

@[instance, simp]
theorem wfBuiltins_prog : prog.WFBuiltins := by
  apply Prog.wfBuiltins_ofDefs; decide

@[simp]
theorem wfDefs' : WFDefs' defs := by
  constructor; iterate 3 simp [defs]
  rw [←prog]; simp [defs]; apply wf_exprLoopSucc₁
  simp [prog, defs, Prog.ofDefs, Map.get?_insert]

@[instance, simp]
theorem wf' : prog.WF' :=
  wfDefs'.wf'

@[instance, simp]
theorem wfWoutModel_prog : prog.WFWoutModel := by
  constructor; intro fs H
  have h₁ := @H.eval_eq mainName (by simp) [0] (by simp)
  simp [prog, defs, Prog.ofDefs, Map.get!_insert, exprLoopSucc₁, H.get!_builtin, fn] at h₁

instance : ProgInfo prog where
  name := "LoopSucc₁"
  defNames := ["main"]
  has_model := false
  has_unique_model := false
  h_defNames := by
    simp [prog, defs, builtinDefs, builtins, Map.ofList_eq_foldl, Map.keys_insert]; decide
  h_wf' := by simp
  h_has_model := by simp [Prog.HasModel, wfWoutModel_prog.not_compatible]
  h_has_unique_model := by simp [Prog.HasUniqueModel, wfWoutModel_prog.not_compatible]