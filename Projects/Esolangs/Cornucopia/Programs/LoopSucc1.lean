import Projects.Esolangs.Cornucopia.Basic

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia.Programs.LoopSucc₁

def exprLoopSucc (name : String) : Expr :=
  .call succName [.call name [.arg 0]]

def defs : List (String × Def) :=
  [(mainName, ⟨1, exprLoopSucc mainName⟩)]

def prog : Prog :=
  .ofDefs defs

-----

@[simp]
theorem nodup_defs : defs.map (·.1) |>.Nodup := by
  simp [defs]

@[simp]
theorem wfDefs' : WFDefs' defs := by
  constructor <;> simp [defs, exprLoopSucc]
  simp [Prog.ofDefs, Map.get!_insert]

@[instance, simp]
theorem wf' : prog.WF' :=
  wfDefs'.wf'

@[instance, simp]
theorem wfWoutModel_prog : prog.WFWoutModel := by
  constructor; intro fs H
  have h₁ := @H.eval_eq mainName (by simp) [0] (by simp)
  simp [prog, defs, Prog.ofDefs, Map.get!_insert, exprLoopSucc, H.get!_builtin, fn] at h₁

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