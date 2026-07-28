import Projects.Esolangs.Cornucopia.Basic

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia.Programs.LoopSucc₂

def exprLoop (name : String) : Expr :=
  .call name [.call succName [.arg 0]]

def defs : List (String × Def) :=
  [(mainName, ⟨1, exprLoop mainName⟩)]

def fs (n : ℕ) : Map String (List ℕ → ℕ) :=
  .ofList [(mainName, fn 1 # λ _ => n)]

def prog : Prog :=
  .ofDefs defs

-----

@[simp]
theorem nodup_defs : defs.map (·.1) |>.Nodup := by
  simp [defs]

@[simp]
theorem wfDefs' : WFDefs' defs := by
  constructor <;> simp [defs, exprLoop]
  simp [Prog.ofDefs, Map.get!_insert]

@[instance, simp]
theorem wf' : prog.WF' :=
  wfDefs'.wf'

@[simp]
theorem compatibleDefs {n} : CompatibleDefs (.ofList defs) (fs n) := by
  use by simp [defs, fs]
  intro name d; simp [defs, fs, Map.get?_insert]
  rintro rfl rfl; simp [exprLoop, Map.get!_insert, fn]

@[simp]
theorem compatible {n} : prog.Compatible (builtinFs ∪ fs n) :=
  wfDefs'.compatible compatibleDefs

@[simp]
theorem builtin_not_mem_fs {n} {b : Builtin} : b.name ∉ fs n := by
  simp [fs]

@[simp]
theorem fs_eq_fs_iff {n m} : fs n = fs m ↔ n = m := by
  symm; use by grind;; simp [fs]; exact λ h => h [0] rfl

@[instance, simp]
theorem wfWoutUnique_prog : prog.WFWoutUnique := by
  constructor
  use builtinFs ∪ fs 0, builtinFs ∪ fs 1
  simp [Map.union_eq_union_iff_right]

instance : ProgInfo prog where
  name := "Loop"
  defNames := ["main"]
  has_model := true
  has_unique_model := false
  h_defNames := by
    simp [prog, defs, builtinDefs, builtins, Map.ofList_eq_foldl, Map.keys_insert]; decide
  h_wf' := by simp
  h_has_model := by
    simp [Prog.HasModel]; use prog.fs; apply τ_spec; use builtinFs ∪ fs 0; simp
  h_has_unique_model := by
    have := wfWoutUnique_prog.exi_two; simp [Prog.HasUniqueModel, not_exiu_iff_or]; tauto