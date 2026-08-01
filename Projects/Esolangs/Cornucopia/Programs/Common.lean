import Projects.Esolangs.Cornucopia.Basic

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia

-----

@[simp]
def Expr.const (name : String) : Expr :=
  .call name []

def exprId : Expr :=
  .arg 0

@[simp]
def defId : Def :=
  ⟨1, exprId⟩

def exprLoop (name : String) : Expr :=
  .call name [.arg 0]

@[simp]
def defLoop (name : String) : Def :=
  ⟨1, exprLoop name⟩

def exprLoopSucc₁ (name : String) : Expr :=
  .call succName [.call name [.arg 0]]

@[simp]
def defLoopSucc₁ (name : String) : Def :=
  ⟨1, exprLoopSucc₁ name⟩

def exprLoopSucc₂ (name : String) : Expr :=
  .call name [.call succName [.arg 0]]

@[simp]
def defLoopSucc₂ (name : String) : Def :=
  ⟨1, exprLoopSucc₂ name⟩

def zero : Expr :=
  .const "0"

def exprZero : Expr :=
  .call subName [zero, zero]

@[simp]
def defZero : Def :=
  ⟨0, exprZero⟩

def one : Expr :=
  .const "1"

def exprOne : Expr :=
  .call succName [zero]

@[simp]
def defOne : Def :=
  ⟨0, exprOne⟩

-- #check 0 #exit

-----

@[simp] theorem arity_defId : defId.arity = 1 := rfl
@[simp] theorem expr_defId : defId.expr = exprId := rfl

@[simp]
theorem wf_exprId {prog} : exprId.WF prog 1 := by
  simp [exprId]

theorem wf_exprLoop {prog name}
(h : prog.def? name = some (defLoop name)) : (exprLoop name).WF prog 1 := by
  simp [exprLoop, Prog.HasDef, Map.mem_of_get?_eq_some h, Prog.arity, Prog.def_eq_get!_def?, h]

theorem wf_exprLoopSucc₁ {prog : Prog} {name} [H : prog.WFBuiltins]
(h : prog.def? name = some (defLoopSucc₁ name)) : (exprLoopSucc₁ name).WF prog 1 := by
  simp [exprLoopSucc₁, prog.hasDef_of_def? h, prog.arity_of_def? h]

theorem wf_exprLoopSucc₂ {prog : Prog} {name} [H : prog.WFBuiltins]
(h : prog.def? name = some (defLoopSucc₂ name)) : (exprLoopSucc₂ name).WF prog 1 := by
  simp [exprLoopSucc₂, prog.hasDef_of_def? h, prog.arity_of_def? h]

theorem Expr.wf_const {prog : Prog} {name d k}
(h₁ : prog.def? name = some d) (h₂ : d.arity = 0) : (Expr.const name).WF prog k := by
  simp [Prog.hasDef_of_def? h₁, Prog.arity_of_def? h₁, h₂]

theorem wf_zero {prog : Prog} {k} (h : prog.def? "0" = some defZero) : zero.WF prog k :=
  Expr.wf_const h rfl

theorem wf_one {prog : Prog} {k} (h : prog.def? "1" = some defOne) : one.WF prog k :=
  Expr.wf_const h rfl

theorem wf_exprZero {prog : Prog} [H : prog.WFBuiltins] {k}
(h : prog.def? "0" = some defZero) : exprZero.WF prog k := by
  simp [exprZero, wf_zero h]

theorem wf_exprOne {prog : Prog} [H : prog.WFBuiltins] {k}
(h : prog.def? "0" = some defZero) : exprOne.WF prog k := by
  simp [exprOne, wf_zero h]