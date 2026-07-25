import Projects.Esolangs.Cornucopia.Defs

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Cornucopia

def exprId : Expr :=
  .arg 0

def progId : Prog where
  defs := [⟨1, exprId⟩]

def exprLoop (i : ℕ) : Expr :=
  .call (.custom i) [.arg 0]

def progLoop : Prog where
  defs := [⟨1, exprLoop 0⟩]

-- #check 0 #exit

-----

@[simp] theorem defs_progId : progId.defs = [⟨1, exprId⟩] := rfl
@[simp] theorem main_progId : progId.main = ⟨1, exprId⟩ := rfl
@[simp] theorem wf_exprId {prog} : exprId.WF prog 1 := by simp [Expr.WF, exprId]
@[simp] theorem wf_defId : (Def.mk 1 (.arg 0)).WF progId := wf_exprId
@[simp] theorem arity_zero_progId : progId.arity 0 = 1 := rfl
@[simp] theorem expr_zero_progId : progId.expr 0 = exprId := rfl

@[simp]
theorem Expr.run_arg {i prog f args} : (arg i).eval prog f args = args[i]! := by
  simp [eval]

@[simp] theorem Prog.defs_mk {ds} : defs ⟨ds⟩ = ds := rfl
@[simp] theorem Builtin.arity_succ : Builtin.succ.arity = 1 := rfl
@[simp] theorem Builtin.arity_sub : Builtin.sub.arity = 2 := rfl
@[simp] theorem Prog.arity_mk {defs i} : arity ⟨defs⟩ i = defs[i]!.arity := rfl
@[simp] theorem Prog.expr_mk {defs i} : expr ⟨defs⟩ i = defs[i]!.expr := rfl
@[simp] theorem Target.f_custom {fs i} : (custom i).f fs = fs[i]! := rfl
@[simp] theorem Target.arity_custom {prog i} : (custom i).arity prog = prog.arity i := rfl
@[simp] theorem Prog.main_mk {defs} : main ⟨defs⟩ = defs[0]! := rfl

@[simp]
theorem Expr.wf_arg {prog n i} : (arg i).WF prog n ↔ i < n := by
  simp [WF]

@[simp, instance]
theorem wf_progId : progId.WF := by
  constructor <;> try simp [exprId]
  use [fn 1 λ xs => xs[0]!]; unfold fn
  simp; split_ands; constructor <;> simp [exprId] <;> grind
  rintro fs ⟨h₁, h₂, h₃⟩; simp at h₁ h₂ h₃
  rw [List.length_eq_one_iff] at h₁; simp [exprId] at h₃
  obtain ⟨f, rfl⟩ := h₁; simp at h₂ h₃ ⊢; grind

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