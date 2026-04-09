import Projects.Esolangs.Lang_001.Defs

namespace Esolangs.Lang_001

def exprId : Expr :=
  .arg 0

def progId : Prog where
  defs := [⟨1, exprId⟩]

def exprSelf (i : ℕ) : Expr :=
  call (.custom i) [.arg 0]

def progSelf : Prog where
  defs := [⟨1, exprSelf 0⟩]

def refZero : Expr :=
  call (.custom 1) []

def refOne : Expr :=
  call (.custom 2) []

def exprZero : Expr :=
  call (.builtin .sub) [refZero, refZero]

def exprOne : Expr :=
  call (.builtin .succ) [refZero]

def exprMain₁ : Expr :=
  exprId

def prog₁ : Prog where
  defs := [
    ⟨1, exprMain₁⟩,
    ⟨0, exprZero⟩,
    ⟨0, exprOne⟩,
  ]

-- #check 0 #exit

-----

@[simp] theorem defs_progId : progId.defs = [⟨1, exprId⟩] := rfl
@[simp] theorem main_progId : progId.main = ⟨1, exprId⟩ := rfl
@[simp] theorem wf_exprId : exprId.WF progId 1 := by simp [Expr.WF, exprId]
@[simp] theorem wf_defId : (Def.mk 1 (.arg 0)).WF progId := wf_exprId
@[simp] theorem arity_zero_progId : progId.arity 0 = 1 := rfl
@[simp] theorem expr_zero_progId : progId.expr 0 = exprId := rfl
@[simp] theorem Expr.eval_arg {i prog f args} : (arg i).eval prog f args = args[i]! := rfl
@[simp] theorem Prog.defs_mk {ds} : defs ⟨ds⟩ = ds := rfl
@[simp] theorem Builtin.arity_succ : Builtin.succ.arity = 1 := rfl
@[simp] theorem Builtin.arity_sub : Builtin.sub.arity = 2 := rfl
@[simp] theorem Prog.arity_mk {defs i} : arity ⟨defs⟩ i = defs[i]!.arity := rfl
@[simp] theorem Prog.expr_mk {defs i} : expr ⟨defs⟩ i = defs[i]!.expr := rfl
@[simp] theorem Target.f_custom {fs i} : (custom i).f fs = fs[i]! := rfl
@[simp] theorem Target.arity_custom {prog i} : (custom i).arity prog = prog.arity i := rfl
@[simp] theorem Prog.main_mk {defs} : main ⟨defs⟩ = defs[0]! := rfl

@[simp, instance]
theorem wf_progId : progId.WF := by
  constructor <;> try simp [exprId]
  use [fn 1 λ xs => xs[0]!]; unfold fn
  simp; split_ands; constructor <;> simp [exprId] <;> grind
  rintro fs ⟨h₁, h₂, h₃⟩; simp at h₁ h₂ h₃
  rw [List.length_eq_one_iff] at h₁; simp [exprId] at h₃
  obtain ⟨f, rfl⟩ := h₁; simp at h₂ h₃ ⊢; grind

@[simp]
theorem Expr.eval_call' {prog fs args t xs} : (Expr.call' t xs).eval prog fs args =
t.f fs (List.range (t.arity prog) |>.map λ i => xs i |>.eval prog fs args) := rfl

@[simp]
theorem Expr.eval_call {prog fs args t xs} : (call t xs).eval prog fs args =
t.f fs (List.range (t.arity prog) |>.map λ i => xs[i]! |>.eval prog fs args) := rfl

theorem not_wf_progSelf : ¬progSelf.WF := by
  unfold progSelf exprSelf
  rintro ⟨-, -, -, h⟩; contrapose! h; clear h
  rw [not_exiu_iff_or]; right
  use [fn 1 λ _ => 0], [fn 1 λ _ => 1]; unfold fn
  simp; split_ands <;> try constructor <;> simp
  apply ne_of_congr (· [0]); simp

@[simp]
theorem Prog.compatible_fs {prog : Prog} [H : prog.WF] : prog.Compatible prog.fs :=
  Classical.epsilon_spec # H.exiu_compatible.exists

@[simp]
theorem eval_progId {n} : progId.eval n = n := by
  simp [Prog.eval, Prog.eval']; have h := @progId.compatible_fs.eval_eq
  simp at h; specialize @h [n]; simp at h; exact h

@[simp]
theorem wf_expr_prog₁_main₁ : exprMain₁.WF prog₁ 1 := by
  constructor; simp

@[simp]
theorem wf_def_prog₁_main₁ : Def.WF prog₁ ⟨1, exprMain₁⟩ := by
  simp [Def.WF]

@[simp]
theorem Prog.hasTarget_builtin {prog : Prog} {bn} : prog.HasTarget (.builtin bn) := trivial

@[simp]
theorem Prog.hasTarget_custom {prog : Prog} {i} :
prog.HasTarget (.custom i) ↔ i < prog.defs.length := by rfl

@[simp] theorem Target.arity_builtin {bn} : arity (builtin bn) = bn.arity := rfl
@[simp] theorem Target.f_builtin_succ {bn fs} : f (.builtin bn) fs = bn.f := rfl
@[simp] theorem Builtin.f_succ : f .succ = (·[0]! + 1) := rfl
@[simp] theorem Builtin.f_sub : f .sub = (λ xs => xs[0]! - xs[1]!) := rfl

-----

@[simp] theorem length_defs_prog₁ : prog₁.defs.length = 3 := rfl

@[simp]
theorem wf_prog₁_refZero : refZero.WF prog₁ 0 := by
  constructor <;> simp [prog₁]

@[simp]
theorem wf_prog₁_refOne : refOne.WF prog₁ 0 := by
  constructor <;> simp [prog₁]

@[simp]
theorem wf_expr_prog₁_exprZero : exprZero.WF prog₁ 0 := by
  constructor <;> simp; intro i; split_ifs with h; grind; simp at h
  rw [show [_, _] = .replicate 2 _ by rfl]
  rw [List.getElem?_eq_getElem h, List.getElem_replicate]; simp

@[simp]
theorem wf_expr_prog₁_exprOne : exprOne.WF prog₁ 0 := by
  constructor <;> simp; intro i; split_ifs with h; grind; simp at h; simp [h]

@[simp]
theorem wf_def_prog₁_exprZero : Def.WF prog₁ ⟨0, exprZero⟩ := by
  simp [Def.WF]

@[simp]
theorem wf_def_prog₁_exprOne : Def.WF prog₁ ⟨0, exprOne⟩ := by
  simp [Def.WF]

-- #check 0 #exit

@[simp] theorem arity_prog₁_0 : prog₁.arity 0 = 1 := rfl
@[simp] theorem arity_prog₁_1 : prog₁.arity 1 = 0 := rfl
@[simp] theorem arity_prog₁_2 : prog₁.arity 2 = 0 := rfl

@[simp, instance]
theorem wf_prog₁ : prog₁.WF := by
  constructor
  · rintro ⟨⟩
  · rfl
  · nth_rw 1 [prog₁]; simp
  use [fn 1 (·[0]!), fn 0 λ _ => 0, fn 0 λ _ => 1]
  simp
  constructor
  · constructor <;> simp
    · intro i h xs h₁
      replace h : i = 0 ∨ i = 1 ∨ i = 2; omega
      rcases h with rfl | rfl | rfl <;> simp at h₁ <;> simp [fn] <;> grind
    · rintro i h xs h₁
      replace h : i = 0 ∨ i = 1 ∨ i = 2; omega
      nth_rw 1 [prog₁]
      rcases h with rfl | rfl | rfl <;> simp at h₁ <;> simp [fn]
      · simp [exprMain₁, exprId, h₁]
      · simp [exprZero]
      · simp [exprOne, h₁, refZero, fn]
  rintro fs ⟨h₁, h₂, h₃⟩
  simp at h₁ h₂ h₃
  rw [List.ext_getElem_iff]
  simp [h₁]
  intro i h₄ h₅
  have h_zero : fs[1] [] = 0
  · specialize @h₃ 1 (by omega) [] (by simp)
    simp [prog₁, exprZero] at h₃
    rw [List.getElem?_eq_getElem # by grind] at h₃
    simp at h₃
    exact h₃
  specialize h₂ h₄
  specialize h₃ h₄
  ext xs
  specialize @h₂ xs
  specialize @h₃ xs
  have h₆ : i = 0 ∨ i = 1 ∨ i = 2; omega
  rcases h₆ with rfl | rfl | rfl
  · simp [fn] at h₂ h₃ ⊢
    split_ifs with H
    · clear h₂
      specialize h₃ H
      simp [prog₁, exprMain₁, exprId] at h₃
      rw [List.length_eq_one_iff] at H
      obtain ⟨x, rfl⟩ := H
      simp at h₃ ⊢
      rw [List.getElem?_eq_getElem # by grind] at h₃
      simp at h₃
      exact h₃
    · clear h₃
      specialize h₂ H
      rw [List.getElem?_eq_getElem # by grind] at h₂
      simp at h₂
      exact h₂
  · simp [fn, prog₁, exprZero] at h₂ h₃ ⊢
    rw [List.getElem?_eq_getElem # by grind] at h₂ h₃
    simp at h₂ h₃
    nth_rw 2 [eq_comm] at h₃
    tauto
  · simp [fn, prog₁] at h₂ h₃ ⊢
    rw [List.getElem?_eq_getElem # by grind] at h₂ h₃
    simp at h₂ h₃
    simp [exprOne, refZero] at h₃
    rw [List.getElem?_eq_getElem # by grind] at h₃
    simp at h₃
    split_ifs with H
    rotate_left; exact h₂ H
    clear h₂
    subst H
    specialize h₃ rfl
    rw [h₃]; clear h₃
    simpa

@[simp]
theorem prog₁_eval'_zero : prog₁.eval' 1 [] = 0 := by
  simp [Prog.eval']; have h := @prog₁.compatible_fs.eval_eq; simp at h
  specialize @h 1 (by omega) [] rfl
  rw [h]; simp [prog₁, exprZero]

@[simp]
theorem prog₁_eval'_one : prog₁.eval' 2 [] = 1 := by
  simp [Prog.eval']; have h := @prog₁.compatible_fs.eval_eq; simp at h
  specialize @h 2 (by omega) [] rfl; rw [h]; clear h
  nth_rw 1 [prog₁]; simp [exprOne, refZero]
  convert prog₁_eval'_zero; ext; simp [Prog.eval']