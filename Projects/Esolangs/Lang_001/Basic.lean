import Projects.Esolangs.Lang_001.Defs

attribute [-simp] List.getElem!_eq_getElem?_getD

namespace Esolangs.Lang_001

def exprId : Expr :=
  .arg 0

def progId : Prog where
  defs := [⟨1, exprId⟩]

def exprLoop (i : ℕ) : Expr :=
  .call (.custom i) [.arg 0]

def progLoop : Prog where
  defs := [⟨1, exprLoop 0⟩]

def refZero : Expr :=
  .call (.custom 1) []

def refOne : Expr :=
  .call (.custom 2) []

def exprZero : Expr :=
  .call (.builtin .sub) [refZero, refZero]

def exprOne : Expr :=
  .call (.builtin .succ) [refZero]

def exprNot : Expr :=
  .call (.builtin .sub) [refOne, .arg 0]

def exprBool : Expr :=
  .call (.custom 3) [.call (.custom 3) [.arg 0]]

def exprAdd : Expr :=
  .call (.builtin .sub)
  [ .call (.builtin .sub)
    [ .call (.builtin .sub)
      [ .call (.builtin .succ) [.call (.builtin .succ) [
          .call (.custom 5)
            [ .call (.builtin .sub) [.arg 0, refOne]
            , .call (.builtin .sub) [.arg 1, refOne]
            ]
        ]]
      , .call (.custom 3) [.arg 0]
      ]
    , .call (.custom 3) [.arg 1]
    ]
  , .call (.custom 5) [refZero, refZero]
  ]

def exprMain₁ : Expr :=
  exprId

def prog₁ : Prog where
  defs := [
    ⟨1, exprMain₁⟩,
    ⟨0, exprZero⟩,
    ⟨0, exprOne⟩,
    ⟨1, exprNot⟩,
    ⟨1, exprBool⟩,
    ⟨2, exprAdd⟩,
  ]

def prog₁FS : List (List ℕ → ℕ) :=
  [ fn 1 λ xs => xs[0]!
  , fn 0 λ _ => 0
  , fn 0 λ _ => 1
  , fn 1 λ xs => if xs[0]! = 0 then 1 else 0
  , fn 1 λ xs => if xs[0]! = 0 then 0 else 1
  , fn 2 λ xs => xs[0]! + xs[1]!
  ]

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
  τ_spec # H.exiu_compatible.exists

@[simp]
theorem eval_exprId {prog fs xs} : exprId.eval prog fs xs = xs[0]! := by
  simp [exprId]

@[simp]
theorem run_progId {n} : progId.run n = n := by
  simp [Prog.run, Prog.eval]; have h := @progId.compatible_fs.eval_eq
  simp at h; specialize @h [n]; simpa using h

@[simp]
theorem wf_expr_prog₁_main₁ : exprMain₁.WF prog₁ 1 := by
  simp [exprMain₁]

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

-- #check 0 #exit

theorem exprAdd_aux {f : ℕ → ℕ → ℕ} (h : ∀ x y, f x y = f (x - 1) (y - 1) + 2 -
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

-- #check 0 #exit

@[simp] theorem length_defs_prog₁ : prog₁.defs.length = 6 := rfl

@[simp] theorem prog₁_arity_0 : prog₁.arity 0 = 1 := rfl
@[simp] theorem prog₁_arity_1 : prog₁.arity 1 = 0 := rfl
@[simp] theorem prog₁_arity_2 : prog₁.arity 2 = 0 := rfl
@[simp] theorem prog₁_arity_3 : prog₁.arity 3 = 1 := rfl
@[simp] theorem prog₁_arity_4 : prog₁.arity 4 = 1 := rfl
@[simp] theorem prog₁_arity_5 : prog₁.arity 5 = 2 := rfl

@[simp]
theorem wf_prog₁_refZero {n} : refZero.WF prog₁ n := by
  simp [refZero]

@[simp]
theorem wf_expr_prog₁_exprZero {n} : exprZero.WF prog₁ n := by
  simp [exprZero]

@[simp]
theorem wf_prog₁_refOne {n} : refOne.WF prog₁ n := by
  simp [refOne]

@[simp]
theorem wf_expr_prog₁_exprOne {n} : exprOne.WF prog₁ n := by
  simp [exprOne]

@[simp]
theorem wf_expr_prog₁_exprNot {n} : exprNot.WF prog₁ n ↔ 1 ≤ n := by
  simp [exprNot]; omega

@[simp]
theorem wf_expr_prog₁_exprBool {n} : exprBool.WF prog₁ n ↔ 1 ≤ n := by
  simp [exprBool]; omega

@[simp]
theorem wf_expr_prog₁_exprAdd {n} : exprAdd.WF prog₁ n ↔ 2 ≤ n := by
  simp [exprAdd]; omega

-- #check 0 #exit

@[simp]
theorem compatible_prog₁_prog₁FS : prog₁.Compatible prog₁FS := by
  unfold prog₁FS; constructor <;> simp
  all_goals
    intro i h xs h₁
    obtain rfl | rfl | rfl | rfl | rfl | rfl :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  iterate 6 simp at h₁; simp [fn] <;> try grind
  all_goals nth_rw 1 [prog₁]; (try simp at h₁); simp [fn, h₁]
  · simp [exprMain₁, exprId]
  · simp [exprZero]
  · simp [exprOne, refZero, fn]
  · simp [exprNot, refOne, fn]; grind
  · simp [exprBool, fn]; grind
  · simp [exprAdd, fn]; rw! [xs.eq_getElem_of_length_eq_two h₁]
    simp; generalize xs[0] = x; generalize xs[1] = y; clear h₁ xs
    simp [refOne, refZero, fn]; cases x; cases y <;> rfl; nm x
    simp; cases y; rfl; nm y; simp; omega

@[simp, instance]
theorem wf_prog₁ : prog₁.WF := by
  constructor; rintro ⟨⟩; rfl; nth_rw 1 [prog₁]; simp
  use prog₁FS, (by simp); unfold prog₁FS
  rintro fs ⟨h₁, h₂, h₃⟩; simp at h₁ h₂ h₃
  have h_zero : fs[1]! [] = 0
  · specialize @h₃ 1 (by omega) [] (by simp)
    simp [prog₁, exprZero] at h₃; exact h₃
  have h_one : fs[2]! [] = 1
  · specialize @h₃ 2 (by omega) [] (by simp)
    simp [prog₁, exprOne, refZero] at h₃; grind
  have h_not : ∀ ⦃x⦄, fs[3]! [x] = if x = 0 then 1 else 0
  · intro x; specialize @h₃ 3 (by omega) [x] (by simp)
    simp [prog₁, exprNot, refOne] at h₃; grind
  have h_bool : ∀ ⦃x⦄, fs[4]! [x] = if x = 0 then 0 else 1
  · intro x; specialize @h₃ 4 (by omega) [x] (by simp)
    simp [prog₁, exprBool] at h₃; grind
  have h_add : ∀ ⦃x y⦄, fs[5]! [x, y] = x + y
  · intro x y; specialize @h₃ 5 (by omega)
    simp [prog₁, exprAdd, refOne, refZero] at h₃
    simp [h_zero, h_one, h_not] at h₃
    replace h₃ : ∀ x y, fs[5]! [x, y] = fs[5]! [x - 1, y - 1] + 2 -
      (if x = 0 then 1 else 0) - (if y = 0 then 1 else 0) - fs[5]! [0, 0]
    · intro x y; specialize @h₃ [x, y]; simp at h₃; omega
    have h₄ := exprAdd_aux (f := λ x y => fs[5]! [x, y]) (by grind); grind
  rw [List.ext_getElem!_iff]; simp [h₁]; intro i h₄; ext xs
  specialize @h₂ i (by omega); specialize @h₃ i (by omega)
  specialize @h₂ xs; specialize @h₃ xs
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  all_goals simp [prog₁, fn] at h₂ h₃ ⊢
  · split_ifs with H
    · specialize h₃ H; simp [exprMain₁, exprId] at h₃; grind
    · specialize h₂ H; grind
  · simp [exprZero] at h₃; grind
  · simp [exprOne] at h₂ h₃; grind
  · simp [exprNot, refOne] at h₂ h₃; grind
  · simp [exprBool] at h₂ h₃; grind
  · simp [exprAdd, refOne, refZero] at h₂ h₃; grind

@[simp]
theorem fs_prog₁ : prog₁.fs = prog₁FS :=
  Prog.fs_eq_of_compatible compatible_prog₁_prog₁FS

@[simp]
theorem eval_prog₁ {i xs} : prog₁.eval i xs = prog₁FS[i]! xs := by
  simp [Prog.eval]

@[simp]
theorem run_prog₁ {x} : prog₁.run x = x := by
  simp [Prog.run, Prog.eval, prog₁FS, fn]