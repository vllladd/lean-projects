import Projects.NatSuccSub.Defs

namespace NatSuccSub

@[simp]
def exprId : Expr :=
  .arg 0

def defId : Def where
  arity := 1
  expr := exprId

def progId : Prog where
  defs := [defId]

-----

@[simp] theorem defs_progId : progId.defs = [defId] := rfl
@[simp] theorem arity_defId : defId.arity = 1 := rfl
@[simp] theorem expr_defId : defId.expr = exprId := rfl
@[simp] theorem main_progId : progId.main = defId := rfl
@[simp] theorem wf_exprId : exprId.WF progId 1 := by simp [Expr.WF]
@[simp] theorem wf_defId : defId.WF progId := wf_exprId
@[simp] theorem arity_zero_progId : progId.arity 0 = 1 := rfl
@[simp] theorem expr_zero_progId : progId.expr 0 = exprId := rfl
@[simp] theorem Expr.eval_arg {i prog f args} : (arg i).eval prog f args = args[i]! := rfl
@[simp] theorem Prog.defs_mk {ds} : defs ⟨ds⟩ = ds := rfl
@[simp] theorem Prog.arity_zero {prog : Prog} : prog.arity 0 = 1 := rfl
@[simp] theorem Prog.arity_one {prog : Prog} : prog.arity 1 = 2 := rfl

@[simp, instance]
theorem wf_progId : progId.WF := by
  constructor; iterate 3 simp
  intro F G hf hg; rcases hf with ⟨h₁, h₂, h₃⟩
  rcases hg with ⟨h₄, h₅, h₆⟩; simp_all
  rw [List.length_eq_one_iff] at h₁ h₄
  obtain ⟨f, rfl⟩ := h₁; obtain ⟨g, rfl⟩ := h₄
  simp_all; grind

-- #check 0 #exit

-- example : ¬(⟨[⟨1, .call 2 (λ n => if n ≠ 0 then default else .arg 0)⟩]⟩ : Prog).WF := by
--   rintro ⟨-, -, -, h⟩
--   contrapose! h; clear h
--   use [λ (xs : List ℕ) => if xs.length ≠ 1 then default else 0]
--   use [λ (xs : List ℕ) => if xs.length ≠ 1 then default else 1]
--   simp
--   split_ands
--   ·
--     constructor <;> simp