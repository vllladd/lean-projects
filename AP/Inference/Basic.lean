import AP.Util

namespace Inference

inductive Expr where
| var : ℕ → Expr
| not : Expr → Expr
| imp : Expr → Expr → Expr

inductive Proof' : Expr → Type where
| ax₁ : ∀ (P Q : Expr), Proof' # .imp P # .imp Q P
| ax₂ : ∀ (P Q R : Expr), Proof' # .imp
  (.imp P # .imp Q R) # .imp (.imp P Q) # .imp P R
| ax₃ : ∀ (P Q : Expr), Proof' # .imp
  (.imp (.not P) (.not Q)) # .imp Q P
| mp : ∀ {P Q}, Proof' (.imp P Q) → Proof' P → Proof' Q

inductive Proof (e : Expr) : Prop where
| mk : Proof' e → Proof e

-----

noncomputable
def Proof.p {e} (h : Proof e) : Proof' e := by
  apply Nonempty.some; cases h; nm h; use h

@[match_pattern] def ax₁ P Q := Proof.mk # Proof'.ax₁ P Q
@[match_pattern] def ax₂ P Q R := Proof.mk # Proof'.ax₂ P Q R
@[match_pattern] def ax₃ P Q := Proof.mk # Proof'.ax₃ P Q

@[match_pattern]
def mp {P Q : Expr} (h₁ : Proof # .imp P Q) (h₂ : Proof _) :=
  Proof.mk # Proof'.mp h₁.p h₂.p

theorem mp' {P Q} (h₁ : Proof P) (h₂ : Proof # .imp P Q) : Proof Q :=
  mp h₂ h₁

theorem imp_refl : Proof # .imp (.var 0) (.var 0) := by
  generalize Expr.var 0 = P
  apply mp' # ax₁ P P
  apply mp' # ax₁ P (.imp P P)
  exact ax₂ P (.imp P P) P

@[simp]
def Expr.subst (e : Expr) (i : ℕ) (e' : Expr) : Expr :=
  match e with
  | .var j => if j = i then e' else e
  | .not e => .not # e.subst i e'
  | .imp a b => .imp (a.subst i e') (b.subst i e')

@[simp]
def proof_subst_of' {e e' i} (p : Proof' e) : Proof' # e.subst i e' :=
  match hp : p with
  | .ax₁ P Q => by nm h₁; subst h₁; simp at hp ⊢; subst hp; apply Proof'.ax₁
  | .ax₂ P Q R => by nm h₁; subst h₁; simp at hp ⊢; subst hp; apply Proof'.ax₂
  | .ax₃ P Q => by nm h₁; subst h₁; simp at hp ⊢; subst hp; apply Proof'.ax₃
  | .mp p₁ p₂ => by
    nm a b h₁; subst h₁; simp at hp; subst hp; have p₁' := @proof_subst_of' _ e' i p₁
    have p₂' := @proof_subst_of' _ e' i p₂; simp at p₁'; exact Proof'.mp p₁' p₂'
termination_by sizeOf p
decreasing_by all_goals
  nm a b p' h₁ h₂; subst h₁; simp at h₂ hp; subst h₂; rw [hp]; simp; try linarith

theorem proof_subst_of {e e' i} (h : Proof e) : Proof # e.subst i e' :=
  ⟨proof_subst_of' h.p⟩

@[simp]
def Proof'.nodes {e} (p : Proof' e) : Set # Σ e, Proof' e :=
  match h₁ : p with
  | .ax₁ _ _ => {⟨e, p⟩}
  | .ax₂ _ _ _ => {⟨e, p⟩}
  | .ax₃ _ _ => {⟨e, p⟩}
  | .mp p₁ p₂ => by nm e p₃ h₂; subst h₂; exact insert ⟨e, p⟩ # p₁.nodes ∪ p₂.nodes
termination_by sizeOf p
decreasing_by all_goals
  nm a b p' h₂; subst h₂; simp at h₁ hp; subst hp; rw [h₁]; simp; try linarith

@[simp]
theorem mem_nodes_self {e} {p : Proof' e} : ⟨e, p⟩ ∈ p.nodes := by
  cases p <;> simp

-- #check 0 #exit

theorem sizeOf_lt_of_mem_nodes {e e'} {p : Proof' e} {p' : Proof' e'}
(h₁ : ⟨e', p'⟩ ∈ p.nodes) (h₂ : e' ≠ e ∨ ¬(p' ≍ p)) : sizeOf p' < sizeOf p := by
  fun_induction Proof'.nodes
  any_goals
    simp at h₁; rcases h₁ with ⟨rfl, h₁⟩; simp at h₁ h₂; contradiction
  nm b a p₁ p₂ ih₁ ih₂ h₁; simp
  rcases h₁ with h₁ | h₁
  · by_cases h₃ : e' = .imp a b ∧ p' ≍ p₁
    · rcases h₃ with ⟨rfl, h₃⟩
      simp at h₃
      subst h₃
      linarith
    rw [not_and_iff_or] at h₃
    specialize ih₁ p₁ (by simp) h₁ h₃
    linarith
  · by_cases h₃ : e' = a ∧ p' ≍ p₂
    · rcases h₃ with ⟨rfl, h₃⟩
      simp at h₃
      subst h₃
      linarith
    rw [not_and_iff_or] at h₃
    specialize ih₂ p₁ (by simp) h₁ h₃
    linarith

theorem sizeOf_le_of_mem_nodes {e e'} {p : Proof' e} {p' : Proof' e'}
(h : ⟨e', p'⟩ ∈ p.nodes) : sizeOf p' ≤ sizeOf p := by
  by_cases h₁ : e' ≠ e ∨ ¬(p' ≍ p)
  · exact le_of_lt # sizeOf_lt_of_mem_nodes h h₁
  push_neg at h₁
  rcases h₁ with ⟨rfl, h₁⟩
  simp at h₁
  rw [h₁]

-- theorem mem_nodes_of_imp_var {a i} (p₁ : Proof' a) (p₂ : Proof' # .imp a # .var i) :
-- ∃ (p : Proof' # .var i), ⟨_, p⟩ ∈ p₂.nodes := by
--   cases h₁ : p₂
--   nm b p₃ p₄
--   subst h₁
--   simp
--   sorry
-- 
-- -- #check 0 #exit
-- 
-- @[simp]
-- theorem not_proof_var {i} : ¬Proof (.var i) := by
--   classical
--   rintro h
--   replace h : ∃ (n : ℕ) (p : Proof' # .var i), sizeOf p = n
--   · simp; exact ⟨h.p⟩
--   replace h : ∃ (p : Proof' # .var i), ∀ (p' : Proof' # .var i), sizeOf p ≤ sizeOf p'
--   · replace h := Nat.exi_least_of_exi h
--     rcases h with ⟨n, ⟨p, rfl⟩, h⟩
--     use p
--     intro p'
--     by_contra! h₁
--     specialize h _ h₁
--     simp at h
--   obtain ⟨p, h⟩ := h
--   cases h₁ : p
--   nm b p₁ p₂
--   subst h₁
--   choose p h₁ using mem_nodes_of_imp_var p₁ p₂
--   replace h₁ := sizeOf_lt_of_mem_nodes h₁ (by simp)
--   specialize h p
--   simp at h
--   linarith