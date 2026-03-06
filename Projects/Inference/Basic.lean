import Projects.Util

namespace Inference

inductive Stat where
| var : ℕ → Stat
| not : Stat → Stat
| imp : Stat → Stat → Stat
deriving Inhabited, DecidableEq

inductive ProofD : Type where
| ax₁ : Stat → Stat → ProofD
| ax₂ : Stat → Stat → Stat → ProofD
| ax₃ : Stat → Stat → ProofD
| mp : ProofD → ProofD → ProofD
deriving Inhabited, DecidableEq

@[simp]
def ProofD.stat (p : ProofD) : Option Stat :=
  match p with
  | .ax₁ P Q => some # .imp P # .imp Q P
  | .ax₂ P Q R => some # .imp
    (.imp P # .imp Q R) # .imp (.imp P Q) # .imp P R
  | .ax₃ P Q => some # .imp
    (.imp (.not P) (.not Q)) # .imp Q P
  | mp p₁ p₂ => do match ←p₁.stat, ←p₂.stat with
    | .imp P Q, P' =>
      guard # P = P'
      some Q
    | _, _ => none

class ProofD.WF (p : ProofD) : Prop where
  h : ∃ s, p.stat = some s

structure Proof (e : Stat) : Prop where
  h : ∃ (p : ProofD), p.stat = some e

-----

theorem ax₁ (P Q : Stat) : Proof # .imp P # .imp Q P := by
  use ProofD.ax₁ P Q; rfl

theorem ax₂ (P Q R : Stat) : Proof # .imp (.imp P # .imp Q R) # .imp (.imp P Q) # .imp P R := by
  use ProofD.ax₂ P Q R; rfl

theorem ax₃ (P Q : Stat) : Proof # .imp (.imp (.not P) (.not Q)) # .imp Q P := by
  use ProofD.ax₃ P Q; rfl

theorem mp {P Q} (h₁ : Proof # .imp P Q) (h₂ : Proof P) : Proof Q := by
  obtain ⟨p₁, h₁⟩ := h₁; obtain ⟨p₂, h₂⟩ := h₂; use ProofD.mp p₁ p₂; simpa [h₁]

theorem mp' {P Q} (h₁ : Proof P) (h₂ : Proof # .imp P Q) : Proof Q :=
  mp h₂ h₁

@[simp]
theorem imp_refl : Proof # .imp (.var 0) (.var 0) := by
  generalize Stat.var 0 = P
  apply mp' # ax₁ P P
  apply mp' # ax₁ P (.imp P P)
  exact ax₂ P (.imp P P) P

@[simp]
def Stat.subst (s : Stat) (i : ℕ) (s' : Stat) : Stat :=
  match s with
  | .var j => if j = i then s' else s
  | .not e => .not # e.subst i s'
  | .imp a b => .imp (a.subst i s') (b.subst i s')

@[simp]
def ProofD.subst (p : ProofD) (i : ℕ) (s : Stat) : ProofD :=
  match p with
  | .ax₁ P Q => .ax₁ (P.subst i s) (Q.subst i s)
  | .ax₂ P Q R => .ax₂ (P.subst i s) (Q.subst i s) (R.subst i s)
  | .ax₃ P Q => .ax₃ (P.subst i s) (Q.subst i s)
  | .mp p₁ p₂ => .mp (p₁.subst i s) (p₂.subst i s)

theorem stat_mp_eq_some_iff {p₁ p₂ : ProofD} {s} : (p₁.mp p₂).stat = some s ↔
∃ P, p₁.stat = some (.imp P s) ∧ p₂.stat = some P := by
  simp
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨w_1, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    simp_all only [Option.some.injEq, exists_eq_right']
    split at right
    next __do_lift __do_lift_1 P Q =>
      simp_all only [Option.bind_eq_some_iff', Option.guard_eq_some', Option.some.injEq,
      exists_const]
    next __do_lift __do_lift_1 x => simp_all only [imp_false, reduceCtorEq]
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    simp_all only [Option.some.injEq, exists_eq_left', guard_true, Option.pure_def,
      Option.bind_some]

theorem ProofD.stat_subst_eq_some_of {s s' i} {p : ProofD}
(h : p.stat = some s) : (p.subst i s').stat = some (s.subst i s') := by
  induction p generalizing s
  any_goals try simp at h; simp [←h]
  nm p₁ p₂ ih₁ ih₂
  simp at h ⊢
  choose s₁ hs₁ s₂ hs₂ h using h
  specialize ih₁ hs₁
  specialize ih₂ hs₂
  simp [ih₁, ih₂]
  split at h <;> simp at h
  nm s₁' s₂' P' Q'
  rcases h with ⟨rfl, rfl⟩
  simp

theorem Proof.subst_of {s s' i} (h : Proof s) : Proof # s.subst i s' := by
  obtain ⟨p, h⟩ := h; use p.subst i s', p.stat_subst_eq_some_of h

open Classical in noncomputable
def ProofD.shortest (p : ProofD) : ProofD :=
  Classical.epsilon # λ p₁ => p₁.stat = p.stat ∧
  ∀ (p₂ : ProofD), p₂.stat = p.stat → sizeOf p₁ ≤ sizeOf p₂

theorem ProofD.shortest_spec {p : ProofD} : p.shortest.stat = p.stat ∧
∀ (p' : ProofD), p'.stat = p.stat → sizeOf p.shortest ≤ sizeOf p' := by
  unfold shortest
  apply Classical.epsilon_spec (p := λ (p₁ : ProofD) => p₁.stat = p.stat ∧
    ∀ (p₂ : ProofD), p₂.stat = p.stat → sizeOf p₁ ≤ sizeOf p₂)
  have h₁ : ∃ (n : ℕ) (p' : ProofD), p'.stat = p.stat ∧ sizeOf p' = n
  · simp
  replace h₁ := Nat.exi_least_of_exi h₁
  obtain ⟨n, ⟨p', h₁, rfl⟩, h₂⟩ := h₁
  use p', h₁
  intro p₂ h₃
  simp at h₂
  by_contra! h₄
  exact h₂ _ h₄ _ h₃ rfl

@[simp]
theorem ProofD.stat_shortest {p : ProofD} : p.shortest.stat = p.stat :=
  shortest_spec.1

theorem Proof.exi_shortest {s} {h : Proof s} : ∃ (p₁ : ProofD), p₁.stat = some s ∧
∀ (p₂ : ProofD), p₂.stat = some s → sizeOf p₁ ≤ sizeOf p₂ := by
  obtain ⟨p, h⟩ := h
  use p.shortest
  rw [←h]
  exact ProofD.shortest_spec

theorem Proof.exi_wf {s} {h : Proof s} : ∃ (p : ProofD), p.WF ∧ p.stat = some s := by
  obtain ⟨p, h⟩ := h; exact ⟨p, ⟨s, h⟩, h⟩

@[simp]
def Stat.eval (s : Stat) (f : ℕ → Bool) : Bool := 
  match s with
  | .var i => f i
  | .not a => !a.eval f
  | .imp a b => !a.eval f ∨ b.eval f

def Stat.Tauto (s : Stat) : Prop :=
  ∀ f, s.eval f

theorem tauto_of_proof {s} (h : Proof s) : s.Tauto := by
  obtain ⟨p, h⟩ := h
  intro f
  induction p generalizing s
  iterate 3 simp at h; subst h; simp; grind
  nm p₁ p₂ ih₁ ih₂
  rw [stat_mp_eq_some_iff] at h
  choose s₁ h₁ h₂ using h
  specialize ih₁ h₁
  specialize ih₂ h₂
  simp [ih₂] at ih₁
  exact ih₁

@[simp]
theorem not_proof_var {i} : ¬Proof (.var i) := by
  intro h
  replace h := tauto_of_proof h
  specialize h # λ _ => false
  simp at h

@[simp]
theorem not_proof_not_var {i} : ¬Proof (.not # .var i) := by
  intro h
  replace h := tauto_of_proof h
  specialize h # λ _ => true
  simp at h

def Stat.true : Stat :=
  .imp (.var 0) (.var 0)

def Stat.false : Stat :=
  .not .true

@[simp]
theorem proof_true : Proof Stat.true :=
  imp_refl

@[simp]
theorem tauto_true : Stat.true.Tauto := by
  intro f; simp [Stat.true]