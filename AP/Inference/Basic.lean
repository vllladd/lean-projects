import AP.Util

namespace Inference

inductive Stat where
| var : ℕ → Stat
| not : Stat → Stat
| imp : Stat → Stat → Stat
deriving Inhabited, DecidableEq

inductive Proof' : Type where
| ax₁ : Stat → Stat → Proof'
| ax₂ : Stat → Stat → Stat → Proof'
| ax₃ : Stat → Stat → Proof'
| mp : Proof' → Proof' → Proof'
deriving Inhabited, DecidableEq

@[simp]
def Proof'.stat (p : Proof') : Option Stat :=
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

structure Proof (e : Stat) : Prop where
  h : ∃ (p : Proof'), p.stat = some e

-----

theorem ax₁ (P Q : Stat) : Proof # .imp P # .imp Q P := by
  use Proof'.ax₁ P Q; rfl

theorem ax₂ (P Q R : Stat) : Proof # .imp (.imp P # .imp Q R) # .imp (.imp P Q) # .imp P R := by
  use Proof'.ax₂ P Q R; rfl

theorem ax₃ (P Q : Stat) : Proof # .imp (.imp (.not P) (.not Q)) # .imp Q P := by
  use Proof'.ax₃ P Q; rfl

theorem mp {P Q} (h₁ : Proof # .imp P Q) (h₂ : Proof P) : Proof Q := by
  obtain ⟨p₁, h₁⟩ := h₁; obtain ⟨p₂, h₂⟩ := h₂; use Proof'.mp p₁ p₂; simpa [h₁]

theorem mp' {P Q} (h₁ : Proof P) (h₂ : Proof # .imp P Q) : Proof Q :=
  mp h₂ h₁

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
def Proof'.subst (p : Proof') (i : ℕ) (s : Stat) : Proof' :=
  match p with
  | .ax₁ P Q => .ax₁ (P.subst i s) (Q.subst i s)
  | .ax₂ P Q R => .ax₂ (P.subst i s) (Q.subst i s) (R.subst i s)
  | .ax₃ P Q => .ax₃ (P.subst i s) (Q.subst i s)
  | .mp p₁ p₂ => .mp (p₁.subst i s) (p₂.subst i s)

theorem Proof'.stat_subst_eq_some_of {s s' i} {p : Proof'}
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
def Proof'.shortest (p : Proof') : Proof' :=
  Classical.epsilon # λ p₁ => p₁.stat = p.stat ∧
  ∀ (p₂ : Proof'), p₂.stat = p.stat → sizeOf p₁ ≤ sizeOf p₂

theorem Proof'.shortest_spec {p : Proof'} : p.shortest.stat = p.stat ∧
∀ (p' : Proof'), p'.stat = p.stat → sizeOf p.shortest ≤ sizeOf p' := by
  unfold shortest
  apply Classical.epsilon_spec (p := λ (p₁ : Proof') => p₁.stat = p.stat ∧
    ∀ (p₂ : Proof'), p₂.stat = p.stat → sizeOf p₁ ≤ sizeOf p₂)
  have h₁ : ∃ (n : ℕ) (p' : Proof'), p'.stat = p.stat ∧ sizeOf p' = n
  · simp
  replace h₁ := Nat.exi_least_of_exi h₁
  obtain ⟨n, ⟨p', h₁, rfl⟩, h₂⟩ := h₁
  use p', h₁
  intro p₂ h₃
  simp at h₂
  by_contra! h₄
  exact h₂ _ h₄ _ h₃ rfl

@[simp]
theorem Proof'.stat_shortest {p : Proof'} : p.shortest.stat = p.stat :=
  shortest_spec.1

theorem Proof.exi_shortest {s} {h : Proof s} : ∃ (p₁ : Proof'), p₁.stat = some s ∧
∀ (p₂ : Proof'), p₂.stat = some s → sizeOf p₁ ≤ sizeOf p₂ := by
  obtain ⟨p, h⟩ := h
  use p.shortest
  rw [←h]
  exact Proof'.shortest_spec

-- @[simp]
-- theorem Proof.not_var {i} : ¬Proof (.var i) := by
--   intro h
--   replace h := h.exi_shortest
--   obtain ⟨p, h₁, h₂⟩ := h
--   sorry