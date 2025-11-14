import AP.Util.Data.Trie.Equiv

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

structure Trie (α β : Type*) [DecidableEq α] [Hashable α] where
  inner : Quotient # Trie.Raw.Setoid (α := α) (β := β)

namespace Trie

open Std

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable {t t' t₁ t₂ t₃ : Trie α β}

@[simp]
def ofRaw (t : Raw α β) : Trie α β :=
  ⟨Quotient.mk _ t⟩

def empty : Trie α β :=
  ofRaw ∅

instance : EmptyCollection # Trie α β := ⟨empty⟩
theorem empty_def : (∅ : Trie α β) = empty := rfl

def depth (t : Trie α β) : ℕ :=
  t.inner.lift Raw.depth # λ _ _ => Raw.Equiv.depth_eq

@[simp]
theorem depth_empty : (∅ : Trie α β).depth = 0 := by
  simp [depth, empty_def, empty]

theorem option_map_ofRaw_get?_eq_of_equiv {a b : Raw α β} {k}
(h₁ : a.Equiv b) : Option.map ofRaw (a.get? k) = Option.map ofRaw (b.get? k) := by
  ext c
  rcases c with ⟨c⟩
  simp
  constructor <;> rintro ⟨c, h₂, rfl⟩
  · replace h₂ := h₁.get? h₂
    choose d h₂ h₃ using h₂
    use d, h₂
    simpa
  · replace h₂ := h₁.get?' h₂
    choose d h₂ h₃ using h₂
    use d, h₂
    simpa

def get? (t : Trie α β) (k : α) : Option (Trie α β) :=
  t.inner.lift (λ t => t.get? k |>.map ofRaw) # λ _ _ => option_map_ofRaw_get?_eq_of_equiv

theorem depth_lt {k} (h : t.get? k = some t') : t'.depth < t.depth := by
  rcases t, t' with ⟨⟨t⟩, ⟨t'⟩⟩
  revert h
  induction t, t' using Quotient.inductionOn₂
  nm t t'
  simp [get?, depth]
  intro a h₁ (h₂ : a.Equiv t')
  rw [←h₂.depth_eq]
  exact Raw.depth_lt h₁

def eqComp (t₁ t₂ : Trie α β) : Bool :=
  t₁.inner.liftOn₂ t₂.1 Raw.equivComp Raw.equivComp_eq_of_equiv2_expl

theorem eq_iff_eqComp : t₁ = t₂ ↔ t₁.eqComp t₂ := by
  rcases t₁, t₂ with ⟨⟨t⟩, ⟨t'⟩⟩
  induction t, t' using Quotient.inductionOn₂
  simp [eqComp]; rfl

instance : DecidableEq (Trie α β) :=
  λ _ _ => decidable_of_bool _ eq_iff_eqComp.symm

@[simp]
theorem eqComp_iff_decide_eq : t₁.eqComp t₂ ↔ decide (t₁ = t₂) := by
  simp [eq_iff_eqComp]