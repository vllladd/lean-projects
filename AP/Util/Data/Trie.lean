import AP.Util.Data.Set

namespace Trie

open Std

inductive Raw (α β : Type*) [DecidableEq α] [Hashable α] where
| mk : Option β → DHashMap.Raw α (λ _ => Raw α β) → Raw α β
deriving Repr

variable {α β : Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α]

def Raw.val : Raw α β → Option β
| .mk val _ => val

def Raw.mp : Raw α β → DHashMap.Raw α (λ _ => Raw α β)
| .mk _ mp => mp

@[simp]
theorem Raw.val_mk {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw α β)} :
(mk val mp).val = val := rfl

@[simp]
theorem Raw.mp_mk {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw α β)} :
(mk val mp).mp = mp := rfl

-- private noncomputable
-- def Raw.toSet_aux (t : Raw α β) : Set (Raw α β) :=
--   {t' | ∃ k, t.mp.get? k = some t'}
-- 
-- private noncomputable
-- def Raw.toSet_bind_aux (s : Set (Raw α β)) : Set (Raw α β) :=
--   ⋃ t ∈ s, t.toSet_aux
-- 
-- private
-- theorem exi_depth_aux {t : Raw α β} : ∃ n, Raw.toSet_bind_aux^[n] {t} = ∅ := by
--   have := @t.recOn

noncomputable
def Raw.depthAux (t : Raw α β) : ℕ :=
  let f := @t.recOn
  @f (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ) (λ _ => ℕ)
    (λ _ _ n => n)
    (λ _ _ n => n)
    (λ _ n => n)
    0 (λ _ _ n m => max n m)
    0 (λ _ _ _ n m => max (n + 1) m)

-- #check 0 #exit

-- theorem aux₁ {α : Type*} {β : α → Type*} [ha₁ : DecidableEq α] [ha₂ : Hashable α] :
-- ((DHashMap.Raw.ofList (α := α) (β := β)) []).2.toList = [] := by
--   simp

-- #check 0 #exit

-- example : Raw.depthAux (α := ℕ) (β := ℕ) (Raw.mk none (.ofList [])) = 0 := by
--   simp only [Raw.depthAux, DHashMap.Raw.ofList_nil]
--   generalize hx : (∅ : DHashMap.Raw _ _).2.toList = xs
--   replace hx : ∀ b ∈ xs, b.toList = []
--   · intro b hb
--     rw [List.eq_nil_iff_forall_not_mem]
--     rintro ⟨k, t⟩
--     subst hx
--     simp at hb
--     sorry
--   induction xs; rfl
--   nm b bs ih
--   simp only [Nat.max_eq_zero_iff]
--   simp at hx
--   rcases hx with ⟨h₁, h₂⟩
--   specialize ih h₂
--   simp [ih]
--   cases b; rfl
--   nm k t b
--   simp at h₁

theorem Raw.depthAux_le {val : Option β} {mp : DHashMap.Raw α (λ _ => Raw α β)}
{k : α} {t : Raw α β} (h : mp.get? k = t) : t.depthAux < (Raw.mk val mp).depthAux := by
  sorry

-- #check 0 #exit

set_option linter.unusedVariables false in
def Raw.rec' {γ : Raw α β → Sort*}
(motive : ∀ (val : Option β) (mp : DHashMap.Raw α (λ _ => Raw α β)),
(∀ i x, mp.get? i = some x → γ x) → γ (mk val mp)) : (t : Raw α β) → γ t
| .mk val mp => motive val mp # λ i t h => t.rec' motive
termination_by t => t.depthAux
decreasing_by exact depthAux_le h

-- #check 0 #exit

def Raw.depth : Raw α β → ℕ :=
  Raw.rec' # λ val mp f => (mp.foldlWith sorry · 0) # by
  intro acc i x h
  exact max acc # 1 + f i x sorry

end Trie