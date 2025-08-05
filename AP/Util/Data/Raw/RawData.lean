import AP.Util.Data.Set

inductive RawData where
| lit : ℤ → RawData
| mp : List (ℤ × RawData) → RawData
deriving Inhabited

namespace RawData

@[class]
inductive Valid : RawData → Prop where
| lit : {n : ℕ} → Valid (lit n)
| mp : {xs : List _} → xs.Sorted (·.1 < ·.1) → (∀ x ∈ xs, x.2.Valid) → Valid (mp xs)

#check 0 #exit

def depth (d : RawData) : ℕ :=
  @d.recOn (λ _ => ℕ) (λ _ => List ℕ) (λ _ => ℕ)
  (λ _ => 0) (λ _ xs => 1 + xs.max?.getD 0) []
  (λ _ _ n ns => n :: ns) (λ _ _ n => n)

#check 0 #exit

def valid : RawData → Bool
| lit _ => true
| mp xs => xs.Sorted (·.1 < ·.1) && xs.all (·.2.valid)