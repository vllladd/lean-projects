import AP.Util

@[simp]
def map_list_cnd.{u} {ι α : Type u} [LinearOrder ι] [DecidableEq α] : List (ι × α) → Prop
| (x :: y :: xs) => x.1 < y.1 ∧ map_list_cnd (y :: xs)
| _ => True

@[ext]
structure Map.{u} (ι α : Type u) [LinearOrder ι] [DecidableEq α] : Type u where
  xs : List (ι × α)
  h : map_list_cnd xs

namespace Map

set_option linter.unusedVariables false
universe u
variable {ι α : Type u} [hhι : LinearOrder ι] [hhα : DecidableEq α]
set_option linter.unusedSectionVars true

def empty : Map ι α :=
  ⟨[], trivial⟩

instance : EmptyCollection (Map ι α) := ⟨Map.empty⟩

def insert' (x : ι × α) : List (ι × α) → List (ι × α)
| [] => [x]
| (y :: xs) => match compare x.1 y.1 with
  | .eq => x :: xs
  | .lt => x :: y :: xs
  | .gt => y :: insert' x xs

omit hhα in
@[simp]
theorem insert'_nil {x : ι × α} : insert' x [] = [x] := rfl

omit hhα in
@[simp]
theorem insert'_cons {x y : ι × α} {xs : List (ι × α)} :
insert' x (y :: xs) = (match compare x.1 y.1 with
| .eq => x :: xs
| .lt => x :: y :: xs
| .gt => y :: insert' x xs) := rfl

theorem map_list_cnd_of_cons {x : ι × α} {xs}
(h : map_list_cnd (x :: xs)) : map_list_cnd xs := by
  cases xs; trivial; exact h.2

theorem map_list_cnd_cons_of_congr {x y : ι × α} {xs}
(h₁ : map_list_cnd (x :: xs)) (h₂ : x.1 = y.1) : map_list_cnd (y :: xs) := by
  cases xs; trivial
  nm z xs
  simp at h₁ ⊢
  rwa [←h₂]

-- #check 0 #exit
-- 
-- def insert_prod (mp : Map ι α) (x : ι × α) : Map ι α := by
--   use insert' x mp.xs
--   rcases mp with ⟨xs, h⟩
--   dsimp
--   induction xs
--   · simp
--   nm y xs ih
--   rcases y with ⟨j, y⟩
--   simp
--   split <;> nm x h₁ <;> clear x
--   · rw [compare_eq_iff_eq] at h₁
--     subst h₁
--     exact map_list_cnd_cons_of_congr h rfl
--   · rw [compare_lt_iff_lt] at h₁; simp; tauto
--   rw [compare_gt_iff_gt] at h₁
--   specialize ih # map_list_cnd_of_cons h
--   cases h₂ : insert' x xs
--   · simp
--   nm z zs
--   rw [h₂] at ih
-- 
-- #check 0 #exit
-- 
-- def insert_prod (p : ι × α) : Map ι α :=
--   mp.insert p.1 p.2
-- 
-- instance : Insert (ι × α) (Map ι α) :=
--   ⟨λ p mp => mp.insert_prod p⟩
-- 
-- def ofList' (mp : Map ι α) : List (ι × α) → Map ι α
-- | [] => mp
-- | (x :: xs) => (insert x mp).ofList' xs
-- 
-- def ofList : List (ι × α) → Map ι α :=
--   empty.ofList'
-- 
-- def lookup (i : ι) : Option α := by
--   obtain ⟨⟨s, hs⟩, h⟩ := mp
--   simp at h
--   apply s.lift_out λ xs => (xs.find? λ a => a.1 = i).map Prod.snd
--   intro xs ys hx hy
--   ext x
--   simp only [Option.map_eq_some_iff, List.find?_eq_some_iff_getElem, decide_eq_true_eq,
--     Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Prod.exists,
--     exists_eq_right, exists_eq_left]
--   change List.Perm _ _ at hx hy
--   have h₁ := hx.trans hy.symm
--   
--   have h₂ : (Quotient.out s).Nodup :=
--     by
--       unfold Multiset.Nodup at hs
--       generalize_proofs h₂ at hs
--       sorry
--   
--   have h₃ := List.Perm.nodup hx.symm h₂
--   have h₄ := List.Perm.nodup hy.symm h₂
--   
--   -- rw [List.perm_iff_count] at hx hy h₁
--   
--   constructor
--   · rintro ⟨n, hn, h₅, h₆⟩
--     have h₇ : xs[n] ∈ ys :=
--       by
--         rw [List.Perm.mem_iff (l₂ := xs)]
--         simp; exact h₁.symm
--     rw [List.mem_iff_getElem] at h₇
--     obtain ⟨n', hn', h₇⟩ := h₇
--     use n', hn', by rwa [h₇]
--     intro m' hm'
--     rw [List.nodup_iff_getElem?_ne_getElem?] at h₄
--     specialize h₄ m' n' hm' hn'
--     rw [List.getElem?_eq_getElem # by linarith] at h₄
--     rw [List.getElem?_eq_getElem # by linarith] at h₄
--     simp at h₄
--     contrapose! h₄
--     
--     have h₈ : ys[n'] ∈ s.out :=
--       by
--         rw [List.Perm.mem_iff (l₂ := ys)]
--         simp; exact hy.symm
--     have h₉ : ys[m'] ∈ s.out :=
--       by
--         rw [List.Perm.mem_iff (l₂ := ys)]
--         simp; exact hy.symm
--     rw [List.mem_iff_getElem] at h₈ h₉
--     obtain ⟨k₁, hk₁, h₈⟩ := h₈
--     obtain ⟨k₂, hk₂, h₉⟩ := h₉
--     
--     rw [←h₈]
--     rw [←h₉] at h₄ ⊢
--     specialize h i x
--     
--     sorry
--   
--   sorry
-- 
-- -- h₂ : ∀ (a b : List (ι × α)), (List.isSetoid (ι × α)) a b → a.Nodup = b.Nodup
-- -- hs : Quot.liftOn s List.Nodup h₂
-- -- ⊢ (Quotient.out s).Nodup