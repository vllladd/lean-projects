import Projects.Expr.Defs

section logic

variable {α β γ : Type*}

-- #check 0 #exit

end logic

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

def wfLex [LT α] (xs ys : List α) : Prop :=
  match compare xs.length ys.length with
  | .lt => True
  | .gt => False
  | .eq => xs < ys

theorem length_le_of_wfLex [ha : LT α] (h : wfLex xs ys) : xs.length ≤ ys.length := by
  grind [wfLex]

-- #check 0 #exit

attribute [-instance] instLinearOrderOfDecidable_projects

-- theorem wf_wfLex [H : WellFoundedRelation α] : WellFounded (wfLex (α := α)) := by
--   classical
--   constructor
--   intro xs
--   
--   by_cases ha : IsEmpty α
--   ·
--     constructor
--     intro ys h
--     simp [wfLex, eq_nil_of_isEmpty] at h
--     
--   simp at ha
--   
--   generalize hn : xs.length = n
--   induction n using Nat.strong_induction_on generalizing xs
--   nm n ih
--   
--   cases n
--   ·
--     simp at hn
--     constructor
--     simp [wfLex, hn]
--     grind
--   nm n
--   simp at ih
--   
--   rw [length_eq_succ_iff_append] at hn
--   obtain ⟨x, xs, ys, rfl, rfl⟩ := hn
--   
--   -- by_contra! h₀
--   -- have h₁ : ∀ x, ∀ y < x, ∀ (xs ys : List α), (∀ m ≤ xs.length + ys.length,
--   --   ∀ (xs : List α), xs.length = m → Acc wfLex xs) → Acc wfLex (xs ++ y :: ys)
--   -- ·
--   --   contrapose! h₀
--   --   choose x' y hy' xs' ys' h₂ h₃ using h₀
--   --   have h₁ : ∀ x, Acc (λ a b => a < b) x := H.2.1
--   
--   obtain ⟨m, hm⟩ := hv λ (a b : α) => if Relation.TransGen H.rel a b then b else a
--   letI : Max α := ⟨m⟩
--   
--   have h₁ : ∀ x, Acc (λ a b => a < b) x := H.2.1
--   conv at h₁ => right; rw [←acc_transGen_iff]
--   generalize hy : (xs ++ x :: ys).max! = y
--   replace hy := le_of_eq hy
--   specialize h₁ y
--   
--   induction h₁ generalizing x xs ys
--   clear y
--   nm y h₁ ih₁
--   
--   -- clear x
--   -- nm x hx ih₁
--   
--   constructor
--   intro zs h₂
--   
--   have h₃ := length_le_of_wfLex h₂
--   rw [Nat.le_iff_lt_or_eq] at h₃
--   rcases h₃ with h₃ | h₃; grind
--   simp at h₃
--   
--   -- replace h₂ : ∃ z zs₁ zs₂, zs = zs₁ ++ z :: zs₂ ∧
--   --   zs₁.length = xs.length ∧ zs₂.length = ys.length
--   -- ·
--   --   use zs[xs.length]!, zs.take xs.length, zs.drop (xs.length + 1)
--   --   simp
--   --   rw [List.getElem?_eq_getElem (by grind)]
--   --   simp
--   --   grind
--   -- 
--   -- obtain ⟨z, zs₁, zs₂, rfl, h₂, h₃⟩ := h₂
--   
--   simp [wfLex, h₃] at h₂
--   rw [List.lt_iff_exists] at h₂
--   simp [h₃] at h₂
--   choose i h₂ h₄ h₅ using h₂
--   
--   obtain ⟨z, zs₁, zs₂, rfl, rfl⟩ := zs.exi_append_cons i (by omega)
--   simp at h₅
--   
--   apply ih₁ z
--   ·
--     -- suffices : y ≤ (xs ++ x :: ys)[zs₁.length]; linarith
--     -- apply h₅.trans_eq
--     
--     -- have H₁ : Relation.TransGen (· < ·) ((xs ++ x :: ys)[zs₁.length]'(by grind)) y
--     -- ·
--     --   exact?
--     
--     apply Relation.TransGen.lt_of_lt_of_le ((xs ++ x :: ys)[zs₁.length]'(by grind))
--     ·
--       constructor; exact h₅
--     
--     rw [or_iff_not_imp_left]
--     intro h₆
--     
--     apply Relation.TransGen.lt_of_lt_of_le (xs ++ x :: ys).max!
--     rotate_left
--     ·
--       rw [le_iff_eq_or_lt] at hy
--       rcases hy with hy | hy
--       ·
--         exact .inl hy
--       right
--       
--       constructor
--       convert hy
--     
--     suffices : (xs ++ x :: ys)[zs₁.length]'(by grind) ≤ (xs ++ x :: ys).max!
--     ·

-- #check 0 #exit

-- instance {α : Type} [H : WellFoundedRelation α] : WellFoundedRelation (List α) where
--   rel := wfLex
--   wf := wf_wfLex

-- #check 0 #exit

end List

namespace Expr

variable {a b c d e : Expr}

@[simp] theorem isNil_nil : nil.isNil := trivial
@[simp] theorem not_isNil_pair : ¬(pair a b).isNil := by simp [isNil]
@[simp] theorem not_isPair_nil : ¬nil := by simp [isPair]
@[simp] theorem isPair_pair : pair a b := trivial
@[simp] theorem fst_nil : nil.fst = nil := rfl
@[simp] theorem snd_nil : nil.snd = nil := rfl
@[simp] theorem fst_pair : (pair a b).fst = a := rfl
@[simp] theorem snd_pair : (pair a b).snd = b := rfl
@[simp] theorem toPair_nil : nil.toPair = pair nil nil := rfl
@[simp] theorem toPair_pair : (pair a b).toPair = pair a b := rfl
@[simp] theorem ite_nil : ite nil a b = b := rfl
@[simp] theorem ite_pair : ite (pair a b) c d = c := rfl
@[simp] theorem ite_toPair : ite a.toPair b c = b := rfl
@[simp] theorem not_isNil_T : ¬T.isNil := by simp [T]
@[simp] theorem isNil_F : F.isNil := trivial
@[simp] theorem isPair_T : T := trivial
@[simp] theorem not_F : ¬F := by simp [F]
@[simp] theorem not_nil_and : ¬nil.and a := by simp [and]
@[simp] theorem isPair_toPair : a.toPair := trivial
@[simp] theorem toProp_nil : nil.toProp = F := rfl
@[simp] theorem toProp_pair : (pair a b).toProp = T := rfl
@[simp] theorem isPair_toProp : a.toProp ↔ a := by cases a <;> simp
@[simp] theorem and_iff : a.and b ↔ a ∧ b := by cases a <;> simp [and]

theorem cases {p : Expr → Expr → Expr} {f : Expr → Expr}
(h : ∀ x, (p x nil).and # p x (f x).toPair) : ∀ x, p x (f x) := by
  intro x; simp at h; choose h₁ h₂ using h x; cases h : f x <;> simp_all

theorem ind {p : Expr → Expr} (h : ∀ (x : Expr), (p nil).and # p x.toPair) : ∀ x, p x := by
  intro x; simp at h; choose h₁ h₂ using h x; cases x <;> simp_all

@[simp]
theorem eq_iff : a.eq b ↔ a = b := by
  simp [eq]; split_ifs <;> simp_all

theorem le_def : a ≤ b ↔ a.sle b := by rfl
theorem lt_def : a < b ↔ a.slt b := by rfl

@[simp]
theorem le_refl : a ≤ a := by
  rw [le_def]; unfold sle; simp

@[simp]
theorem not_lt_nil : ¬a < nil := by
  simp [lt_def, slt]

@[simp]
theorem nil_le : nil ≤ a := by
  simp [le_def, sle]

@[simp]
theorem or_iff : a.or b ↔ a ∨ b := by
  cases a <;> simp [or]

@[simp]
theorem nil_lt_iff : nil < a ↔ a := by
  rw [lt_def]; unfold slt; split <;> simp [←le_def]

@[simp]
theorem pair_ne_fst : pair a b ≠ a := by
  apply ne_of_congr sizeOf; simp; omega

@[simp]
theorem pair_ne_snd : pair a b ≠ b := by
  apply ne_of_congr sizeOf; simp

@[simp]
theorem fst_ne_pair : a ≠ pair a b := by
  simp [ne_symm']

@[simp]
theorem snd_ne_pair : b ≠ pair a b := by
  simp [ne_symm']

@[simp] theorem depth'_nil : nil.depth' = 0 := rfl
@[simp] theorem depth'_pair : (pair a b).depth' = 1 + max a.depth' b.depth' := rfl

@[simp]
theorem depth'_eq_zero_iff : a.depth' = 0 ↔ a = nil := by
  cases a <;> simp

theorem depth'_le_of_le (h : a ≤ b) : a.depth' ≤ b.depth' := by
  induction b
  · simp
    rw [le_def] at h; unfold sle at h
    split_ifs at h <;> simp_all
  nm x y ih₁ ih₂
  simp
  rw [le_def] at h; unfold sle at h
  split_ifs at h with h₁
  · simp [h₁]
  split at h
  · simp
  · simp at h
  nm q w e r z h₂ h₃
  simp at h₃
  obtain ⟨rfl, rfl⟩ := h₃
  simp at h
  grind [le_def]

@[simp]
theorem not_pair_le_fst : ¬pair a b ≤ a := by
  intro h; replace h := depth'_le_of_le h; simp at h; omega

@[simp]
theorem not_pair_le_snd : ¬pair a b ≤ b := by
  intro h; replace h := depth'_le_of_le h; simp at h; omega

@[simp]
theorem lt_irrefl : ¬a < a := by
  rw [lt_def]; unfold slt; split <;> simp [←le_def]

theorem not_pair_le_nil : ¬pair a b ≤ nil := by
  simp [le_def, sle]

@[simp]
theorem le_nil_iff : a ≤ nil ↔ a = nil := by
  cases a <;> simp [not_pair_le_nil]

theorem le_iff_eq_or_lt : a ≤ b ↔ a = b ∨ a < b := by
  simp [lt_def, slt]; cases b <;> simp; nm x y
  conv => left; rw [le_def]; unfold sle
  split_ifs <;> simp_all; split <;> simp_all [←le_def]

theorem lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ ¬a.eq b := by
  simp [le_iff_eq_or_lt]
  symm; use by grind
  intro h; by_cases h₁ : a = b
  on_goal 2 => grind
  subst h₁; simp at h

theorem le_of_lt (h : a < b) : a ≤ b := by
  rw [le_iff_eq_or_lt]; tauto

@[simp]
theorem lt_pair_iff : a < pair b c ↔ a ≤ b ∨ a ≤ c := by
  rw [lt_def, slt]; simp [←le_def]

theorem depth'_lt_of_lt (h : a < b) : a.depth' < b.depth' := by
  simp [lt_iff_le_and_ne] at h
  choose h₁ h₂ using h
  induction b
  · simp [h₂] at h₁
  nm x y ih₁ ih₂
  simp
  simp [le_iff_eq_or_lt, h₂] at h₁
  simp [←le_iff_eq_or_lt] at h₁
  grind

theorem depth'_le_of_lt (h : a < b) : a.depth' ≤ b.depth' :=
  Nat.le_of_lt # depth'_lt_of_lt h

@[simp]
theorem not_pair_lt_fst : ¬pair a b < a := by
  intro h; replace h := depth'_lt_of_lt h; simp at h; omega

@[simp]
theorem not_pair_lt_snd : ¬pair a b < b := by
  intro h; replace h := depth'_lt_of_lt h; simp at h; omega

-----

-- instance : WellFoundedRelation Expr where
--   rel a b := a < b
--   wf := by sorry

-- def fn (fs : List (Expr → Expr)) (f : (Expr → Expr) → (x : Expr) → Expr) (x : Expr) : Expr :=
--   let xs : List Expr := fs.map (· x)
--   f (x := x) λ y =>
--     let ys := fs.map (· y)
--     if h : ys < xs then fn fs f y else nil
-- termination_by fs.map (· x)
-- decreasing_by

-- def f (n m : ℕ) : ℕ :=
--   match n, m with
--   | 0, 0 => 0
--   | 0, m + 1 => f 0 m
--   | n + 1, 0 => f n (n ^ 2)
--   | n + 1, m + 1 => f (n + 1) m
-- termination_by ![n, m]
-- decreasing_by

-----

-- def isTree (e : Expr) : Expr