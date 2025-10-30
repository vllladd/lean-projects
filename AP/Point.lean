import AP.Util

variable {α : Type*}

@[ext]
structure Point (α : Type*) where
  x : α
  y : α
deriving Inhabited, DecidableEq, Fintype

abbrev PointN := Point ℕ
abbrev PointZ := Point ℤ
abbrev PointR := Point ℝ

namespace Point

@[simp] def ofProd (p : α × α) : Point α := ⟨p.1, p.2⟩
@[simp] def toProd (p : Point α) : α × α := ⟨p.1, p.2⟩

instance [ha : Repr α] : Repr (Point α) := by
  constructor
  rintro ⟨x, y⟩ prec
  exact (x, y).repr prec

instance [Hashable α] : Hashable (Point α) :=
  ⟨λ p => hash p.toProd⟩

section LinearOrder

variable [ha : LinearOrder α]

@[simp]
def le (a b : Point α) : Prop :=
  a.y < b.y ∨ (a.y = b.y ∧ a.x ≤ b.x)

@[simp]
def lt (a b : Point α) : Prop :=
  a.y < b.y ∨ (a.y = b.y ∧ a.x < b.x)

instance {a b : Point α} : Decidable # le a b :=
  match h : compare a.y b.y with
  | .lt => .isTrue # by rw [compare_lt_iff_lt] at h; left; exact h
  | .gt => .isFalse # by
    rw [compare_gt_iff_gt] at h; simp
    use le_of_lt h; intro h₁; simp [h₁] at h
  | .eq => match h₁ : decide # a.x ≤ b.x with
    | true => .isTrue # by
      simp at h₁; rw [compare_eq_iff_eq] at h
      right; simp_all only [and_self]
    | false => .isFalse # by
      simp at h₁; rw [compare_eq_iff_eq] at h
      simp_all only [le, lt_self_iff_false, true_and, false_or, not_le]

instance : LinearOrder # Point α where
  le := le
  le_refl a := by aesop
  le_trans a b c h₁ h₂ := by
    rcases h₁ with h₁ | ⟨h₁, h₃⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₄⟩
    · left; exact h₁.trans h₂
    · left; exact lt_of_lt_of_eq h₁ h₂
    · simp_all only [le, true_or]
    · right; simp [h₁, h₂]; exact h₃.trans h₄
  le_antisymm a b h₁ h₂ := by
    rcases h₁ with h₁ | ⟨h₁, h₃⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₄⟩
    · cases false_of_lt_and_lt h₁ h₂
    · simp_all only [lt_self_iff_false]
    · simp_all only [lt_self_iff_false]
    · ext; exact le_antisymm h₃ h₄; exact h₁
  le_total a b := by
    rcases a, b with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
    simp [or_iff_not_imp_left]
    intro h₁ h₂ h₃
    have h₄ := le_antisymm h₃ h₁
    specialize h₂ h₄
    use h₄.symm, le_of_lt h₂
  toDecidableLE a b := (inferInstance : Decidable # le a b)

theorem le_def {a b : Point α} : a ≤ b ↔ le a b := by rfl

theorem lt_def {a b : Point α} : a < b ↔ lt a b := by
  rw [lt_iff_le_and_ne]
  simp [le_def]
  rcases a, b with ⟨⟨x₁, y₁⟩, x₂, y₂⟩
  have := @lt_of_le_of_ne α _
  have := @le_of_lt α _
  simp_all only [ne_eq, mk.injEq, not_and]
  apply Iff.intro
  · intro a
    obtain ⟨left, right⟩ := a
    cases left with
    | inl h => simp_all only [true_or]
    | inr h_1 => simp_all only [not_true_eq_false, imp_false, lt_self_iff_false,
      not_false_eq_true, and_self, or_true]
  · intro a
    cases a with
    | inl h =>
      simp_all only [true_or, true_and]
      intro a
      subst a
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [lt_self_iff_false]
    | inr h_1 =>
      simp_all only [lt_self_iff_false, and_self, or_true, not_true_eq_false,
        imp_false, true_and]
      obtain ⟨left, right⟩ := h_1
      subst left
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [lt_self_iff_false]

@[simp]
theorem mk_le {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) ≤ ⟨x₂, y₂⟩ ↔ Point.le ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
theorem mk_lt {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) < ⟨x₂, y₂⟩ ↔ Point.lt ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by
  simp [lt_def]

-- @[simp]
-- theorem mk_min {x₁ y₁ x₂ y₂} :
-- (⟨x₁, y₁⟩ : Point α) ⊓ ⟨x₂, y₂⟩ = Point.min ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := rfl
-- 
-- @[simp]
-- theorem mk_max {x₁ y₁ x₂ y₂} :
-- (⟨x₁, y₁⟩ : Point α) ⊔ ⟨x₂, y₂⟩ = Point.max ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := rfl

-- #check 0 #exit

end LinearOrder

section Ring

def add [Add α] (a b : Point α) : Point α :=
  ⟨a.x + b.x, a.y + b.y⟩

instance [Add α] : Add (Point α) := ⟨add⟩

theorem add_def [Add α] {a b : Point α} : a + b = ⟨a.1 + b.1, a.2 + b.2⟩ := rfl

@[simp] theorem mk_add_mk [Add α] {x₁ y₁ x₂ y₂ : α} :
(⟨x₁, y₁⟩ : Point α) + ⟨x₂, y₂⟩ = ⟨x₁ + x₂, y₁ + y₂⟩ := rfl

@[simp] theorem x_add [ha : Add α] {p₁ p₂ : Point α} : (p₁ + p₂).x = p₁.x + p₂.x := rfl
@[simp] theorem y_add [ha : Add α] {p₁ p₂ : Point α} : (p₁ + p₂).y = p₁.y + p₂.y := rfl

def sub [Sub α] (a b : Point α) : Point α :=
  ⟨a.x - b.x, a.y - b.y⟩

instance [Sub α] : Sub (Point α) := ⟨sub⟩

theorem sub_def [Sub α] {a b : Point α} : a - b = ⟨a.1 - b.1, a.2 - b.2⟩ := rfl

@[simp] theorem mk_sub_mk [Sub α] {x₁ y₁ x₂ y₂ : α} :
(⟨x₁, y₁⟩ : Point α) - ⟨x₂, y₂⟩ = ⟨x₁ - x₂, y₁ - y₂⟩ := rfl

@[simp] theorem x_sub [ha : Sub α] {p₁ p₂ : Point α} : (p₁ - p₂).x = p₁.x - p₂.x := rfl
@[simp] theorem y_sub [ha : Sub α] {p₁ p₂ : Point α} : (p₁ - p₂).y = p₁.y - p₂.y := rfl

def mul [Mul α] (a b : Point α) : Point α :=
  ⟨a.x * b.x, a.y * b.y⟩

instance [Mul α] : Mul (Point α) := ⟨mul⟩

theorem mul_def [Mul α] {a b : Point α} : a * b = ⟨a.1 * b.1, a.2 * b.2⟩ := rfl

@[simp] theorem mk_mul_mk [Mul α] {x₁ y₁ x₂ y₂ : α} :
(⟨x₁, y₁⟩ : Point α) * ⟨x₂, y₂⟩ = ⟨x₁ * x₂, y₁ * y₂⟩ := rfl

@[simp] theorem x_mul [ha : Mul α] {p₁ p₂ : Point α} : (p₁ * p₂).x = p₁.x * p₂.x := rfl
@[simp] theorem y_mul [ha : Mul α] {p₁ p₂ : Point α} : (p₁ * p₂).y = p₁.y * p₂.y := rfl

def div [Div α] (a b : Point α) : Point α :=
  ⟨a.x / b.x, a.y / b.y⟩

instance [Div α] : Div (Point α) := ⟨div⟩

theorem div_def [Div α] {a b : Point α} : a / b = ⟨a.1 / b.1, a.2 / b.2⟩ := rfl

@[simp] theorem mk_div_mk [Div α] {x₁ y₁ x₂ y₂ : α} :
(⟨x₁, y₁⟩ : Point α) / ⟨x₂, y₂⟩ = ⟨x₁ / x₂, y₁ / y₂⟩ := rfl

@[simp] theorem x_div [ha : Div α] {p₁ p₂ : Point α} : (p₁ / p₂).x = p₁.x / p₂.x := rfl
@[simp] theorem y_div [ha : Div α] {p₁ p₂ : Point α} : (p₁ / p₂).y = p₁.y / p₂.y := rfl

instance [ha : Zero α] : Zero (Point α) where
  zero := ⟨0, 0⟩

theorem zero_def [ha : Zero α] : (0 : Point α) = ⟨0, 0⟩ := rfl

instance [ha : One α] : One (Point α) where
  one := ⟨1, 1⟩

theorem one_def [ha : One α] : (1 : Point α) = ⟨1, 1⟩ := rfl

instance [ha : NatCast α] : NatCast (Point α) where
  natCast := λ n => ⟨n, n⟩

theorem natCast_def [ha : NatCast α] {n : ℕ} : (n : Point α) = ⟨n, n⟩ := rfl

instance [ha : IntCast α] : IntCast (Point α) where
  intCast := λ n => ⟨n, n⟩

theorem intCast_def [ha : IntCast α] {n : ℤ} : (n : Point α) = ⟨n, n⟩ := rfl

instance [ha : Neg α] : Neg (Point α) where
  neg := λ ⟨x, y⟩ => ⟨-x, -y⟩

theorem neg_def [ha : Neg α] {p : Point α} : -p = ⟨-p.1, -p.2⟩ := rfl

@[simp]
theorem neg_mk [ha : Neg α] {x y : α} : -(⟨x, y⟩ : Point α) = ⟨-x, -y⟩ := rfl

@[simp] theorem x_neg [ha : Neg α] {p : Point α} : (-p).x = -p.x := rfl
@[simp] theorem y_neg [ha : Neg α] {p : Point α} : (-p).y = -p.y := rfl

-----

instance [ha : AddSemigroup α] : AddSemigroup (Point α) where
  add_assoc := λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩ => by simp [add_assoc]

instance [ha : AddZeroClass α] : AddZeroClass (Point α) where
  zero_add := λ ⟨x, y⟩ => by simp [zero_def]
  add_zero := λ ⟨x, y⟩ => by simp [zero_def]

instance [ha : AddMonoid α] : AddMonoid (Point α) where
  nsmul := λ c ⟨x, y⟩ => ⟨c • x, c • y⟩
  nsmul_zero := by rintro ⟨x, y⟩; simp; rfl
  nsmul_succ := by rintro n ⟨x, y⟩; simp; constructor <;> apply succ_nsmul

theorem nsmul_def [ha : AddMonoid α] {c : ℕ} {p : Point α} :
c • p = ⟨c • p.1, c • p.2⟩ := rfl

@[simp]
theorem nsmul_mk [ha : AddMonoid α] {c : ℕ} {x y : α} :
c • (⟨x, y⟩ : Point α) = ⟨c • x, c • y⟩ := rfl

instance [ha : SubNegMonoid α] : SubNegMonoid (Point α) where
  zsmul := λ c ⟨x, y⟩ => ⟨c • x, c • y⟩
  zsmul_zero' := by rintro ⟨x, y⟩; simp; rfl
  zsmul_succ' := by
    rintro n ⟨x, y⟩
    simp only [Nat.succ_eq_add_one, natCast_zsmul, mk_add_mk, mk.injEq]
    constructor <;> apply succ_nsmul
  zsmul_neg' := by
    rintro n ⟨x, y⟩; simp
    constructor <;> have h := @ha.zsmul_neg' <;> simp at h <;> apply h
  sub_eq_add_neg := λ ⟨x₁, y1⟩ ⟨x₂, y₂⟩ => by simp [sub_eq_add_neg]

theorem zsmul_def [ha : SubNegMonoid α] {c : ℤ} {p : Point α} :
c • p = ⟨c • p.1, c • p.2⟩ := rfl

@[simp]
theorem zsmul_mk [ha : SubNegMonoid α] {c : ℤ} {x y : α} :
c • (⟨x, y⟩ : Point α) = ⟨c • x, c • y⟩ := rfl

instance [ha : AddCommMagma α] : AddCommMagma (Point α) where
  add_comm := λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => by simp [add_comm]

instance [ha : Distrib α] : Distrib (Point α) where
  left_distrib := λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩ => by simp [left_distrib]
  right_distrib := λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩ => by simp [right_distrib]

instance [ha : MulZeroClass α] : MulZeroClass (Point α) where
  zero_mul := λ ⟨x, y⟩ => by simp [zero_def]
  mul_zero := λ ⟨x, y⟩ => by simp [zero_def]

instance [ha : Semigroup α] : Semigroup (Point α) where
  mul_assoc := λ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩ => by simp [mul_assoc]

instance [ha : MulOneClass α] : MulOneClass (Point α) where
  one_mul := λ ⟨x, y⟩ => by simp [one_def]
  mul_one := λ ⟨x, y⟩ => by simp [one_def]

instance [ha : AddMonoidWithOne α] : AddMonoidWithOne (Point α) where
  natCast_zero := by simp [natCast_def, zero_def]
  natCast_succ := λ n => by simp [natCast_def, one_def]

instance [ha : AddGroup α] : AddGroup (Point α) where
  neg_add_cancel := λ ⟨x, y⟩ => by simp [zero_def]

instance [ha : AddGroupWithOne α] : AddGroupWithOne (Point α) where
  intCast_ofNat := λ n => by simp [intCast_def, natCast_def]
  intCast_negSucc := λ n => by
    simp [intCast_def, neg_def]; constructor <;> rfl

instance [ha : AddCommSemigroup α] : AddCommSemigroup (Point α) where
instance [ha : AddCommMonoid α] : AddCommMonoid (Point α) where
instance [ha : NonUnitalNonAssocSemiring α] :
  NonUnitalNonAssocSemiring (Point α) where
instance [ha : SemigroupWithZero α] : SemigroupWithZero (Point α) where
instance [ha : NonUnitalSemiring α] : NonUnitalSemiring (Point α) where
instance [ha : MulZeroOneClass α] : MulZeroOneClass (Point α) where
instance [ha : AddCommMonoidWithOne α] : AddCommMonoidWithOne (Point α) where
instance [ha : NonAssocSemiring α] : NonAssocSemiring (Point α) where
instance [ha : Monoid α] : Monoid (Point α) where
instance [ha : MonoidWithZero α] : MonoidWithZero (Point α) where
instance [ha : Semiring α] : Semiring (Point α) where
instance [ha : AddCommGroup α] : AddCommGroup (Point α) where
instance [ha : Ring α] : Ring (Point α) where

end Ring

theorem eq_zero_iff [Zero α] {p : Point α} : p = 0 ↔ p.1 = 0 ∧ p.2 = 0 := by
  cases p; simp [zero_def]

theorem zero_eq_iff [Zero α] {p : Point α} : 0 = p ↔ p.1 = 0 ∧ p.2 = 0 := by
  rw [eq_comm]; exact eq_zero_iff

@[simp]
theorem mk_eq_zero_iff [Zero α] {x y : α} : (⟨x, y⟩ : Point α) = 0 ↔ x = 0 ∧ y = 0 :=
  eq_zero_iff

@[simp]
theorem zero_eq_mk_iff [Zero α] {x y : α} : 0 = (⟨x, y⟩ : Point α) ↔ x = 0 ∧ y = 0 :=
  zero_eq_iff

section StrictMono

variable [ha₁ : LinearOrder α] [ha₂ : Ring α]

instance [ha : AddLeftStrictMono α] : AddLeftStrictMono (Point α) := by
  constructor; rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩; simp

instance [ha : AddRightStrictMono α] : AddRightStrictMono (Point α) := by
  constructor; rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩; simp [Function.swap]

instance [ha : MulLeftStrictMono α] : MulLeftStrictMono (Point α) := by
  constructor; rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩; simp; rintro (h | ⟨rfl, h⟩)
  · left; exact mul_lt_mul_left' h y₁
  · right; use rfl; exact mul_lt_mul_left' h x₁

instance [ha : MulRightStrictMono α] : MulRightStrictMono (Point α) := by
  constructor; rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩; simp [Function.swap]
  rintro (h | ⟨rfl, h⟩)
  · left; exact mul_lt_mul_right' h y₁
  · right; use rfl; exact mul_lt_mul_right' h x₁

end StrictMono

-- instance [ha : SubtractionMonoid α] : SubtractionMonoid (Point α) := by
--   constructor
--   · rintro ⟨x, y⟩; simp
--   · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩; simp
--   · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩; simp; intro h₁ h₂
--     constructor <;> apply neg_eq_of_add_eq_zero_right <;> assumption

theorem ofNat_def [ha : Ring α] {n} :
(OfNat.ofNat n : Point α) = ⟨OfNat.ofNat n, OfNat.ofNat n⟩ := by
  induction n; simp; nm n ih
  rw [Lean.Grind.Semiring.ofNat_succ, ih]
  nth_rw 2 3 [Lean.Grind.Semiring.ofNat_succ]; rfl

@[simp]
theorem add_self_eq_zero_iff
[ha₁ : Ring α] [ha₂ : NoZeroDivisors α] [ha₃ : InjectiveOfNat α]
{a : Point α} : a + a = 0 ↔ a = 0 := by rcases a with ⟨x, y⟩; simp

section dist

variable [ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : IsOrderedAddMonoid α]
  {a b c d e : Point α}

def dist [LinearOrder α] [Ring α] (a b : Point α) : α :=
  max |(a.x : α) - b.x| |(a.y : α) - b.y|

omit ha₃ in @[simp]
theorem mk_dist_mk {x₁ y₁ x₂ y₂} : (⟨x₁, y₁⟩ : Point α).dist ⟨x₂, y₂⟩ =
max |x₁ - x₂| |y₁ - y₂| := rfl

omit ha₃ in
@[symm]
theorem dist_comm : a.dist b = b.dist a := by
  simp [dist, abs_sub_comm]

@[simp]
theorem dist_self : a.dist a = 0 := by
  simp [dist]

@[simp]
theorem dist_eq_zero_iff : a.dist b = 0 ↔ a = b := by
  refine' ⟨λ h => _, λ h => by simp [h]⟩
  rcases a, b with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
  simp [dist, max_eq_iff] at h; simp
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁] at h₂ <;>
    constructor <;> apply eq_of_sub_eq_zero <;> assumption

@[simp]
theorem triangle : dist a c ≤ dist a b + dist b c := by
  simp [dist]; constructor
  · have h := abs_add_le_max_add_max (a.x - b.x) (b.x - c.x) (|a.y - b.y|) (|b.y - c.y|)
    simp at h; nth_rw 2 [max_comm]; exact h
  · have h := abs_add_le_max_add_max (a.y - b.y) (b.y - c.y) (|a.x - b.x|) (|b.x - c.x|)
    simp at h; nth_rw 1 [max_comm]; exact h

omit ha₃ in
theorem dist_le_iff {a b : Point α} {d : α} :
a.dist b ≤ d ↔ max (|a.x - b.x|) (|a.y - b.y|) ≤ d := by
  simp [dist]

@[simp]
theorem dist_le_zero_iff : a.dist b ≤ 0 ↔ a = b := by
  refine' ⟨λ h => _, λ h => by simp [h]⟩
  rcases a, b with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩; simp at h ⊢
  constructor <;> apply eq_of_sub_eq_zero <;> simp [h]

@[simp] theorem zero_le_dist : 0 ≤ a.dist b := by simp [dist]
@[simp] theorem not_dist_lt_zero : ¬(a.dist b < 0) := by simp

omit ha₃

@[simp]
theorem dist_add_left_cancel : (c + a).dist (c + b) = a.dist b := by
  cases a; cases b; cases c; simp only [dist, mk_add_mk, add_sub_add_left_eq_sub]

@[simp]
theorem dist_add_right_cancel : (a + c).dist (b + c) = a.dist b := by
  rw [add_comm a, add_comm b]; simp

include ha₃

end dist

section rect

variable [ha₁ : LocallyFiniteOrderList α] [ha₂ : Ring α] [ha₃ : IsOrderedAddMonoid α]
  {a b c d e : Point α}

def rect (x₁ y₁ x₂ y₂ : α) : List (Point α) := do
  let y ← List.icc y₁ y₂
  let x ← List.icc x₁ x₂
  return ⟨x, y⟩

def rectRel (p : Point α) (dx₁ dy₁ dx₂ dy₂ : α) : List (Point α) :=
  rect (p.x - dx₁) (p.y - dy₁) (p.x + dx₂) (p.y + dy₂)

def nbhd (a : Point α) (d : α) : List (Point α) :=
  a.rectRel d d d d

omit ha₂ ha₃ in @[simp]
theorem mem_rect {a : Point α} {x₁ x₂ y₁ y₂} : a ∈ rect x₁ y₁ x₂ y₂ ↔
x₁ ≤ a.x ∧ a.x ≤ x₂ ∧ y₁ ≤ a.y ∧ a.y ≤ y₂ := by
  rcases a with ⟨x, y⟩; simp [rect]; aesop

omit ha₃ in @[simp]
theorem mem_rectRel {a b : Point α} {dx₁ dx₂ dy₁ dy₂} : b ∈ a.rectRel dx₁ dy₁ dx₂ dy₂ ↔
a.x - dx₁ ≤ b.x ∧ b.x ≤ a.x + dx₂ ∧ a.y - dy₁ ≤ b.y ∧ b.y ≤ a.y + dy₂ := mem_rect

@[simp]
theorem mem_nbhd {a b : Point α} {d} : b ∈ a.nbhd d ↔ a.dist b ≤ d := by
  simp [nbhd, dist, abs_le, add_comm d]; tauto

theorem finite_setOf_dist_le {c : PointZ} {d : ℕ} :
{p : PointZ | p.dist c ≤ d}.Finite := by
  apply Set.finite_of_subset_finset # List.toFinset # c.nbhd d; simp [dist_comm]

end rect

section le

variable [ha₁ : LinearOrder α] [ha₂ : Ring α]
variable [ha₃ : IsOrderedAddMonoid α] [ha₄ : ZeroLEOneClass α] [ha₅ : NeZero (1 : α)]

omit ha₃ ha₄ ha₅ in @[simp]
theorem forall_le_iff_le_xx_iff₁ {a b : α} :
(∀ (p : Point α), p.x ≤ a ↔ p.x ≤ b) ↔ a = b := by
  symm; constructor; rintro rfl; simp; intro h
  have h₁ := h ⟨a, 0⟩; have h₂ := h ⟨b, 0⟩
  simp at h₁ h₂; exact le_antisymm h₁ h₂

omit ha₃ ha₄ ha₅ in @[simp]
theorem forall_le_iff_le_yy_iff₁ {a b : α} :
(∀ (p : Point α), p.y ≤ a ↔ p.y ≤ b) ↔ a = b := by
  symm; constructor; rintro rfl; simp; intro h
  have h₁ := h ⟨0, a⟩; have h₂ := h ⟨0, b⟩
  simp at h₁ h₂; exact le_antisymm h₁ h₂

@[simp]
theorem forall_le_iff_le_xy_iff₁ {a b : α} :
(∀ (p : Point α), p.x ≤ a ↔ p.y ≤ b) ↔ False := by
  simp [not_iff]; use ⟨a + 1, b⟩; simp

@[simp]
theorem forall_le_iff_le_yx_iff₁ {a b : α} :
(∀ (p : Point α), p.y ≤ a ↔ p.x ≤ b) ↔ False := by
  simp [not_iff]; use ⟨b, a + 1⟩; simp

@[simp]
theorem forall_le_iff_le_xx_iff₂ {a b : α} :
(∀ (p : Point α), a ≤ p.x ↔ p.x ≤ b) ↔ False := by
  simp [not_iff]; use ⟨min a b - 1, 0⟩; simp

@[simp]
theorem forall_le_iff_le_yy_iff₂ {a b : α} :
(∀ (p : Point α), a ≤ p.y ↔ p.y ≤ b) ↔ False := by
  simp [not_iff]; use ⟨0, min a b - 1⟩; simp

@[simp]
theorem forall_le_iff_le_xy_iff₂ {a b : α} :
(∀ (p : Point α), a ≤ p.x ↔ p.y ≤ b) ↔ False := by
  simp [not_iff]; use ⟨a, b + 1⟩; simp

@[simp]
theorem forall_le_iff_le_yx_iff₂ {a b : α} :
(∀ (p : Point α), a ≤ p.y ↔ p.x ≤ b) ↔ False := by
  simp [not_iff]; use ⟨b + 1, a⟩; simp

@[simp]
theorem forall_le_iff_le_xx_iff₃ {a b : α} :
(∀ (p : Point α), p.x ≤ a ↔ b ≤ p.x) ↔ False := by
  simp [not_iff]; use ⟨max a b + 1, 0⟩; simp; apply le_of_lt; simp

@[simp]
theorem forall_le_iff_le_yy_iff₃ {a b : α} :
(∀ (p : Point α), p.y ≤ a ↔ b ≤ p.y) ↔ False := by
  simp [not_iff]; use ⟨0, max a b + 1⟩; simp; apply le_of_lt; simp

@[simp]
theorem forall_le_iff_le_xy_iff₃ {a b : α} :
(∀ (p : Point α), p.x ≤ a ↔ b ≤ p.y) ↔ False := by
  simp [not_iff]; use ⟨a, b - 1⟩; simp

@[simp]
theorem forall_le_iff_le_yx_iff₃ {a b : α} :
(∀ (p : Point α), p.y ≤ a ↔ b ≤ p.x) ↔ False := by
  simp [not_iff]; use ⟨b - 1, a⟩; simp

omit ha₃ ha₄ ha₅ in @[simp]
theorem forall_le_iff_le_xx_iff₄ {a b : α} :
(∀ (p : Point α), a ≤ p.x ↔ b ≤ p.x) ↔ a = b := by
  symm; constructor; rintro rfl; simp; intro h
  have h₁ := h ⟨a, 0⟩; have h₂ := h ⟨b, 0⟩
  simp at h₁ h₂; exact le_antisymm h₂ h₁

omit ha₃ ha₄ ha₅ in @[simp]
theorem forall_le_iff_le_yy_iff₄ {a b : α} :
(∀ (p : Point α), a ≤ p.y ↔ b ≤ p.y) ↔ a = b := by
  symm; constructor; rintro rfl; simp; intro h
  have h₁ := h ⟨0, a⟩; have h₂ := h ⟨0, b⟩
  simp at h₁ h₂; exact le_antisymm h₂ h₁

@[simp]
theorem forall_le_iff_le_xy_iff₄ {a b : α} :
(∀ (p : Point α), a ≤ p.x ↔ b ≤ p.y) ↔ False := by
  simp [not_iff]; use ⟨a, b - 1⟩; simp

@[simp]
theorem forall_le_iff_le_yx_iff₄ {a b : α} :
(∀ (p : Point α), a ≤ p.y ↔ b ≤ p.x) ↔ False := by
  simp [not_iff]; use ⟨b - 1, a⟩; simp

end le

section

variable [ha₁ : LinearOrder α] [ha₂ : Ring α]

@[simp]
theorem zero_le_dist' [ha₃ : AddLeftMono α]
{a b : Point α} : 0 ≤ a.dist b := by simp [dist]

@[simp]
theorem max_dist_zero [ha₃ : AddLeftMono α]
{a b : Point α} : max (a.dist b) 0 = a.dist b := by
  simp

instance [ha₃ : AddLeftMono α] : AddLeftMono # Point α := by
  constructor; rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩; simp

instance [ha₃ : AddRightMono α] : AddRightMono # Point α := by
  constructor; rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩; simp [Function.swap]

end

theorem forall_iff {p : Point α → Prop} : (∀ pt, p pt) ↔ ∀ x y, p ⟨x, y⟩ :=
  ⟨λ h x y => h ⟨x, y⟩, λ h ⟨x, y⟩ => h x y⟩

theorem exi_iff {p : Point α → Prop} : (∃ pt, p pt) ↔ ∃ x y, p ⟨x, y⟩ := by
  rw [iff_iff_not]; push_neg; exact forall_iff