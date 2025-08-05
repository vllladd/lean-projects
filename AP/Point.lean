import AP.Util.Main

variable {α : Type*}

@[ext]
structure Point (α : Type*) where
  x : α
  y : α

namespace Point

section LinearOrder

variable [ha : LinearOrder α]

instance : DecidableEq (Point α) := λ a b =>
match h : decide # a.x = b.x ∧ a.y = b.y with
| true => isTrue # by ext <;> simp_all
| false => isFalse # by rintro rfl; simp at h

instance [Inhabited α] : Inhabited (Point α) :=
  ⟨default, default⟩

instance [ha : Repr α] : Repr (Point α) := by
  constructor
  rintro ⟨x, y⟩ prec
  exact (x, y).repr prec

@[simp]
def lt (a b : Point α) : Prop :=
  if a.y = b.y then a.x < b.x else a.y < b.y

@[simp]
def le (a b : Point α) : Prop :=
  a = b ∨ a.lt b

instance : LT (Point α) := ⟨Point.lt⟩
instance : LE (Point α) := ⟨Point.le⟩

instance : Preorder (Point α) := by
  apply Preorder.mk
  · intro a
    simp [instLE]
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ h₁ h₂
    simp [instLE] at h₁ h₂ ⊢
    split_ifs at * <;> try simp_all
    · nm h₃ h₄
      subst h₃ h₄
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with rfl | h₂ <;> try simp_all
      right
      exact h₁.trans h₂
    · nm h₃ h₄ h₅
      subst h₃
      contrapose! h₂
      exact le_of_lt h₁
    · nm h₃ h₄ h₅
      exact h₁.trans h₂
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    simp [instLE, instLT]
    split_ifs <;> try simp_all
    · constructor
      · intro h
        simp [h]
        rw [lt_iff_le_and_ne] at h
        simp [h]
        exact h.2.symm
      · nm x; clear x
        rintro ⟨rfl | h₁, h₂, h₃⟩
        · simp at h₂
        · rw [lt_iff_le_and_ne]; tauto
    · nm h₁ h₂
      intro h₃
      exact le_of_lt h₃

instance : DecidableLT (Point α) := by
  intro a b
  simp [instLT]
  infer_instance

instance : DecidableLE (Point α) := by
  intro a b
  simp [instLE]
  infer_instance

@[simp] def compare (a b : Point α) :=
  if a = b then Ordering.eq
  else if a < b then Ordering.lt
  else Ordering.gt

instance : Ord (Point α) := ⟨Point.compare⟩

@[simp]
theorem mk_ord {x₁ y₁ x₂ y₂} :
Ord.compare (⟨x₁, y₁⟩ : Point α) ⟨x₂, y₂⟩ =
Point.compare ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
protected def min (a b : Point α) :=
  if a ≤ b then a else b

@[simp]
protected def max (a b : Point α) :=
  if a ≤ b then b else a

instance : Min (Point α) := ⟨Point.min⟩
instance : Max (Point α) := ⟨Point.max⟩

@[simp]
theorem mk_lt {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) < ⟨x₂, y₂⟩ ↔ Point.lt ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
theorem mk_le {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) ≤ ⟨x₂, y₂⟩ ↔ Point.le ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
theorem mk_min {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) ⊓ ⟨x₂, y₂⟩ = Point.min ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := rfl

@[simp]
theorem mk_max {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) ⊔ ⟨x₂, y₂⟩ = Point.max ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := rfl

instance : PartialOrder (Point α) := by
  constructor
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h₁ h₂
  simp at h₁ h₂ ⊢
  split_ifs at * <;> simp_all
  · rcases h₁ with rfl | h₁
    · rfl
    rcases h₂ with rfl | h₂
    · rfl
    contrapose! h₂; exact le_of_lt h₁
  · contrapose! h₂; exact le_of_lt h₁

instance : LinearOrder (Point α) := by
  constructor
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    simp
    split_ifs <;> simp_all
    nm x; clear x
    simp only [or_iff_not_imp_left]
    intro h₁ h₂
    simp at h₁
    rw [eq_comm] at h₁
    simp [h₂] at h₁
    contrapose! h₂
    apply le_antisymm h₁ h₂
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    simp
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    simp
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    simp
    change _ = ite _ _ _
    simp
    split_ifs <;> simp_all
  · infer_instance
  · infer_instance

def toProd (p : Point α) : α × α :=
  (p.1, p.2)

instance [Hashable α] : Hashable (Point α) :=
  ⟨λ p => hash p.toProd⟩

end LinearOrder

section Ring

def add [Add α] (a b : Point α) : Point α :=
  ⟨a.x + b.x, a.y + b.y⟩

instance [Add α] : Add (Point α) := ⟨add⟩

theorem add_def [Add α] {a b : Point α} : a + b = ⟨a.1 + b.1, a.2 + b.2⟩ := rfl

@[simp] theorem mk_add_mk [Add α] {x₁ y₁ x₂ y₂ : α} :
(⟨x₁, y₁⟩ : Point α) + ⟨x₂, y₂⟩ = ⟨x₁ + x₂, y₁ + y₂⟩ := rfl

def sub [Sub α] (a b : Point α) : Point α :=
  ⟨a.x - b.x, a.y - b.y⟩

instance [Sub α] : Sub (Point α) := ⟨sub⟩

theorem sub_def [Sub α] {a b : Point α} : a - b = ⟨a.1 - b.1, a.2 - b.2⟩ := rfl

@[simp] theorem mk_sub_mk [Sub α] {x₁ y₁ x₂ y₂ : α} :
(⟨x₁, y₁⟩ : Point α) - ⟨x₂, y₂⟩ = ⟨x₁ - x₂, y₁ - y₂⟩ := rfl

def mul [Mul α] (a b : Point α) : Point α :=
  ⟨a.x * b.x, a.y * b.y⟩

instance [Mul α] : Mul (Point α) := ⟨mul⟩

theorem mul_def [Mul α] {a b : Point α} : a * b = ⟨a.1 * b.1, a.2 * b.2⟩ := rfl

@[simp] theorem mk_mul_mk [Mul α] {x₁ y₁ x₂ y₂ : α} :
(⟨x₁, y₁⟩ : Point α) * ⟨x₂, y₂⟩ = ⟨x₁ * x₂, y₁ * y₂⟩ := rfl

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

end Point

abbrev PointN := Point ℕ
abbrev PointZ := Point ℤ

def PointN.dist (a b : PointN) : ℕ :=
  max |(a.x : ℤ) - b.x| |(a.y : ℤ) - b.y| |>.toNat

def PointZ.dist (a b : PointZ) : ℕ :=
  max |a.x - b.x| |a.y - b.y| |>.toNat

@[simp, symm]
theorem PointN.dist.comm {a b : PointN} : a.dist b = b.dist a := by
  simp [PointN.dist, abs_sub_comm]

@[simp, symm]
theorem PointZ.dist.comm {a b : PointZ} : a.dist b = b.dist a := by
  simp [PointZ.dist, abs_sub_comm]

@[simp]
theorem PointN.add_self_eq_zero_iff {a : PointN} : a + a = 0 ↔ a = 0 := by
  rcases a with ⟨x, y⟩; simp

@[simp]
theorem PointZ.add_self_eq_zero_iff {a : PointZ} : a + a = 0 ↔ a = 0 := by
  rcases a with ⟨x, y⟩; simp