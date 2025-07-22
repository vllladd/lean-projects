import AP.Util.Main

namespace AP

@[ext]
structure Point where
  x : ℤ
  y : ℤ

instance : DecidableEq Point := λ a b =>
match h : decide # a.x = b.x ∧ a.y = b.y with
| true => isTrue # by ext <;> simp_all
| false => isFalse # by rintro rfl; simp at h

instance : Inhabited Point := ⟨0, 0⟩

instance : Repr Point := by
  constructor
  rintro ⟨x, y⟩ prec
  exact (x, y).repr prec

@[simp]
def Point.lt (a b : Point) : Prop :=
  if a.y = b.y then a.x < b.x else a.y < b.y

@[simp]
def Point.le (a b : Point) : Prop :=
  a = b ∨ a.lt b

instance : LT Point := ⟨Point.lt⟩
instance : LE Point := ⟨Point.le⟩

instance : Preorder Point := by
  apply Preorder.mk
  · intro a
    simp [instLEPoint]
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ h₁ h₂
    simp [instLEPoint, instLTPoint] at h₁ h₂ ⊢
    split_ifs at * <;> try simp_all
    · nm h₃ h₄
      subst h₃ h₄
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with rfl | h₂ <;> try simp_all
      right
      linarith
    · nm h₃ h₄ h₅
      subst h₃
      rw [←Int.le_iff_eq_or_lt]
      linarith
    · nm h₃ h₄ h₅
      linarith
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    simp [instLEPoint, instLTPoint]
    split_ifs <;> try simp_all
    · constructor
      · intro h
        simp [h]
        rw [Int.lt_iff_le_and_ne] at h
        simp [h]
        exact h.2.symm
      · nm x; clear x
        rintro ⟨rfl | h₁, h₂, h₃⟩
        · simp at h₂
        · linarith
    · nm h₁ h₂
      intro h₃
      linarith

instance : DecidableLT Point := by
  intro a b
  simp [instLTPoint]
  infer_instance

instance : DecidableLE Point := by
  intro a b
  simp [instLEPoint]
  infer_instance

@[simp] def Point.compare (a b : Point) :=
  if a = b then Ordering.eq
  else if a < b then Ordering.lt
  else Ordering.gt

instance : Ord Point := ⟨Point.compare⟩

@[simp]
theorem point_mk_ord {x₁ y₁ x₂ y₂} :
compare (⟨x₁, y₁⟩ : Point) ⟨x₂, y₂⟩ = Point.compare ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
protected def Point.min (a b : Point) :=
  if a ≤ b then a else b

@[simp]
protected def Point.max (a b : Point) :=
  if a ≤ b then b else a

instance : Min Point := ⟨Point.min⟩
instance : Max Point := ⟨Point.max⟩

@[simp]
theorem point_mk_lt {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point) < ⟨x₂, y₂⟩ ↔ Point.lt ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
theorem point_mk_le {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point) ≤ ⟨x₂, y₂⟩ ↔ Point.le ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
theorem point_mk_min {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point) ⊓ ⟨x₂, y₂⟩ = Point.min ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := rfl

@[simp]
theorem point_mk_max {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point) ⊔ ⟨x₂, y₂⟩ = Point.max ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := rfl

instance : PartialOrder Point := by
  constructor
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h₁ h₂
  simp at h₁ h₂ ⊢
  split_ifs at * <;> simp_all
  · rcases h₁ with rfl | h₁
    · rfl
    rcases h₂ with rfl | h₂
    · rfl
    linarith
  · linarith

instance : LinearOrder Point := by
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
    linarith
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

def Point.dist (a b : Point) : ℕ :=
  Int.toNat # max |a.x - b.x| |a.y - b.y|

@[simp, symm]
theorem Point.dist.comm {a b : Point} : a.dist b = b.dist a := by
  simp [Point.dist, abs_sub_comm]

def Point.toProd (p : Point) : ℤ × ℤ :=
  (p.1, p.2)

instance : Hashable Point :=
  ⟨λ p => hash p.toProd⟩