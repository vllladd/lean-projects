import AP.Util.Main

variable {α : Type*} [ha : LinearOrder α]

@[ext]
structure Point (α : Type*) where
  x : α
  y : α

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
def Point.lt (a b : Point α) : Prop :=
  if a.y = b.y then a.x < b.x else a.y < b.y

@[simp]
def Point.le (a b : Point α) : Prop :=
  a = b ∨ a.lt b

instance : LT (Point α) := ⟨Point.lt⟩
instance : LE (Point α) := ⟨Point.le⟩

instance : Preorder (Point α) := by
  apply Preorder.mk
  · intro a
    simp [instLEPoint]
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ h₁ h₂
    simp [instLEPoint] at h₁ h₂ ⊢
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
    simp [instLEPoint, instLTPoint]
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
  simp [instLTPoint]
  infer_instance

instance : DecidableLE (Point α) := by
  intro a b
  simp [instLEPoint]
  infer_instance

@[simp] def Point.compare (a b : Point α) :=
  if a = b then Ordering.eq
  else if a < b then Ordering.lt
  else Ordering.gt

instance : Ord (Point α) := ⟨Point.compare⟩

@[simp]
theorem point_mk_ord {x₁ y₁ x₂ y₂} :
compare (⟨x₁, y₁⟩ : Point α) ⟨x₂, y₂⟩ =
Point.compare ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
protected def Point.min (a b : Point α) :=
  if a ≤ b then a else b

@[simp]
protected def Point.max (a b : Point α) :=
  if a ≤ b then b else a

instance : Min (Point α) := ⟨Point.min⟩
instance : Max (Point α) := ⟨Point.max⟩

@[simp]
theorem point_mk_lt {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) < ⟨x₂, y₂⟩ ↔ Point.lt ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
theorem point_mk_le {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) ≤ ⟨x₂, y₂⟩ ↔ Point.le ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by rfl

@[simp]
theorem point_mk_min {x₁ y₁ x₂ y₂} :
(⟨x₁, y₁⟩ : Point α) ⊓ ⟨x₂, y₂⟩ = Point.min ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := rfl

@[simp]
theorem point_mk_max {x₁ y₁ x₂ y₂} :
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

def Point.toProd (p : Point α) : α × α :=
  (p.1, p.2)

instance [Hashable α] : Hashable (Point α) :=
  ⟨λ p => hash p.toProd⟩

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