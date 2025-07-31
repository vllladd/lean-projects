import AP.Util.Set
import AP.Util.Finset

theorem nonempty_equiv_comm {α β : Type*} :
Nonempty (α ≃ β) ↔ Nonempty (β ≃ α) := by
  apply Nonempty.congr <;> exact λ h => h.symm

@[simp]
theorem nonempty_equiv_refl {α : Type*} : Nonempty (α ≃ α) := ⟨by rfl⟩

theorem nonempty_equiv_set_empty_empty {α β : Type*} :
Nonempty ((∅ : Set α) ≃ (∅ : Set β)) := by
  refine' ⟨⟨_, _, _, _⟩⟩
  all_goals try rintro ⟨x, h⟩; simp at h

@[simp]
theorem nonempty_equiv_set_empty_iff {α β : Type*} {s : Set α} :
Nonempty (s ≃ (∅ : Set β)) ↔ s = ∅ := by
  constructor
  · rintro ⟨h⟩
    ext x
    simp
    intro hx
    exact (h.toFun ⟨_, hx⟩).2
  · rintro rfl
    exact nonempty_equiv_set_empty_empty

theorem nonempty_equiv_trans {α γ : Type*} (β : Type*)
(h₁ : Nonempty (α ≃ β)) (h₂ : Nonempty (β ≃ γ)) : Nonempty (α ≃ γ) := by
  rcases h₁ with ⟨a⟩
  rcases h₂ with ⟨b⟩
  exact ⟨a.trans b⟩

theorem nonempty_equiv_set_univ_self {α : Type*} :
Nonempty (α ≃ (Set.univ : Set α)) := by
  simp [←Cardinal.eq]

theorem nonempty_equiv_set_univ_self' {α : Type*} :
Nonempty ((Set.univ : Set α) ≃ α) := by
  simp [←Cardinal.eq]

theorem nonempty_equiv_set_univ_set_univ_iff.{u} {α β : Type u} :
Nonempty ((Set.univ : Set α) ≃ (Set.univ : Set β)) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

@[simp]
theorem nonempty_equiv_set_univ_iff.{u} {α β : Type u} :
Nonempty (α ≃ (Set.univ : Set β)) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

@[simp]
theorem nonempty_equiv_set_univ_iff'.{u} {α β : Type u} :
Nonempty ((Set.univ : Set α) ≃ β) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

theorem Cardinal.mk_eq_of_fintype_card {α : Type*} [h : Fintype α] {n}
(h₁ : Fintype.card α = n) : Cardinal.mk α = n := by
  rw [mk_fintype, h₁]

@[simp]
theorem Cardinal.mk_subtype_const_true {α : Type*} :
Cardinal.mk {_x : α // True} = Cardinal.mk α := by
  rw [Cardinal.eq]
  use λ ⟨x, _⟩ => x
  use λ x => ⟨x, trivial⟩
  all_goals intro x; simp

@[simp]
theorem Cardinal.mk_eq_mk_of_finite.{u} {α β : Type u}
[ha : Fintype α] [hb : Fintype β] :
Cardinal.mk α = Cardinal.mk β ↔ Fintype.card α = Fintype.card β := by
  rw [Cardinal.eq, Fintype.card_eq]

@[simp]
theorem nonempty_equiv_subtype_const_true_iff.{u} {α β : Type u} :
Nonempty (α ≃ {_x : β // True}) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

theorem Finset.mkRaw_card_eq_set_card_range {α β : Type*}
[ha : Fintype α] {f : α → β} :
(mkRaw f).card = (Set.range f).ncard := by
  classical
  simp [Finset.card_eq_cardinal_mk_to_nat]
  have h₁ : Cardinal.mk {x // ∃ a, f a = x} = Cardinal.mk (Set.range f) :=
    by
      rw [Cardinal.eq]
      exact nonempty_equiv_refl
  rw [h₁]
  clear h₁
  unfold Set.ncard
  apply congrArg Cardinal.toNat
  simp

@[simp]
theorem Fintype.card_set_eq_ncard {α : Type*}
{s : Set α} [hs : Fintype s] : Fintype.card s = s.ncard := by
  unfold Fintype.card
  rw [Finset.card_eq_cardinal_mk_to_nat]
  apply congrArg Cardinal.toNat
  simp

theorem Finset.card_eq_card_iff_equiv.{u} {α β : Type u}
{sa : Finset α} {sb : Finset β} : sa.card = sb.card ↔ Nonempty (sa ≃ sb) := by
  simp [←Cardinal.eq]

theorem Set.injOn_of_card_image_eq' {α : Type*} {s : Set α} {f : α → α}
(h₁ : s.Finite) (h₂ : Cardinal.mk (f '' s) = Cardinal.mk s) : s.InjOn f := by
  classical
  have h₃ := Set.Finite.image f h₁
  replace h₁ := h₁.toFintype
  replace h₃ := h₃.toFintype
  simp at h₂
  rename' s => s'
  generalize hs : s'.toFinset = s
  replace hs := congrArg (·.toSet) hs
  simp at hs
  subst hs
  clear h₁ h₃
  simp at h₂
  rw [Finset.image_toSet_eq, Finset.ncard_toSet, Finset.card_image_iff] at h₂
  exact h₂

theorem Set.card_image_eq_iff_injOn' {α : Type*} {s : Set α} {f : α → α}
(h₁ : s.Finite) : Cardinal.mk (f '' s) = Cardinal.mk s ↔ s.InjOn f := by
  classical
  use injOn_of_card_image_eq' h₁
  intro h
  rw [Cardinal.eq]
  constructor
  symm
  apply Equiv.ofBijective # λ ⟨x, hx⟩ => ⟨f x, by simp; use x⟩
  simp
  constructor
  · simpa [Function.Injective]
  · simp [Function.Surjective]

theorem Set.ncard_eq_ncard_iff_nonempty_equiv.{u} {α β : Type u}
{sa : Set α} {sb : Set β} (ha : sa.Finite) (hb : sb.Finite) :
sa.ncard = sb.ncard ↔ Nonempty (sa ≃ sb) := by
  classical
  rw [←Cardinal.eq]
  replace ha := ha.toFintype
  replace hb := hb.toFintype
  simp

theorem Set.ncard_image_eq_iff_injOn' {α : Type*} {s : Set α} {f : α → α}
(h₁ : s.Finite) : (f '' s).ncard = s.ncard ↔ s.InjOn f := by
  rw [ncard_eq_ncard_iff_nonempty_equiv (Set.Finite.image f h₁) h₁]
  rw [←Cardinal.eq]
  exact card_image_eq_iff_injOn' h₁

theorem nonempty_equiv_iff_bijective {α β : Type*} :
Nonempty (α ≃ β) ↔ ∃ (f : α → β), f.Bijective := by
  use λ ⟨e⟩ => ⟨_, e.bijective⟩
  use λ ⟨f, hf⟩ => ⟨Equiv.ofBijective f hf⟩

theorem Set.ncard_eq_ncard_iff_bijective.{u} {α β : Type u}
{sa : Set α} {sb : Set β} (ha : sa.Finite) (hb : sb.Finite) :
sa.ncard = sb.ncard ↔ ∃ (f : sa → sb), f.Bijective := by
  rw [ncard_eq_ncard_iff_nonempty_equiv ha hb]
  exact nonempty_equiv_iff_bijective

theorem Set.range_eq_image {α β : Type*} {f : α → β} :
Set.range f = f '' Set.univ := by simp

theorem Fintype.card_eq_finset_card {α : Type*} [ha : Fintype α] :
Fintype.card α = (Finset.univ : Finset α).card := by simp

theorem Set.univ_eq_finset_univ_of_fintype {α : Type*} [ha : Fintype α] :
(Set.univ : Set α) = Finset.univ.toSet := by simp

theorem Fintype.card_range_eq_iff_injective {α β : Type*}
[ha : Fintype α] {f : α → β} :
Fintype.card (Set.range f) = Fintype.card α ↔ f.Injective := by
  classical
  refine' ⟨_, λ h => Set.card_range_of_injective h⟩
  intro h
  simp at h
  rw [Set.range_eq_image, Fintype.card_eq_finset_card,
    Set.univ_eq_finset_univ_of_fintype, Finset.image_toSet_eq,
    Finset.ncard_toSet] at h
  rw [Finset.card_image_iff] at h
  simp at h
  exact h

theorem Fintype.card_eq_set_ncard {α : Type*} [ha : Fintype α] :
Fintype.card α = (Set.univ : Set α).ncard := by
  rw [Set.ncard_eq_toFinset_card]; simp

theorem Set.finite_of_finite_and_bijective {α β : Type*}
{sa : Set α} {sb : Set β}
(h₁ : sa.Finite) (h₂ : ∃ (f : sa → sb), f.Bijective) : sb.Finite := by
  rw [←nonempty_equiv_iff_bijective] at h₂
  obtain ⟨e⟩ := h₂
  replace h₁ := h₁.toFintype
  suffices h₃ : Fintype sb from Set.toFinite sb
  exact Fintype.ofEquiv _ e

theorem exi_bijective_symm {α β : Type*}
(h : ∃ (f : α → β), f.Bijective) : ∃ (f : β → α), f.Bijective := by
  obtain ⟨f, hf⟩ := h
  rw [Function.bijective_iff_has_inverse] at hf
  obtain ⟨g, h₁, h₂⟩ := hf
  use g
  exact Equiv.bijective ⟨g, f, h₂, h₁⟩

theorem exi_bijective_comm {α β : Type*} :
(∃ (f : α → β), f.Bijective) ↔ ∃ (f : β → α), f.Bijective := by
  constructor <;> exact exi_bijective_symm

theorem Set.finite_of_finite_and_bijective' {α β : Type*}
{sa : Set α} {sb : Set β}
(h₁ : sa.Finite) (h₂ : ∃ (f : sb → sa), f.Bijective) : sb.Finite := by
  rw [exi_bijective_comm] at h₂
  exact finite_of_finite_and_bijective h₁ h₂

theorem Set.ncard_image_eq_iff_injOn {α β : Type*} {s : Set α} {f : α → β}
(h₁ : s.Finite) : (f '' s).ncard = s.ncard ↔ s.InjOn f := ncard_image_iff h₁

theorem Set.range_sum_inl_card_eq {α β : Type*} [ha : Fintype α] :
(Set.range # @Sum.inl α β).ncard = Fintype.card α := by
  rw [Fintype.card_eq_set_ncard, Set.range_eq_image]
  rw [Set.ncard_image_eq_iff_injOn Set.finite_univ]
  apply Set.injOn_of_injective Sum.inl_injective

theorem Set.range_sum_inr_card_eq {α β : Type*} [hb : Fintype β] :
(Set.range # @Sum.inr α β).ncard = Fintype.card β := by
  rw [Fintype.card_eq_set_ncard, Set.range_eq_image]
  rw [Set.ncard_image_eq_iff_injOn Set.finite_univ]
  apply Set.injOn_of_injective Sum.inr_injective

theorem Set.nonempty_range_equiv_self_iff_injective.{u} {α β : Type u}
[ha : Fintype α] {f : α → β} : Nonempty (Set.range f ≃ α) ↔ f.Injective := by
  rw [←Fintype.card_range_eq_iff_injective, ←Cardinal.eq]; simp

@[simp]
theorem Finset.mkRaw_card_eq_fintype_card_iff_injective.{u} {α β : Type u}
[ha : Fintype α] {f : α → β} :
(mkRaw f).card = Fintype.card α ↔ f.Injective := by
  classical
  by_cases h₁ : IsEmpty α
  · simp [Finset.eq_empty_iff_forall_notMem]
    exact Function.injective_of_subsingleton f
  simp at h₁
  change _ = Finset.univ.card ↔ _
  rw [←Fintype.card_range_eq_iff_injective]
  rw [Finset.card_eq_card_iff_equiv, ←Cardinal.eq]
  simp [Set.range]
  simp only [←Finset.card_univ]
  simp only [Finset.card_eq_cardinal_mk_to_nat]
  simp
  constructor <;> intro h
  · simp [h]
  rwa [Cardinal.toNat_eq_iff] at h
  simp

@[simp]
theorem Finset.card_le_fintype_card {α : Type*} [ha : Fintype α] {s : Finset α} :
s.card ≤ Fintype.card α := Finset.card_le_univ s

theorem inf_type : Infinite Type := by
  rw [Cardinal.infinite_iff]
  suffices h : Cardinal.aleph0 ≤ Cardinal.lift.{1, 1} (Cardinal.mk Type)
    by
      simp at h
      exact h
  rw [Cardinal.aleph0, Cardinal.lift_mk_le]
  refine' ⟨⟨Fin, _⟩⟩
  intro x y h
  replace h := congrArg Cardinal.mk h
  simp at h
  exact h

instance : Infinite Type := inf_type

theorem Cardinal.mk_lt_fn_prop {α : Type*} :
Cardinal.mk α < Cardinal.mk (α → Prop) := by
  simp [Cardinal.mk_pi]; apply Cardinal.cantor

section card_type

universe u v w q

theorem nonempty_equiv_of_embed {α : Type u} {β : Type v}
(h₁ : Nonempty (α ↪ β)) (h₂ : Nonempty (β ↪ α)) : Nonempty (α ≃ β) := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  rw [nonempty_equiv_iff_bijective]
  exact Function.Embedding.schroeder_bernstein hf hg

theorem nonempty_embed_trans {α : Type u} {β : Type v} {γ : Type w}
(h₁ : Nonempty (α ↪ β)) (h₂ : Nonempty (β ↪ γ)) : Nonempty (α ↪ γ) := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨_, Function.Injective.comp hg hf⟩

theorem nonempty_embed_iff_lift_left {α : Type v} {β : Type w} :
Nonempty (α ↪ β) ↔ Nonempty (ULift.{u} α ↪ β) := by
  constructor <;> rintro ⟨f, hf⟩
  all_goals
    refine' ⟨λ x => _, _⟩
    first | exact f x.down | exact f (.up x)
    intro x y h
    simp at h
    specialize hf h
    simp at hf
    exact hf

theorem nonempty_embed_iff_lift_right {α : Type v} {β : Type w} :
Nonempty (α ↪ β) ↔ Nonempty (α ↪ ULift.{u} β) := by
  constructor <;> rintro ⟨f, hf⟩
  all_goals
    refine' ⟨λ x => _, _⟩
    first | exact .up (f x) | exact (f x).down
    intro x y h
    simp at h
    specialize hf h
    exact hf

theorem isEmpty_embed_iff_lift_left {α : Type v} {β : Type w} :
IsEmpty (α ↪ β) ↔ IsEmpty (ULift.{u} α ↪ β) := by
  rw [←not_iff_not]; simp; exact nonempty_embed_iff_lift_left

theorem isEmpty_embed_iff_lift_right {α : Type v} {β : Type w} :
IsEmpty (α ↪ β) ↔ IsEmpty (α ↪ ULift.{u} β) := by
  rw [←not_iff_not]; simp; exact nonempty_embed_iff_lift_right

theorem nonempty_embed_iff_lift {α : Type w} {β : Type q} :
Nonempty (α ↪ β) ↔ Nonempty (ULift.{u} α ↪ ULift.{v} β) := by
  constructor <;> rintro ⟨f, hf⟩
  all_goals
    refine' ⟨λ y => _, _⟩
    first | exact .up (f y.down) | exact (f (.up y)).down
    intro x y h
    simp at h
    specialize hf h
    simp at hf
    exact hf

theorem isEmpty_embed_iff_lift {α : Type w} {β : Type q} :
IsEmpty (α ↪ β) ↔ IsEmpty (ULift.{u} α ↪ ULift.{v} β) := by
  rw [←not_iff_not]
  simp
  exact nonempty_embed_iff_lift

theorem nonempty_embed_of_empty_embed_rev {α : Type u} {β : Type v}
(h : IsEmpty (β ↪ α)) : Nonempty (α ↪ β) := by
  rw [isEmpty_embed_iff_lift.{u, v}] at h
  rw [nonempty_embed_iff_lift.{v, u}]
  rw [←Cardinal.le_def]
  contrapose! h
  simp
  rw [←Cardinal.le_def]
  exact le_of_lt h

theorem isEmpty_embed_of_isEmpty_of_nonempty {α : Type u} {β : Type v} {γ : Type w}
(h₁ : IsEmpty (β ↪ α)) (h₂ : Nonempty (β ↪ γ)) : IsEmpty (γ ↪ α) := by
  contrapose h₁
  simp at h₁ ⊢
  exact nonempty_embed_trans h₂ h₁

@[simp]
theorem isEmpty_set_embed {α : Type u} : IsEmpty (Set α ↪ α) := by
  by_contra h
  simp at h
  rw [←Cardinal.le_def] at h
  simp at h
  contrapose! h
  apply Cardinal.cantor

theorem nonempty_embed_type {α : Type u} : Nonempty (α ↪ Type u) := by
  use λ x => (embeddingToCardinal.1 x).out
  intro x y h
  simp at h
  exact embeddingToCardinal.2 h

theorem isEmpty_type_embed {α : Type u} : IsEmpty (Type u ↪ α) := by
  apply isEmpty_embed_of_isEmpty_of_nonempty isEmpty_set_embed
  exact nonempty_embed_type

theorem cardinal_embed_type : Nonempty (Cardinal.{u} ↪ Type u) := by
  use Quotient.out
  intro x y h
  simp at h
  exact h

theorem cardinal_embed_ordinal : Nonempty (Cardinal.{u} ↪ Ordinal.{u}) := by
  use Cardinal.ord
  intro x y h
  simp at h
  exact h

theorem ifEmpty_embed_trans {α : Type u} {β : Type v} {γ : Type w}
(h₁ : IsEmpty (α ↪ β)) (h₂ : IsEmpty (β ↪ γ)) : IsEmpty (α ↪ γ) := by
  apply isEmpty_embed_of_isEmpty_of_nonempty h₂
  exact nonempty_embed_of_empty_embed_rev h₁

@[simp]
theorem nonempty_lift_embed_iff {α : Type v} {β : Type w} :
Nonempty (ULift.{u} α ↪ β) ↔ Nonempty (α ↪ β) :=
  nonempty_embed_iff_lift_left.symm

@[simp]
theorem nonempty_embed_lift_iff {α : Type v} {β : Type w} :
Nonempty (α ↪ ULift.{u} β) ↔ Nonempty (α ↪ β) :=
  nonempty_embed_iff_lift_right.symm

@[simp]
theorem isEmpty_lift_embed_iff {α : Type v} {β : Type w} :
IsEmpty (ULift.{u} α ↪ β) ↔ IsEmpty (α ↪ β) :=
  isEmpty_embed_iff_lift_left.symm

@[simp]
theorem isEmpty_embed_lift_iff {α : Type v} {β : Type w} :
IsEmpty (α ↪ ULift.{u} β) ↔ IsEmpty (α ↪ β) :=
  isEmpty_embed_iff_lift_right.symm

theorem nonempty_embed_type_max {α : Type v} :
Nonempty (α ↪ Type (max v u)) := by
  rw [nonempty_embed_iff_lift_left.{max u v}]
  exact nonempty_embed_type

theorem isEmpty_type_max_embed {α : Type v} :
IsEmpty (Type (max v u) ↪ α) := by
  apply isEmpty_embed_of_isEmpty_of_nonempty isEmpty_set_embed
  exact nonempty_embed_type_max.{max u v}

@[simp]
theorem type_embed_type_succ : Nonempty (Type u ↪ Type (u + 1)) :=
  nonempty_embed_type_max.{u + 1}

@[simp]
theorem not_type_succ_embed_type : IsEmpty (Type (u + 1) ↪ Type u) :=
  isEmpty_type_max_embed.{u + 1}

end card_type

theorem Finset.card_fin_eq_of {n m : ℕ} {s : Finset (Fin n)} {t : Finset (Fin m)}
(hs : ∀ {i h}, ⟨i, h⟩ ∈ s → ∃ h, ⟨i, h⟩ ∈ t)
(ht : ∀ {i h}, ⟨i, h⟩ ∈ t → ∃ h, ⟨i, h⟩ ∈ s) :
s.card = t.card := by
  rw [card_eq_card_iff_equiv]
  rw [nonempty_equiv_iff_bijective]
  refine' ⟨_, _⟩
  · rintro ⟨⟨i, h₁⟩, h₂⟩
    refine' ⟨⟨i, _⟩, _⟩ <;> obtain ⟨h₃, h₄⟩ := hs h₂ <;> assumption
  constructor
  · rintro ⟨⟨i, h₁⟩, h₂⟩ ⟨⟨j, h₃⟩, h₄⟩; simp
  rintro ⟨⟨i, h₁⟩, h₂⟩
  simp
  obtain ⟨h₃, h₄⟩ := ht h₂
  refine' ⟨_, h₄, rfl⟩

@[simp]
theorem Equiv.bijective_toFun {α β : Type*} (e : α ≃ β) : e.toFun.Bijective := by
  rw [Function.bijective_iff_has_inverse]
  exact ⟨e.invFun, e.left_inv, e.right_inv⟩

@[simp]
theorem Equiv.bijective_invFun {α β : Type*} (e : α ≃ β) : e.invFun.Bijective := by
  rw [Function.bijective_iff_has_inverse]
  exact ⟨e.toFun, e.right_inv, e.left_inv⟩