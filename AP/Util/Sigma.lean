import AP.Util.Logic

namespace Sigma

@[simp]
theorem fst_comp_mk_eq_id {α : Type*} {β : α → Type*} {f : (i : α) → β i} :
((λ (x : Σ i, β i) => x.fst) ∘ (λ i => ⟨i, f i⟩)) = (λ i => i) := by
  ext x; simp

@[simp]
def toProd {α β : Type*} (x : Σ (_ : α), β) : α × β :=
  ⟨x.1, x.2⟩

@[simp]
theorem prod_to_sigma_comp_sigma_to_prod {α β : Type*} :
@Sigma.toProd α β ∘ Prod.toSigma = id := by
  ext:1; simp

@[simp]
theorem sigma_to_prod_comp_prod_to_sigma {α β : Type*} :
@Prod.toSigma α β ∘ Sigma.toProd = id := by
  ext:1; simp

theorem toProd_inj {α β : Type*} {x y : Σ (_ : α), β}
(h : x.toProd = y.toProd) : x = y := by
  replace h := congrArg Prod.toSigma h; simp at h; exact h

@[simp]
theorem toProd_eq_toProd {α β : Type*} {x y : Σ (_ : α), β} :
x.toProd = y.toProd ↔ x = y :=
  ⟨toProd_inj, by rintro rfl; rfl⟩

@[simp]
theorem injective_toProd {α β : Type*} : Function.Injective # @Sigma.toProd α β := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h; simp at h; simp [h]

end Sigma namespace Option

@[simp]
theorem map_sigma_toProd_eq_iff {α β : Type*} {ma mb : Option (Σ (_ : α), β)} :
ma.map Sigma.toProd = mb.map Sigma.toProd ↔ ma = mb := by
  refine' ⟨λ h => _, by rintro rfl; rfl⟩
  cases ma <;> cases mb <;> simp at h; rfl
  nm a b
  simp
  ext <;> simp [h]

end Option namespace List

@[simp]
theorem map_sigma_toProd_eq_iff {α β : Type*} {xs ys : List (Σ (_ : α), β)} :
xs.map Sigma.toProd = ys.map Sigma.toProd ↔ xs = ys := by
  refine' ⟨λ h => _, by rintro rfl; rfl⟩
  rw [map_eq_iff] at h
  ext
  nm i x
  rcases x with ⟨a, b⟩
  specialize h i
  simp at h
  rw [h]

theorem ind_pair_sigma {α β : Type*} {P : List (α × β) → Prop}
(h : ∀ (xs : List # Σ (_ : α), β), P # xs.map Sigma.toProd)
(xs : List # α × β) : P xs := by
  obtain ⟨xs, rfl⟩ : ∃ (ys : List _), ys.map Sigma.toProd = xs :=
    ⟨xs.map Prod.toSigma, by simp⟩
  apply h

end List namespace Sigma

@[simp]
theorem fst_eq_fst_and_eq_iff {α : Type*} {β : α → Type*} {x y : Σ (i : α), β i} :
x.fst = y.fst ∧ x = y ↔ x = y := by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩; simp