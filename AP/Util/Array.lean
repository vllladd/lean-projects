import AP.Util.List

namespace Array

variable {α : Type*} {β : Type*} {xs ys : Array α}

def foldlWith' (xs : Array α)
(f : β → (x : α) → x ∈ xs → β) (z : β) (i : ℕ) : β :=
  if h : i < xs.size then xs.foldlWith' f (f z (xs[i]) (by simp)) (i + 1) else z

def foldlWith (xs : Array α) (f : β → (x : α) → x ∈ xs → β) (z : β) : β :=
  xs.foldlWith' f z 0

theorem foldlWith'_cons' {xs : List α} {x : α}
{f : β → (y : α) → y ∈ (⟨x :: xs⟩ : Array α) → β} {z : β} {i} (h : i ≠ 0) :
(⟨x :: xs⟩ : Array α).foldlWith' f z i = (⟨xs⟩ : Array α).foldlWith'
(λ acc x h₁ => f acc x # by simp at h₁; simp [h₁]) z (i - 1) := by
  fun_induction foldlWith'
  · nm r i h₁ ih
    simp at ih ⊢
    rw [ih]
    clear ih
    cases i; simp at h; nm i; clear h
    nth_rw 2 [foldlWith']
    split_ifs with h₂; simp
    simp at h₁ h₂
    linarith
  · nm r i h₁
    cases i; simp at h; nm i; clear h
    simp at h₁ ⊢
    unfold foldlWith'
    simp
    intro h₂
    linarith

@[simp]
theorem foldlWith'_cons {xs : List α} {x : α}
{f : β → (y : α) → y ∈ (⟨x :: xs⟩ : Array α) → β} {z : β} {i} :
(⟨x :: xs⟩ : Array α).foldlWith' f z (i + 1) = (⟨xs⟩ : Array α).foldlWith'
(λ acc x h₁ => f acc x # by simp at h₁; simp [h₁]) z i :=
  foldlWith'_cons' # by simp

theorem foldlWith_eq_foldlWith_toList {f : β → (x : α) → x ∈ xs → β} {z : β} :
xs.foldlWith f z = xs.toList.foldlWith (λ acc x h => f acc x # by simp at h; exact h) z := by
  classical
  unfold foldlWith
  rcases xs with ⟨xs⟩; dsimp
  induction xs generalizing z
  · unfold foldlWith'; simp
  nm x xs ih
  nth_rw 1 [foldlWith']
  simp [ih]

@[simp]
theorem foldlWith_snoc {x : α} {f : β → (y : α) → y ∈ xs ++ [x] → β} {z : β} :
(xs ++ [x]).foldlWith f z = f (xs.foldlWith (λ acc y h => f acc y (by simp [h])) z)
x (by simp) := by
  classical
  rcases xs with ⟨xs⟩
  simp [foldlWith_eq_foldlWith_toList, List.foldlWith_eq_foldl]
  congr 1
  apply List.foldl_eq_foldl_of_fn_congr
  intro acc y hy
  simp [hy]

theorem foldlWith_eq_foldl [ha : DecidableEq α] {f : β → (x : α) → x ∈ xs → β} {z : β} :
xs.foldlWith f z = xs.foldl (λ acc x => if h : x ∈ xs then f acc x h else z) z := by
  rcases xs with ⟨xs⟩
  rw [foldlWith_eq_foldlWith_toList, ←foldl_toList, List.foldlWith_eq_foldl]
  apply List.foldl_eq_foldl_of_fn_congr
  intro acc x hx; simp [hx]

theorem foldlWith_eq_foldl_toList [ha : DecidableEq α] {f : β → (x : α) → x ∈ xs → β} {z : β} :
xs.foldlWith f z = xs.toList.foldl (λ acc x => if h : x ∈ xs then f acc x h else z) z := by
  simp; exact foldlWith_eq_foldl

def mapWith (xs : Array α) (f : (x : α) → x ∈ xs → β) : Array β :=
  ⟨xs.toList.mapWith # λ x h => f x # by simp at h; exact h⟩

open Classical in noncomputable
def dfltMapWith (f : (x : α) → x ∈ xs → β) (h : xs ≠ #[]) : β :=
  match h₁ : xs with
  | ⟨[]⟩ => by simp at h
  | ⟨x :: _⟩ => Nonempty.some ⟨f x # by simp⟩

theorem dfltMapWith_eq_dfltMapWith {f₁ f₂ : (x : α) → x ∈ xs → β}
{h : xs ≠ #[]} : dfltMapWith f₁ h = dfltMapWith f₂ h := by
  rcases xs with ⟨⟨⟩ | ⟨x, xs⟩⟩; simp at h; simp [dfltMapWith]

@[simp]
theorem dfltMapWith_eq_some_of_nonempty [hb : Nonempty β] {f : (x : α) → x ∈ xs → β}
{h : xs ≠ #[]} : dfltMapWith f h = hb.some := by
  rcases xs with ⟨⟨⟩ | ⟨x, xs⟩⟩; simp at h; simp [dfltMapWith]

theorem mapWith_eq_mapWith_toList {f : (x : α) → x ∈ xs → β} :
xs.mapWith f = ⟨xs.toList.mapWith # λ x h => f x # by simp at h; exact h⟩ := rfl

@[simp]
theorem mapWith_mk {xs : List α} {f : (x : α) → x ∈ Array.mk xs → β} :
(Array.mk xs).mapWith f = ⟨xs.mapWith (λ x h => f x # by simpa)⟩ := rfl

theorem ext_iff' : xs = ys ↔ xs.toList = ys.toList :=
  toList_inj.symm

theorem mapWith_eq_map [ha : DecidableEq α] {f : (x : α) → x ∈ xs → β} :
xs.mapWith f = if h : xs = #[] then #[] else
xs.map (λ x => if h₁ : x ∈ xs then f x h₁ else
dfltMapWith f h) := by
  rcases xs with xs
  rw [ext_iff']
  rw [mapWith_eq_mapWith_toList]
  dsimp
  rw [List.mapWith_eq_map]
  simp
  split_ifs with h₁; rfl
  simp
  intro x hx
  split_ifs
  rfl
  