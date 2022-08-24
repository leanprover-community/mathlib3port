/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.Algebra.IndicatorFunction

/-!
# Type of functions with finite support

For any type `α` and any type `M` with zero, we define the type `finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `monoid_algebra R M` and `add_monoid_algebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `add_monoid_algebra`s, hence they use
  `finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `linear_independent`) is defined as a map
  `finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `multiset α ≃+ α →₀ ℕ`;
* `free_abelian_group α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `finsupp` elements, which is defined in
`algebra/big_operators/finsupp`.

Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `monoid_algebra`, `add_monoid_algebra`, and types based on these two have
non-pointwise multiplication.

## Main declarations

* `finsupp`: The type of finitely supported functions from `α` to `β`.
* `finsupp.single`: The `finsupp` which is nonzero in exactly one point.
* `finsupp.update`: Changes one value of a `finsupp`.
* `finsupp.erase`: Replaces one value of a `finsupp` by `0`.
* `finsupp.on_finset`: The restriction of a function to a `finset` as a `finsupp`.
* `finsupp.map_range`: Composition of a `zero_hom` with a `finsupp`.
* `finsupp.emb_domain`: Maps the domain of a `finsupp` by an embedding.
* `finsupp.zip_with`: Postcomposition of two `finsupp`s with a function `f` such that `f 0 0 = 0`.

## Notations

This file adds `α →₀ M` as a global notation for `finsupp α M`.

We also use the following convention for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `has_zero` or `(add_)(comm_)monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/


noncomputable section

open Finset Function

open Classical BigOperators

variable {α β γ ι M M' N P G H R S : Type _}

/-- `finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure Finsupp (α : Type _) (M : Type _) [Zero M] where
  Support : Finset α
  toFun : α → M
  mem_support_to_fun : ∀ a, a ∈ support ↔ to_fun a ≠ 0

-- mathport name: «expr →₀ »
infixr:25 " →₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `finsupp` -/


section Basic

variable [Zero M]

instance funLike : FunLike (α →₀ M) α fun _ => M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

/-- Helper instance for when there are too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →₀ M) fun _ => α → M :=
  FunLike.hasCoeToFun

@[ext]
theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h

/-- Deprecated. Use `fun_like.ext_iff` instead. -/
theorem ext_iff {f g : α →₀ M} : f = g ↔ ∀ a, f a = g a :=
  FunLike.ext_iff

/-- Deprecated. Use `fun_like.coe_fn_eq` instead. -/
theorem coe_fn_inj {f g : α →₀ M} : (f : α → M) = g ↔ f = g :=
  FunLike.coe_fn_eq

/-- Deprecated. Use `fun_like.coe_injective` instead. -/
theorem coe_fn_injective : @Function.Injective (α →₀ M) (α → M) coeFn :=
  FunLike.coe_injective

/-- Deprecated. Use `fun_like.congr_fun` instead. -/
theorem congr_fun {f g : α →₀ M} (h : f = g) (a : α) : f a = g a :=
  FunLike.congr_fun h _

@[simp]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) : ⇑(⟨s, f, h⟩ : α →₀ M) = f :=
  rfl

instance : Zero (α →₀ M) :=
  ⟨⟨∅, 0, fun _ => ⟨False.elim, fun H => H rfl⟩⟩⟩

@[simp]
theorem coe_zero : ⇑(0 : α →₀ M) = 0 :=
  rfl

theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
  rfl

@[simp]
theorem support_zero : (0 : α →₀ M).Support = ∅ :=
  rfl

instance : Inhabited (α →₀ M) :=
  ⟨0⟩

@[simp]
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.Support ↔ f a ≠ 0 :=
  f.mem_support_to_fun

@[simp, norm_cast]
theorem fun_support_eq (f : α →₀ M) : Function.Support f = f.Support :=
  Set.ext fun x => mem_support_iff.symm

theorem not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.Support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast]
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 := by
  rw [← coe_zero, coe_fn_inj]

theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.Support = g.Support ∧ ∀ x ∈ f.Support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a =>
      if h : a ∈ f.Support then h₂ a h
      else by
        have hf : f a = 0 := not_mem_support_iff.1 h
        have hg : g a = 0 := by
          rwa [h₁, not_mem_support_iff] at h
        rw [hf, hg]⟩

@[simp]
theorem support_eq_empty {f : α →₀ M} : f.Support = ∅ ↔ f = 0 := by
  exact_mod_cast @Function.support_eq_empty_iff _ _ _ f

theorem support_nonempty_iff {f : α →₀ M} : f.Support.Nonempty ↔ f ≠ 0 := by
  simp only [Finsupp.support_eq_empty, Finset.nonempty_iff_ne_empty, Ne.def]

theorem nonzero_iff_exists {f : α →₀ M} : f ≠ 0 ↔ ∃ a : α, f a ≠ 0 := by
  simp [← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_not_mem]

theorem card_support_eq_zero {f : α →₀ M} : card f.Support = 0 ↔ f = 0 := by
  simp

instance [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) := fun f g =>
  decidableOfIff (f.Support = g.Support ∧ ∀ a ∈ f.Support, f a = g a) ext_iff'.symm

theorem finite_support (f : α →₀ M) : Set.Finite (Function.Support f) :=
  f.fun_support_eq.symm ▸ f.Support.finite_to_set

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (a «expr ∉ » s)
theorem support_subset_iff {s : Set α} {f : α →₀ M} : ↑f.Support ⊆ s ↔ ∀ (a) (_ : a ∉ s), f a = 0 := by
  simp only [Set.subset_def, mem_coe, mem_support_iff] <;> exact forall_congrₓ fun a => not_imp_comm

/-- Given `fintype α`, `equiv_fun_on_fintype` is the `equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
def equivFunOnFintype [Fintype α] : (α →₀ M) ≃ (α → M) :=
  ⟨fun f a => f a, fun f =>
    mk (Finset.univ.filter fun a => f a ≠ 0) f
      (by
        simp only [true_andₓ, Finset.mem_univ, iff_selfₓ, Finset.mem_filter, Finset.filter_congr_decidable,
          forall_true_iff]),
    by
    intro f
    ext a
    rfl, by
    intro f
    ext a
    rfl⟩

@[simp]
theorem equiv_fun_on_fintype_symm_coe {α} [Fintype α] (f : α →₀ M) : equivFunOnFintype.symm f = f := by
  ext
  simp [equiv_fun_on_fintype]

/-- If `α` has a unique term, the type of finitely supported functions `α →₀ β` is equivalent to `β`.
-/
@[simps]
noncomputable def _root_.equiv.finsupp_unique {ι : Type _} [Unique ι] : (ι →₀ M) ≃ M :=
  Finsupp.equivFunOnFintype.trans (Equivₓ.funUnique ι M)

end Basic

/-! ### Declarations about `single` -/


section Single

variable [Zero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M :=
  ⟨if b = 0 then ∅ else {a}, fun a' => if a = a' then b else 0, fun a' => by
    by_cases' hb : b = 0 <;> by_cases' a = a' <;> simp only [hb, h, if_pos, if_false, mem_singleton]
    · exact ⟨False.elim, fun H => H rfl⟩
      
    · exact ⟨False.elim, fun H => H rfl⟩
      
    · exact ⟨fun _ => hb, fun _ => rfl⟩
      
    · exact ⟨fun H _ => h H.symm, fun H => (H rfl).elim⟩
      ⟩

theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 := by
  convert rfl

theorem single_eq_indicator : ⇑(single a b) = Set.indicatorₓ {a} fun _ => b := by
  ext
  simp [single_apply, Set.indicatorₓ, @eq_comm _ a]

@[simp]
theorem single_eq_same : (single a b : α →₀ M) a = b :=
  if_pos rfl

@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 :=
  if_neg h

theorem single_eq_update [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Function.update 0 a b := by
  rw [single_eq_indicator, ← Set.piecewise_eq_indicator, Set.piecewise_singleton]

theorem single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.single a b :=
  single_eq_update a b

@[simp]
theorem single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
  coe_fn_injective <| by
    simpa only [single_eq_update, coe_zero] using Function.update_eq_self a (0 : α → M)

theorem single_of_single_apply (a a' : α) (b : M) : single a ((single a' b) a) = single a' (single a' b) a := by
  rw [single_apply, single_apply]
  ext
  split_ifs
  · rw [h]
    
  · rw [zero_apply, single_apply, if_t_t]
    

theorem support_single_ne_zero (a : α) (hb : b ≠ 0) : (single a b).Support = {a} :=
  if_neg hb

theorem support_single_subset : (single a b).Support ⊆ {a} :=
  show ite _ _ _ ⊆ _ by
    split_ifs <;> [exact empty_subset _, exact subset.refl _]

theorem single_apply_mem (x) : single a b x ∈ ({0, b} : Set M) := by
  rcases em (a = x) with (rfl | hx) <;> [simp , simp [single_eq_of_ne hx]]

theorem range_single_subset : Set.Range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem

/-- `finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`finsupp.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a := by
    rw [Eq]
  rwa [single_eq_same, single_eq_same] at this

theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 := by
  simp [single_eq_indicator]

theorem single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ x = a ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]

theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).Support ↔ a = a' ∧ b ≠ 0 := by
  simp [single_apply_eq_zero, not_or_distrib]

theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.Support ⊆ {a} ∧ f a = b := by
  refine' ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases' hx : a = x <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne.def, not_false_iff]
  exact not_mem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)

theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := by
  constructor
  · intro eq
    by_cases' a₁ = a₂
    · refine' Or.inl ⟨h, _⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
      
    · rw [ext_iff] at eq
      have h₁ := Eq a₁
      have h₂ := Eq a₂
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (Ne.symm h)] at h₁ h₂
      exact Or.inr ⟨h₁, h₂.symm⟩
      
    
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
      
    · rw [single_zero, single_zero]
      
    

/-- `finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b := fun a a' H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff

theorem support_single_ne_bot (i : α) (h : b ≠ 0) : (single i b).Support ≠ ⊥ := by
  simpa only [support_single_ne_zero _ h] using singleton_ne_empty _

theorem support_single_disjoint [DecidableEq α] {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
    Disjoint (single i b).Support (single j b').Support ↔ i ≠ j := by
  rw [support_single_ne_zero _ hb, support_single_ne_zero _ hb', disjoint_singleton]

@[simp]
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by
  simp [ext_iff, single_eq_indicator]

theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  simp only [single_apply] <;> ac_rfl

instance [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) := by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)

theorem unique_single [Unique α] (x : α →₀ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm

@[ext]
theorem unique_ext [Unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
  ext fun a => by
    rwa [Unique.eq_default a]

theorem unique_ext_iff [Unique α] {f g : α →₀ M} : f = g ↔ f default = g default :=
  ⟨fun h => h ▸ rfl, unique_ext⟩

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same, single_eq_same]

theorem support_eq_singleton {f : α →₀ M} {a : α} : f.Support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h => ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a, eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩, fun h =>
    h.2.symm ▸ support_single_ne_zero _ h.1⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (b «expr ≠ » 0)
theorem support_eq_singleton' {f : α →₀ M} {a : α} : f.Support = {a} ↔ ∃ (b : _)(_ : b ≠ 0), f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨b, hb, hf⟩ => hf.symm ▸ support_single_ne_zero _ hb⟩

theorem card_support_eq_one {f : α →₀ M} : card f.Support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) := by
  simp only [card_eq_one, support_eq_singleton]

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (b «expr ≠ » 0)
theorem card_support_eq_one' {f : α →₀ M} : card f.Support = 1 ↔ ∃ (a : _)(b : _)(_ : b ≠ 0), f = single a b := by
  simp only [card_eq_one, support_eq_singleton']

theorem support_subset_singleton {f : α →₀ M} {a : α} : f.Support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.Support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩

theorem card_support_le_one [Nonempty α] {f : α →₀ M} : card f.Support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]

theorem card_support_le_one' [Nonempty α] {f : α →₀ M} : card f.Support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

@[simp]
theorem equiv_fun_on_fintype_single [DecidableEq α] [Fintype α] (x : α) (m : M) :
    (@Finsupp.equivFunOnFintype α M _ _) (Finsupp.single x m) = Pi.single x m := by
  ext
  simp [Finsupp.single_eq_pi_single, Finsupp.equivFunOnFintype]

@[simp]
theorem equiv_fun_on_fintype_symm_single [DecidableEq α] [Fintype α] (x : α) (m : M) :
    (@Finsupp.equivFunOnFintype α M _ _).symm (Pi.single x m) = Finsupp.single x m := by
  ext
  simp [Finsupp.single_eq_pi_single, Finsupp.equivFunOnFintype]

end Single

/-! ### Declarations about `update` -/


section Update

variable [Zero M] (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `finsupp.support`.
Otherwise, if `a` was not in the `finsupp.support`, it is added to it.

This is the finitely-supported version of `function.update`. -/
def update : α →₀ M :=
  ⟨if b = 0 then f.Support.erase a else insert a f.Support, Function.update f a b, fun i => by
    simp only [Function.update_apply, Ne.def]
    split_ifs with hb ha ha hb <;> simp [ha, hb]⟩

@[simp]
theorem coe_update [DecidableEq α] : (f.update a b : α → M) = Function.update f a b := by
  convert rfl

@[simp]
theorem update_self : f.update a (f a) = f := by
  ext
  simp

@[simp]
theorem zero_update : update 0 a b = single a b := by
  ext
  rw [single_eq_update]
  rfl

theorem support_update [DecidableEq α] :
    support (f.update a b) = if b = 0 then f.Support.erase a else insert a f.Support := by
  convert rfl

@[simp]
theorem support_update_zero [DecidableEq α] : support (f.update a 0) = f.Support.erase a := by
  convert if_pos rfl

variable {b}

theorem support_update_ne_zero [DecidableEq α] (h : b ≠ 0) : support (f.update a b) = insert a f.Support := by
  convert if_neg h

end Update

/-! ### Declarations about `erase` -/


section Erase

variable [Zero M]

/-- `erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →₀ M) : α →₀ M :=
  ⟨f.Support.erase a, fun a' => if a' = a then 0 else f a', fun a' => by
    rw [mem_erase, mem_support_iff] <;>
      split_ifs <;> [exact ⟨fun H _ => H.1 h, fun H => (H rfl).elim⟩, exact and_iff_right h]⟩

@[simp]
theorem support_erase [DecidableEq α] {a : α} {f : α →₀ M} : (f.erase a).Support = f.Support.erase a := by
  convert rfl

@[simp]
theorem erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 :=
  if_pos rfl

@[simp]
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' :=
  if_neg h

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 := by
  ext s
  by_cases' hs : s = a
  · rw [hs, erase_same]
    rfl
    
  · rw [erase_ne hs]
    exact single_eq_of_ne (Ne.symm hs)
    

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := by
  ext s
  by_cases' hs : s = a
  · rw [hs, erase_same, single_eq_of_ne h.symm]
    
  · rw [erase_ne hs]
    

@[simp]
theorem erase_of_not_mem_support {f : α →₀ M} {a} (haf : a ∉ f.Support) : erase a f = f := by
  ext b
  by_cases' hab : b = a
  · rwa [hab, erase_same, eq_comm, ← not_mem_support_iff]
    
  · rw [erase_ne hab]
    

@[simp]
theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 := by
  rw [← support_eq_empty, support_erase, support_zero, erase_empty]

end Erase

/-! ### Declarations about `on_finset` -/


section OnFinset

variable [Zero M]

/-- `on_finset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
The function must be `0` outside of `s`. Use this when the set needs to be filtered anyways,
otherwise a better set representation is often available. -/
def onFinset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ M :=
  ⟨s.filter fun a => f a ≠ 0, f, by
    simpa⟩

@[simp]
theorem on_finset_apply {s : Finset α} {f : α → M} {hf a} : (onFinset s f hf : α →₀ M) a = f a :=
  rfl

@[simp]
theorem support_on_finset_subset {s : Finset α} {f : α → M} {hf} : (onFinset s f hf).Support ⊆ s :=
  filter_subset _ _

@[simp]
theorem mem_support_on_finset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) {a : α} :
    a ∈ (Finsupp.onFinset s f hf).Support ↔ f a ≠ 0 := by
  rw [Finsupp.mem_support_iff, Finsupp.on_finset_apply]

theorem support_on_finset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) :
    (Finsupp.onFinset s f hf).Support = s.filter fun a => f a ≠ 0 :=
  rfl

end OnFinset

section OfSupportFinite

variable [Zero M]

/-- The natural `finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.Support f).Finite) : α →₀ M where
  Support := hf.toFinset
  toFun := f
  mem_support_to_fun := fun _ => hf.mem_to_finset

theorem of_support_finite_coe {f : α → M} {hf : (Function.Support f).Finite} : (ofSupportFinite f hf : α → M) = f :=
  rfl

instance : CanLift (α → M) (α →₀ M) where
  coe := coeFn
  cond := fun f => (Function.Support f).Finite
  prf := fun f hf => ⟨ofSupportFinite f hf, rfl⟩

end OfSupportFinite

/-! ### Declarations about `map_range` -/


section MapRange

variable [Zero M] [Zero N] [Zero P]

/-- The composition of `f : M → N` and `g : α →₀ M` is `map_range f hf g : α →₀ N`,
which is well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled (defined in `data/finsupp/basic`):

* `finsupp.map_range.equiv`
* `finsupp.map_range.zero_hom`
* `finsupp.map_range.add_monoid_hom`
* `finsupp.map_range.add_equiv`
* `finsupp.map_range.linear_map`
* `finsupp.map_range.linear_equiv`
-/
def mapRange (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  (onFinset g.Support (f ∘ g)) fun a => by
    rw [mem_support_iff, not_imp_not] <;> exact fun H => (congr_arg f H).trans hf

@[simp]
theorem map_range_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} : mapRange f hf g a = f (g a) :=
  rfl

@[simp]
theorem map_range_zero {f : M → N} {hf : f 0 = 0} : mapRange f hf (0 : α →₀ M) = 0 :=
  ext fun a => by
    simp only [hf, zero_apply, map_range_apply]

@[simp]
theorem map_range_id (g : α →₀ M) : mapRange id rfl g = g :=
  ext fun _ => rfl

theorem map_range_comp (f : N → P) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0) (g : α →₀ M) :
    mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl

theorem support_map_range {f : M → N} {hf : f 0 = 0} {g : α →₀ M} : (mapRange f hf g).Support ⊆ g.Support :=
  support_on_finset_subset

@[simp]
theorem map_range_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} : mapRange f hf (single a b) = single a (f b) :=
  ext fun a' =>
    show f (ite _ _ _) = ite _ _ _ by
      split_ifs <;> [rfl, exact hf]

theorem support_map_range_of_injective {e : M → N} (he0 : e 0 = 0) (f : ι →₀ M) (he : Function.Injective e) :
    (Finsupp.mapRange e he0 f).Support = f.Support := by
  ext
  simp only [Finsupp.mem_support_iff, Ne.def, Finsupp.map_range_apply]
  exact he.ne_iff' he0

end MapRange

/-! ### Declarations about `emb_domain` -/


section EmbDomain

variable [Zero M] [Zero N]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `emb_domain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def embDomain (f : α ↪ β) (v : α →₀ M) : β →₀ M := by
  refine'
    ⟨v.support.map f, fun a₂ => if h : a₂ ∈ v.support.map f then v (v.support.choose (fun a₁ => f a₁ = a₂) _) else 0, _⟩
  · rcases Finset.mem_map.1 h with ⟨a, ha, rfl⟩
    exact ExistsUnique.intro a ⟨ha, rfl⟩ fun b ⟨_, hb⟩ => f.injective hb
    
  · intro a₂
    split_ifs
    · simp only [h, true_iffₓ, Ne.def]
      rw [← not_mem_support_iff, not_not]
      apply Finset.choose_mem
      
    · simp only [h, Ne.def, ne_self_iff_false]
      
    

@[simp]
theorem support_emb_domain (f : α ↪ β) (v : α →₀ M) : (embDomain f v).Support = v.Support.map f :=
  rfl

@[simp]
theorem emb_domain_zero (f : α ↪ β) : (embDomain f 0 : β →₀ M) = 0 :=
  rfl

@[simp]
theorem emb_domain_apply (f : α ↪ β) (v : α →₀ M) (a : α) : embDomain f v (f a) = v a := by
  change dite _ _ _ = _
  split_ifs <;> rw [Finset.mem_map' f] at h
  · refine' congr_arg (v : α → M) (f.inj' _)
    exact Finset.choose_property (fun a₁ => f a₁ = f a) _ _
    
  · exact (not_mem_support_iff.1 h).symm
    

theorem emb_domain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ Set.Range f) : embDomain f v a = 0 := by
  refine' dif_neg (mt (fun h => _) h)
  rcases Finset.mem_map.1 h with ⟨a, h, rfl⟩
  exact Set.mem_range_self a

theorem emb_domain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →₀ M) → β →₀ M) := fun l₁ l₂ h =>
  ext fun a => by
    simpa only [emb_domain_apply] using ext_iff.1 h (f a)

@[simp]
theorem emb_domain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (emb_domain_injective f).eq_iff

@[simp]
theorem emb_domain_eq_zero {f : α ↪ β} {l : α →₀ M} : embDomain f l = 0 ↔ l = 0 :=
  (emb_domain_injective f).eq_iff' <| emb_domain_zero f

theorem emb_domain_map_range (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by
  ext a
  by_cases' a ∈ Set.Range f
  · rcases h with ⟨a', rfl⟩
    rw [map_range_apply, emb_domain_apply, emb_domain_apply, map_range_apply]
    
  · rw [map_range_apply, emb_domain_notin_range, emb_domain_notin_range, ← hg] <;> assumption
    

theorem single_of_emb_domain_single (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
    (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  have h_map_support : Finset.map f l.support = {a} := by
    rw [← support_emb_domain, h, support_single_ne_zero _ hb] <;> rfl
  have ha : a ∈ Finset.map f l.support := by
    simp only [h_map_support, Finset.mem_singleton]
  rcases Finset.mem_map.1 ha with ⟨c, hc₁, hc₂⟩
  use c
  constructor
  · ext d
    rw [← emb_domain_apply f l, h]
    by_cases' h_cases : c = d
    · simp only [Eq.symm h_cases, hc₂, single_eq_same]
      
    · rw [single_apply, single_apply, if_neg, if_neg h_cases]
      by_contra hfd
      exact h_cases (f.injective (hc₂.trans hfd))
      
    
  · exact hc₂
    

@[simp]
theorem emb_domain_single (f : α ↪ β) (a : α) (m : M) : embDomain f (single a m) = single (f a) m := by
  ext b
  by_cases' h : b ∈ Set.Range f
  · rcases h with ⟨a', rfl⟩
    simp [single_apply]
    
  · simp only [emb_domain_notin_range, h, single_apply, not_false_iff]
    rw [if_neg]
    rintro rfl
    simpa using h
    

end EmbDomain

/-! ### Declarations about `zip_with` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

/-- Given finitely supported functions `g₁ : α →₀ M` and `g₂ : α →₀ N` and function `f : M → N → P`,
`zip_with f hf g₁ g₂` is the finitely supported function `α →₀ P` satisfying
`zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f 0 0 = 0`. -/
def zipWith (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  (onFinset (g₁.Support ∪ g₂.Support) fun a => f (g₁ a) (g₂ a)) fun a H => by
    simp only [mem_union, mem_support_iff, Ne]
    rw [← not_and_distrib]
    rintro ⟨h₁, h₂⟩
    rw [h₁, h₂] at H
    exact H hf

@[simp]
theorem zip_with_apply {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

theorem support_zip_with [D : DecidableEq α] {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} :
    (zipWith f hf g₁ g₂).Support ⊆ g₁.Support ∪ g₂.Support := by
  rw [Subsingleton.elimₓ D] <;> exact support_on_finset_subset

end ZipWith

/-! ### Additive monoid structure on `α →₀ M` -/


section AddZeroClassₓ

variable [AddZeroClassₓ M]

instance : Add (α →₀ M) :=
  ⟨zipWith (· + ·) (add_zeroₓ 0)⟩

@[simp]
theorem coe_add (f g : α →₀ M) : ⇑(f + g) = f + g :=
  rfl

theorem add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ + g₂) a = g₁ a + g₂ a :=
  rfl

theorem support_add [DecidableEq α] {g₁ g₂ : α →₀ M} : (g₁ + g₂).Support ⊆ g₁.Support ∪ g₂.Support :=
  support_zip_with

theorem support_add_eq [DecidableEq α] {g₁ g₂ : α →₀ M} (h : Disjoint g₁.Support g₂.Support) :
    (g₁ + g₂).Support = g₁.Support ∪ g₂.Support :=
  (le_antisymmₓ support_zip_with) fun a ha =>
    (Finset.mem_union.1 ha).elim
      (fun ha => by
        have : a ∉ g₂.Support := disjoint_left.1 h ha
        simp only [mem_support_iff, not_not] at * <;> simpa only [add_apply, this, add_zeroₓ] )
      fun ha => by
      have : a ∉ g₁.Support := disjoint_right.1 h ha
      simp only [mem_support_iff, not_not] at * <;> simpa only [add_apply, this, zero_addₓ]

@[simp]
theorem single_add (a : α) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  ext fun a' => by
    by_cases' h : a = a'
    · rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same]
      
    · rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_addₓ]
      

instance : AddZeroClassₓ (α →₀ M) :=
  FunLike.coe_injective.AddZeroClass _ coe_zero coe_add

/-- `finsupp.single` as an `add_monoid_hom`.

See `finsupp.lsingle` in `linear_algebra/finsupp` for the stronger version as a linear map. -/
@[simps]
def singleAddHom (a : α) : M →+ α →₀ M :=
  ⟨single a, single_zero a, single_add a⟩

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `finsupp.lapply` in `linear_algebra/finsupp` for the stronger version as a linear map. -/
@[simps apply]
def applyAddHom (a : α) : (α →₀ M) →+ M :=
  ⟨fun g => g a, zero_apply, fun _ _ => add_apply _ _ _⟩

/-- Coercion from a `finsupp` to a function type is an `add_monoid_hom`. -/
@[simps]
noncomputable def coeFnAddHom : (α →₀ M) →+ α → M where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add

theorem update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) : f.update a b = single a b + f.erase a := by
  ext j
  rcases eq_or_ne a j with (rfl | h)
  · simp
    
  · simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]
    

theorem update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) : f.update a b = f.erase a + single a b := by
  ext j
  rcases eq_or_ne a j with (rfl | h)
  · simp
    
  · simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]
    

theorem single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.erase a = f := by
  rw [← update_eq_single_add_erase, update_self]

theorem erase_add_single (a : α) (f : α →₀ M) : f.erase a + single a (f a) = f := by
  rw [← update_eq_erase_add_single, update_self]

@[simp]
theorem erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s
  by_cases' hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zeroₓ]
    
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]

/-- `finsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def eraseAddHom (a : α) : (α →₀ M) →+ α →₀ M where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a

@[elabAsElim]
protected theorem induction {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.Support → b ≠ 0 → p f → p (single a b + f)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.Support = s → p f from this _ _ rfl
  fun s =>
  (Finset.induction_on s fun f hf => by
      rwa [support_eq_empty.1 hf])
    fun a s has ih f hf => by
    suffices p (single a (f a) + f.erase a) by
      rwa [single_add_erase] at this
    apply ha
    · rw [support_erase, mem_erase]
      exact fun H => H.1 rfl
      
    · rw [← mem_support_iff, hf]
      exact mem_insert_self _ _
      
    · apply ih _ _
      rw [support_erase, hf, Finset.erase_insert has]
      

theorem induction₂ {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.Support → b ≠ 0 → p f → p (f + single a b)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.Support = s → p f from this _ _ rfl
  fun s =>
  (Finset.induction_on s fun f hf => by
      rwa [support_eq_empty.1 hf])
    fun a s has ih f hf => by
    suffices p (f.erase a + single a (f a)) by
      rwa [erase_add_single] at this
    apply ha
    · rw [support_erase, mem_erase]
      exact fun H => H.1 rfl
      
    · rw [← mem_support_iff, hf]
      exact mem_insert_self _ _
      
    · apply ih _ _
      rw [support_erase, hf, Finset.erase_insert has]
      

theorem induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0) (hadd : ∀ f g : α →₀ M, p f → p g → p (f + g))
    (hsingle : ∀ a b, p (single a b)) : p f :=
  induction₂ f h0 fun a b f _ _ w => hadd _ _ w (hsingle _ _)

@[simp]
theorem add_closure_set_of_eq_single : AddSubmonoid.closure { f : α →₀ M | ∃ a b, f = single a b } = ⊤ :=
  top_unique fun x hx =>
    (Finsupp.induction x (AddSubmonoid.zero_mem _)) fun a b f ha hb hf =>
      AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure <| ⟨a, b, rfl⟩) hf

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`,
then they are equal. -/
theorem add_hom_ext [AddZeroClassₓ N] ⦃f g : (α →₀ M) →+ N⦄ (H : ∀ x y, f (single x y) = g (single x y)) : f = g := by
  refine' AddMonoidHom.eq_of_eq_on_mdense add_closure_set_of_eq_single _
  rintro _ ⟨x, y, rfl⟩
  apply H

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`,
then they are equal.

We formulate this using equality of `add_monoid_hom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext]
theorem add_hom_ext' [AddZeroClassₓ N] ⦃f g : (α →₀ M) →+ N⦄
    (H : ∀ x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g :=
  add_hom_ext fun x => AddMonoidHom.congr_fun (H x)

theorem mul_hom_ext [MulOneClassₓ N] ⦃f g : Multiplicative (α →₀ M) →* N⦄
    (H : ∀ x y, f (Multiplicative.ofAdd <| single x y) = g (Multiplicative.ofAdd <| single x y)) : f = g :=
  MonoidHom.ext <| AddMonoidHom.congr_fun <| @add_hom_ext α M (Additive N) _ _ f.toAdditive'' g.toAdditive'' H

@[ext]
theorem mul_hom_ext' [MulOneClassₓ N] {f g : Multiplicative (α →₀ M) →* N}
    (H : ∀ x, f.comp (singleAddHom x).toMultiplicative = g.comp (singleAddHom x).toMultiplicative) : f = g :=
  mul_hom_ext fun x => MonoidHom.congr_fun (H x)

theorem map_range_add [AddZeroClassₓ N] {f : M → N} {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y)
    (v₁ v₂ : α →₀ M) : mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun a => by
    simp only [hf', add_apply, map_range_apply]

/-- Bundle `emb_domain f` as an additive map from `α →₀ M` to `β →₀ M`. -/
@[simps]
def embDomain.addMonoidHom (f : α ↪ β) : (α →₀ M) →+ β →₀ M where
  toFun := fun v => embDomain f v
  map_zero' := by
    simp
  map_add' := fun v w => by
    ext b
    by_cases' h : b ∈ Set.Range f
    · rcases h with ⟨a, rfl⟩
      simp
      
    · simp [emb_domain_notin_range, h]
      

@[simp]
theorem emb_domain_add (f : α ↪ β) (v w : α →₀ M) : embDomain f (v + w) = embDomain f v + embDomain f w :=
  (embDomain.addMonoidHom f).map_add v w

end AddZeroClassₓ

section AddMonoidₓ

variable [AddMonoidₓ M]

/-- Note the general `finsupp.has_smul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasNatScalar : HasSmul ℕ (α →₀ M) :=
  ⟨fun n v => v.map_range ((· • ·) n) (nsmul_zero _)⟩

instance : AddMonoidₓ (α →₀ M) :=
  FunLike.coe_injective.AddMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoidₓ

instance [AddCommMonoidₓ M] : AddCommMonoidₓ (α →₀ M) :=
  FunLike.coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => rfl

instance [AddGroupₓ G] : Neg (α →₀ G) :=
  ⟨mapRange Neg.neg neg_zero⟩

@[simp]
theorem coe_neg [AddGroupₓ G] (g : α →₀ G) : ⇑(-g) = -g :=
  rfl

theorem neg_apply [AddGroupₓ G] (g : α →₀ G) (a : α) : (-g) a = -g a :=
  rfl

instance [AddGroupₓ G] : Sub (α →₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩

@[simp]
theorem coe_sub [AddGroupₓ G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl

theorem sub_apply [AddGroupₓ G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a :=
  rfl

/-- Note the general `finsupp.has_smul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasIntScalar [AddGroupₓ G] : HasSmul ℤ (α →₀ G) :=
  ⟨fun n v => v.map_range ((· • ·) n) (zsmul_zero _)⟩

instance [AddGroupₓ G] : AddGroupₓ (α →₀ G) :=
  FunLike.coe_injective.AddGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance [AddCommGroupₓ G] : AddCommGroupₓ (α →₀ G) :=
  FunLike.coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

theorem single_add_single_eq_single_add_single [AddCommMonoidₓ M] {k l m n : α} {u v : M} (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n :=
  by
  simp_rw [FunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
  exact Pi.single_add_single_eq_single_add_single hu hv

@[simp]
theorem support_neg [AddGroupₓ G] (f : α →₀ G) : support (-f) = support f :=
  Finset.Subset.antisymm support_map_range
    (calc
      support f = support (- -f) := congr_arg support (neg_negₓ _).symm
      _ ⊆ support (-f) := support_map_range
      )

theorem support_sub [DecidableEq α] [AddGroupₓ G] {f g : α →₀ G} : support (f - g) ⊆ support f ∪ support g := by
  rw [sub_eq_add_neg, ← support_neg g]
  exact support_add

theorem erase_eq_sub_single [AddGroupₓ G] (f : α →₀ G) (a : α) : f.erase a = f - single a (f a) := by
  ext a'
  rcases eq_or_ne a a' with (rfl | h)
  · simp
    
  · simp [erase_ne h.symm, single_eq_of_ne h]
    

theorem update_eq_sub_add_single [AddGroupₓ G] (f : α →₀ G) (a : α) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single, erase_eq_sub_single]

end Finsupp

