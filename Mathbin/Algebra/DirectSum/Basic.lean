/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Data.Dfinsupp.Basic
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `direct_sum`.
This notation is in the `direct_sum` locale, accessible after `open_locale direct_sum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/


open_locale BigOperators

universe u v w u₁

variable (ι : Type v) [dec_ι : DecidableEq ι] (β : ι → Type w)

/-- `direct_sum β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open_locale direct_sum` will enable the notation `⨁ i, β i` for `direct_sum β`. -/
def DirectSum [∀ i, AddCommMonoidₓ (β i)] : Type _ :=
  Π₀ i, β i deriving AddCommMonoidₓ, Inhabited

instance [∀ i, AddCommMonoidₓ (β i)] : CoeFun (DirectSum ι β) fun _ => ∀ i : ι, β i :=
  Dfinsupp.hasCoeToFun

-- mathport name: «expr⨁ , »
localized [DirectSum] notation3 "⨁ " (...) ", " r:(scoped f => DirectSum _ f) => r

namespace DirectSum

variable {ι}

section AddCommGroupₓ

variable [∀ i, AddCommGroupₓ (β i)]

instance : AddCommGroupₓ (DirectSum ι β) :=
  Dfinsupp.addCommGroup

variable {β}

@[simp]
theorem sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  Dfinsupp.sub_apply _ _ _

end AddCommGroupₓ

variable [∀ i, AddCommMonoidₓ (β i)]

@[simp]
theorem zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0 :=
  rfl

variable {β}

@[simp]
theorem add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
  Dfinsupp.add_apply _ _ _

variable (β)

include dec_ι

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
def mk (s : Finset ι) : (∀ i : (↑s : Set ι), β i.1) →+ ⨁ i, β i where
  toFun := Dfinsupp.mk s
  map_add' := fun _ _ => Dfinsupp.mk_add
  map_zero' := Dfinsupp.mk_zero

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
def of (i : ι) : β i →+ ⨁ i, β i :=
  Dfinsupp.singleAddHom β i

@[simp]
theorem of_eq_same (i : ι) (x : β i) : (of _ i x) i = x :=
  Dfinsupp.single_eq_same

theorem of_eq_of_ne (i j : ι) (x : β i) (h : i ≠ j) : (of _ i x) j = 0 :=
  Dfinsupp.single_eq_of_ne h

@[simp]
theorem support_zero [∀ i : ι x : β i, Decidable (x ≠ 0)] : (0 : ⨁ i, β i).support = ∅ :=
  Dfinsupp.support_zero

@[simp]
theorem support_of [∀ i : ι x : β i, Decidable (x ≠ 0)] (i : ι) (x : β i) (h : x ≠ 0) : (of _ i x).support = {i} :=
  Dfinsupp.support_single_ne_zero h

theorem support_of_subset [∀ i : ι x : β i, Decidable (x ≠ 0)] {i : ι} {b : β i} : (of _ i b).support ⊆ {i} :=
  Dfinsupp.support_single_subset

theorem sum_support_of [∀ i : ι x : β i, Decidable (x ≠ 0)] (x : ⨁ i, β i) : (∑ i in x.support, of β i (x i)) = x :=
  Dfinsupp.sum_single

variable {β}

theorem mk_injective (s : Finset ι) : Function.Injective (mk β s) :=
  Dfinsupp.mk_injective s

theorem of_injective (i : ι) : Function.Injective (of β i) :=
  Dfinsupp.single_injective

@[elab_as_eliminator]
protected theorem induction_on {C : (⨁ i, β i) → Prop} (x : ⨁ i, β i) (H_zero : C 0)
    (H_basic : ∀ i : ι x : β i, C (of β i x)) (H_plus : ∀ x y, C x → C y → C (x + y)) : C x := by
  apply Dfinsupp.induction x H_zero
  intro i b f h1 h2 ih
  solve_by_elim

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal. -/
theorem add_hom_ext {γ : Type _} [AddMonoidₓ γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ i : ι y : β i, f (of _ i y) = g (of _ i y)) : f = g :=
  Dfinsupp.add_hom_ext H

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem add_hom_ext' {γ : Type _} [AddMonoidₓ γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g :=
  add_hom_ext fun i => AddMonoidHom.congr_fun <| H i

variable {γ : Type u₁} [AddCommMonoidₓ γ]

section ToAddMonoid

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

/-- `to_add_monoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def toAddMonoid : (⨁ i, β i) →+ γ :=
  Dfinsupp.liftAddHom φ

@[simp]
theorem to_add_monoid_of i (x : β i) : toAddMonoid φ (of β i x) = φ i x :=
  Dfinsupp.lift_add_hom_apply_single φ i x

theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f := by
  congr
  ext
  simp [to_add_monoid, of]

end ToAddMonoid

section FromAddMonoid

/-- `from_add_monoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` arises in this way. -/
def fromAddMonoid : (⨁ i, γ →+ β i) →+ γ →+ ⨁ i, β i :=
  to_add_monoid fun i => AddMonoidHom.compHom (of β i)

@[simp]
theorem from_add_monoid_of (i : ι) (f : γ →+ β i) : fromAddMonoid (of _ i f) = (of _ i).comp f := by
  rw [from_add_monoid, to_add_monoid_of]
  rfl

theorem from_add_monoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) : fromAddMonoid (of _ i f) x = of _ i (f x) := by
  rw [from_add_monoid_of, AddMonoidHom.coe_comp]

end FromAddMonoid

variable (β)

/-- `set_to_set β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
-- TODO: generalize this to remove the assumption `S ⊆ T`.
def setToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, β i) →+ ⨁ i : T, β i :=
  to_add_monoid fun i => of (fun i : Subtype T => β i) ⟨↑i, H i.Prop⟩

variable {β}

omit dec_ι

/-- The natural equivalence between `⨁ _ : ι, M` and `M` when `unique ι`. -/
protected def id (M : Type v) (ι : Type _ := PUnit) [AddCommMonoidₓ M] [Unique ι] : (⨁ _ : ι, M) ≃+ M :=
  { DirectSum.toAddMonoid fun _ => AddMonoidHom.id M with toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M,
    invFun := of (fun _ => M) default,
    left_inv := fun x =>
      DirectSum.induction_on x
        (by
          rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero])
        (fun p x => by
          rw [Unique.default_eq p, to_add_monoid_of] <;> rfl)
        fun x y ihx ihy => by
        rw [AddMonoidHom.map_add, AddMonoidHom.map_add, ihx, ihy],
    right_inv := fun x => to_add_monoid_of _ _ _ }

/-- The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `add_submonoid M`
indexed by `ι`-/
def addSubmonoidCoe {M : Type _} [DecidableEq ι] [AddCommMonoidₓ M] (A : ι → AddSubmonoid M) : (⨁ i, A i) →+ M :=
  toAddMonoid fun i => (A i).Subtype

@[simp]
theorem add_submonoid_coe_of {M : Type _} [DecidableEq ι] [AddCommMonoidₓ M] (A : ι → AddSubmonoid M) (i : ι)
    (x : A i) : addSubmonoidCoe A (of (fun i => A i) i x) = x :=
  to_add_monoid_of _ _ _

theorem coe_of_add_submonoid_apply {M : Type _} [DecidableEq ι] [AddCommMonoidₓ M] {A : ι → AddSubmonoid M} (i j : ι)
    (x : A i) : (of _ i x j : M) = if i = j then x else 0 := by
  obtain rfl | h := Decidable.eq_or_ne i j
  · rw [DirectSum.of_eq_same, if_pos rfl]
    
  · rw [DirectSum.of_eq_of_ne _ _ _ _ h, if_neg h, AddSubmonoid.coe_zero]
    

/-- The `direct_sum` formed by a collection of `add_submonoid`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →+ M` is bijective.

See `direct_sum.add_subgroup_is_internal` for the same statement about `add_subgroup`s. -/
def AddSubmonoidIsInternal {M : Type _} [DecidableEq ι] [AddCommMonoidₓ M] (A : ι → AddSubmonoid M) : Prop :=
  Function.Bijective (addSubmonoidCoe A)

theorem AddSubmonoidIsInternal.supr_eq_top {M : Type _} [DecidableEq ι] [AddCommMonoidₓ M] (A : ι → AddSubmonoid M)
    (h : AddSubmonoidIsInternal A) : supr A = ⊤ := by
  rw [AddSubmonoid.supr_eq_mrange_dfinsupp_sum_add_hom, AddMonoidHom.mrange_top_iff_surjective]
  exact Function.Bijective.surjective h

/-- The canonical embedding from `⨁ i, A i` to `M`  where `A` is a collection of `add_subgroup M`
indexed by `ι`-/
def addSubgroupCoe {M : Type _} [DecidableEq ι] [AddCommGroupₓ M] (A : ι → AddSubgroup M) : (⨁ i, A i) →+ M :=
  toAddMonoid fun i => (A i).Subtype

@[simp]
theorem add_subgroup_coe_of {M : Type _} [DecidableEq ι] [AddCommGroupₓ M] (A : ι → AddSubgroup M) (i : ι) (x : A i) :
    addSubgroupCoe A (of (fun i => A i) i x) = x :=
  to_add_monoid_of _ _ _

theorem coe_of_add_subgroup_apply {M : Type _} [DecidableEq ι] [AddCommGroupₓ M] {A : ι → AddSubgroup M} (i j : ι)
    (x : A i) : (of _ i x j : M) = if i = j then x else 0 := by
  obtain rfl | h := Decidable.eq_or_ne i j
  · rw [DirectSum.of_eq_same, if_pos rfl]
    
  · rw [DirectSum.of_eq_of_ne _ _ _ _ h, if_neg h, AddSubgroup.coe_zero]
    

/-- The `direct_sum` formed by a collection of `add_subgroup`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →+ M` is bijective.

See `direct_sum.submodule_is_internal` for the same statement about `submodules`s. -/
def AddSubgroupIsInternal {M : Type _} [DecidableEq ι] [AddCommGroupₓ M] (A : ι → AddSubgroup M) : Prop :=
  Function.Bijective (addSubgroupCoe A)

theorem AddSubgroupIsInternal.to_add_submonoid {M : Type _} [DecidableEq ι] [AddCommGroupₓ M] (A : ι → AddSubgroup M) :
    AddSubgroupIsInternal A ↔ AddSubmonoidIsInternal fun i => (A i).toAddSubmonoid :=
  Iff.rfl

end DirectSum

