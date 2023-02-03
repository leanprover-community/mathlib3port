/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.big_operators.finprod
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.IndicatorFunction

/-!
# Finite products and sums over types and sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define products and sums over types and subsets of types, with no finiteness hypotheses.
All infinite products and sums are defined to be junk values (i.e. one or zero).
This approach is sometimes easier to use than `finset.sum`,
when issues arise with `finset` and `fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
   Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
   it's finite. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∏ᶠ i, f i` and `∏ᶠ i : α, f i` for `finprod f`

This notation works for functions `f : p → M`, where `p : Prop`, so the following works:

* `∑ᶠ i ∈ s, f i`, where `f : α → M`, `s : set α` : sum over the set `s`;
* `∑ᶠ n < 5, f n`, where `f : ℕ → M` : same as `f 0 + f 1 + f 2 + f 3 + f 4`;
* `∏ᶠ (n >= -2) (hn : n < 3), f n`, where `f : ℤ → M` : same as `f (-2) * f (-1) * f 0 * f 1 * f 2`.

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `finset` and
`fintype`. By sticking solely to `set.finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
function. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

We did not add `is_finite (X : Type) : Prop`, because it is simply `nonempty (fintype X)`.

## Tags

finsum, finprod, finite sum, finite product
-/


open Function Set

/-!
### Definition and relation to `finset.sum` and `finset.prod`
-/


section Sort

variable {G M N : Type _} {α β ι : Sort _} [CommMonoid M] [CommMonoid N]

open BigOperators

section

/- Note: we use classical logic only for these definitions, to ensure that we do not write lemmas
with `classical.dec` in their statement. -/
open Classical

#print finsum /-
/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
otherwise. -/
noncomputable irreducible_def finsum {M α} [AddCommMonoid M] (f : α → M) : M :=
  if h : (support (f ∘ PLift.down)).Finite then ∑ i in h.toFinset, f i.down else 0
#align finsum finsum
-/

#print finprod /-
/-- Product of `f x` as `x` ranges over the elements of the multiplicative support of `f`, if it's
finite. One otherwise. -/
@[to_additive]
noncomputable irreducible_def finprod (f : α → M) : M :=
  if h : (mulSupport (f ∘ PLift.down)).Finite then ∏ i in h.toFinset, f i.down else 1
#align finprod finprod
#align finsum finsum
-/

end

-- mathport name: finsum
scoped[BigOperators] notation3"∑ᶠ "(...)", "r:(scoped f => finsum f) => r

-- mathport name: finprod
scoped[BigOperators] notation3"∏ᶠ "(...)", "r:(scoped f => finprod f) => r

/- warning: finprod_eq_prod_plift_of_mul_support_to_finset_subset -> finprod_eq_prod_pLift_of_mulSupport_toFinset_subset is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} (hf : Set.Finite.{u2} (PLift.{u2} α) (Function.mulSupport.{u2, u1} (PLift.{u2} α) M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Function.comp.{succ u2, u2, succ u1} (PLift.{u2} α) α M f (PLift.down.{u2} α)))) {s : Finset.{u2} (PLift.{u2} α)}, (HasSubset.Subset.{u2} (Finset.{u2} (PLift.{u2} α)) (Finset.hasSubset.{u2} (PLift.{u2} α)) (Set.Finite.toFinset.{u2} (PLift.{u2} α) (Function.mulSupport.{u2, u1} (PLift.{u2} α) M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Function.comp.{succ u2, u2, succ u1} (PLift.{u2} α) α M f (PLift.down.{u2} α))) hf) s) -> (Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M (PLift.{u2} α) _inst_1 s (fun (i : PLift.{u2} α) => f (PLift.down.{u2} α i))))
but is expected to have type
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} (hf : Set.Finite.{u2} (PLift.{u2} α) (Function.mulSupport.{u2, u1} (PLift.{u2} α) M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Function.comp.{succ u2, u2, succ u1} (PLift.{u2} α) α M f (PLift.down.{u2} α)))) {s : Finset.{u2} (PLift.{u2} α)}, (HasSubset.Subset.{u2} (Finset.{u2} (PLift.{u2} α)) (Finset.instHasSubsetFinset.{u2} (PLift.{u2} α)) (Set.Finite.toFinset.{u2} (PLift.{u2} α) (Function.mulSupport.{u2, u1} (PLift.{u2} α) M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Function.comp.{succ u2, u2, succ u1} (PLift.{u2} α) α M f (PLift.down.{u2} α))) hf) s) -> (Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M (PLift.{u2} α) _inst_1 s (fun (i : PLift.{u2} α) => f (PLift.down.{u2} α i))))
Case conversion may be inaccurate. Consider using '#align finprod_eq_prod_plift_of_mul_support_to_finset_subset finprod_eq_prod_pLift_of_mulSupport_toFinset_subsetₓ'. -/
@[to_additive]
theorem finprod_eq_prod_pLift_of_mulSupport_toFinset_subset {f : α → M}
    (hf : (mulSupport (f ∘ PLift.down)).Finite) {s : Finset (PLift α)} (hs : hf.toFinset ⊆ s) :
    (∏ᶠ i, f i) = ∏ i in s, f i.down :=
  by
  rw [finprod, dif_pos]
  refine' Finset.prod_subset hs fun x hx hxf => _
  rwa [hf.mem_to_finset, nmem_mul_support] at hxf
#align finprod_eq_prod_plift_of_mul_support_to_finset_subset finprod_eq_prod_pLift_of_mulSupport_toFinset_subset
#align finsum_eq_sum_plift_of_support_to_finset_subset finsum_eq_sum_pLift_of_support_toFinset_subset

/- warning: finprod_eq_prod_plift_of_mul_support_subset -> finprod_eq_prod_pLift_of_mulSupport_subset is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Finset.{u2} (PLift.{u2} α)}, (HasSubset.Subset.{u2} (Set.{u2} (PLift.{u2} α)) (Set.hasSubset.{u2} (PLift.{u2} α)) (Function.mulSupport.{u2, u1} (PLift.{u2} α) M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Function.comp.{succ u2, u2, succ u1} (PLift.{u2} α) α M f (PLift.down.{u2} α))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} (PLift.{u2} α)) (Set.{u2} (PLift.{u2} α)) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} (PLift.{u2} α)) (Set.{u2} (PLift.{u2} α)) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} (PLift.{u2} α)) (Set.{u2} (PLift.{u2} α)) (Finset.Set.hasCoeT.{u2} (PLift.{u2} α)))) s)) -> (Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M (PLift.{u2} α) _inst_1 s (fun (i : PLift.{u2} α) => f (PLift.down.{u2} α i))))
but is expected to have type
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Finset.{u2} (PLift.{u2} α)}, (HasSubset.Subset.{u2} (Set.{u2} (PLift.{u2} α)) (Set.instHasSubsetSet.{u2} (PLift.{u2} α)) (Function.mulSupport.{u2, u1} (PLift.{u2} α) M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Function.comp.{succ u2, u2, succ u1} (PLift.{u2} α) α M f (PLift.down.{u2} α))) (Finset.toSet.{u2} (PLift.{u2} α) s)) -> (Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M (PLift.{u2} α) _inst_1 s (fun (i : PLift.{u2} α) => f (PLift.down.{u2} α i))))
Case conversion may be inaccurate. Consider using '#align finprod_eq_prod_plift_of_mul_support_subset finprod_eq_prod_pLift_of_mulSupport_subsetₓ'. -/
@[to_additive]
theorem finprod_eq_prod_pLift_of_mulSupport_subset {f : α → M} {s : Finset (PLift α)}
    (hs : mulSupport (f ∘ PLift.down) ⊆ s) : (∏ᶠ i, f i) = ∏ i in s, f i.down :=
  finprod_eq_prod_pLift_of_mulSupport_toFinset_subset (s.finite_toSet.Subset hs) fun x hx =>
    by
    rw [finite.mem_to_finset] at hx
    exact hs hx
#align finprod_eq_prod_plift_of_mul_support_subset finprod_eq_prod_pLift_of_mulSupport_subset
#align finsum_eq_sum_plift_of_support_subset finsum_eq_sum_pLift_of_support_subset

/- warning: finprod_one -> finprod_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M], Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (i : α) => OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u2}} {α : Sort.{u1}} [_inst_1 : CommMonoid.{u2} M], Eq.{succ u2} M (finprod.{u2, u1} M α _inst_1 (fun (i : α) => OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finprod_one finprod_oneₓ'. -/
@[simp, to_additive]
theorem finprod_one : (∏ᶠ i : α, (1 : M)) = 1 :=
  by
  have : (mul_support fun x : PLift α => (fun _ => 1 : α → M) x.down) ⊆ (∅ : Finset (PLift α)) :=
    fun x h => h rfl
  rw [finprod_eq_prod_pLift_of_mulSupport_subset this, Finset.prod_empty]
#align finprod_one finprod_one
#align finsum_zero finsum_zero

/- warning: finprod_of_is_empty -> finprod_of_isEmpty is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_3 : IsEmpty.{u2} α] (f : α -> M), Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (i : α) => f i)) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_3 : IsEmpty.{u2} α] (f : α -> M), Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (i : α) => f i)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finprod_of_is_empty finprod_of_isEmptyₓ'. -/
@[to_additive]
theorem finprod_of_isEmpty [IsEmpty α] (f : α → M) : (∏ᶠ i, f i) = 1 :=
  by
  rw [← finprod_one]
  congr
#align finprod_of_is_empty finprod_of_isEmpty
#align finsum_of_is_empty finsum_of_isEmpty

/- warning: finprod_false -> finprod_false is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : False -> M), Eq.{succ u1} M (finprod.{u1, 0} M False _inst_1 (fun (i : False) => f i)) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : False -> M), Eq.{succ u1} M (finprod.{u1, 0} M False _inst_1 (fun (i : False) => f i)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finprod_false finprod_falseₓ'. -/
@[simp, to_additive]
theorem finprod_false (f : False → M) : (∏ᶠ i, f i) = 1 :=
  finprod_of_isEmpty _
#align finprod_false finprod_false
#align finsum_false finsum_false

/- warning: finprod_eq_single -> finprod_eq_single is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (a : α), (forall (x : α), (Ne.{u2} α x a) -> (Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))))) -> (Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (x : α) => f x)) (f a))
but is expected to have type
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (a : α), (forall (x : α), (Ne.{u2} α x a) -> (Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))) -> (Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 (fun (x : α) => f x)) (f a))
Case conversion may be inaccurate. Consider using '#align finprod_eq_single finprod_eq_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ≠ » a) -/
@[to_additive]
theorem finprod_eq_single (f : α → M) (a : α) (ha : ∀ (x) (_ : x ≠ a), f x = 1) :
    (∏ᶠ x, f x) = f a :=
  by
  have : mul_support (f ∘ PLift.down) ⊆ ({PLift.up a} : Finset (PLift α)) :=
    by
    intro x
    contrapose
    simpa [PLift.eq_up_iff_down_eq] using ha x.down
  rw [finprod_eq_prod_pLift_of_mulSupport_subset this, Finset.prod_singleton]
#align finprod_eq_single finprod_eq_single
#align finsum_eq_single finsum_eq_single

#print finprod_unique /-
@[to_additive]
theorem finprod_unique [Unique α] (f : α → M) : (∏ᶠ i, f i) = f default :=
  finprod_eq_single f default fun x hx => (hx <| Unique.eq_default _).elim
#align finprod_unique finprod_unique
#align finsum_unique finsum_unique
-/

#print finprod_true /-
@[simp, to_additive]
theorem finprod_true (f : True → M) : (∏ᶠ i, f i) = f trivial :=
  @finprod_unique M True _ ⟨⟨trivial⟩, fun _ => rfl⟩ f
#align finprod_true finprod_true
#align finsum_true finsum_true
-/

/- warning: finprod_eq_dif -> finprod_eq_dif is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {p : Prop} [_inst_3 : Decidable p] (f : p -> M), Eq.{succ u1} M (finprod.{u1, 0} M p _inst_1 (fun (i : p) => f i)) (dite.{succ u1} M p _inst_3 (fun (h : p) => f h) (fun (h : Not p) => OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {p : Prop} [_inst_3 : Decidable p] (f : p -> M), Eq.{succ u1} M (finprod.{u1, 0} M p _inst_1 (fun (i : p) => f i)) (dite.{succ u1} M p _inst_3 (fun (h : p) => f h) (fun (h : Not p) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finprod_eq_dif finprod_eq_difₓ'. -/
@[to_additive]
theorem finprod_eq_dif {p : Prop} [Decidable p] (f : p → M) :
    (∏ᶠ i, f i) = if h : p then f h else 1 :=
  by
  split_ifs
  · haveI : Unique p := ⟨⟨h⟩, fun _ => rfl⟩
    exact finprod_unique f
  · haveI : IsEmpty p := ⟨h⟩
    exact finprod_of_isEmpty f
#align finprod_eq_dif finprod_eq_dif
#align finsum_eq_dif finsum_eq_dif

/- warning: finprod_eq_if -> finprod_eq_if is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {p : Prop} [_inst_3 : Decidable p] {x : M}, Eq.{succ u1} M (finprod.{u1, 0} M p _inst_1 (fun (i : p) => x)) (ite.{succ u1} M p _inst_3 x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {p : Prop} [_inst_3 : Decidable p] {x : M}, Eq.{succ u1} M (finprod.{u1, 0} M p _inst_1 (fun (i : p) => x)) (ite.{succ u1} M p _inst_3 x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finprod_eq_if finprod_eq_ifₓ'. -/
@[to_additive]
theorem finprod_eq_if {p : Prop} [Decidable p] {x : M} : (∏ᶠ i : p, x) = if p then x else 1 :=
  finprod_eq_dif fun _ => x
#align finprod_eq_if finprod_eq_if
#align finsum_eq_if finsum_eq_if

/- warning: finprod_congr -> finprod_congr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {g : α -> M}, (forall (x : α), Eq.{succ u1} M (f x) (g x)) -> (Eq.{succ u1} M (finprod.{u1, u2} M α _inst_1 f) (finprod.{u1, u2} M α _inst_1 g))
but is expected to have type
  forall {M : Type.{u2}} {α : Sort.{u1}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {g : α -> M}, (forall (x : α), Eq.{succ u2} M (f x) (g x)) -> (Eq.{succ u2} M (finprod.{u2, u1} M α _inst_1 f) (finprod.{u2, u1} M α _inst_1 g))
Case conversion may be inaccurate. Consider using '#align finprod_congr finprod_congrₓ'. -/
@[to_additive]
theorem finprod_congr {f g : α → M} (h : ∀ x, f x = g x) : finprod f = finprod g :=
  congr_arg _ <| funext h
#align finprod_congr finprod_congr
#align finsum_congr finsum_congr

#print finprod_congr_Prop /-
@[congr, to_additive]
theorem finprod_congr_Prop {p q : Prop} {f : p → M} {g : q → M} (hpq : p = q)
    (hfg : ∀ h : q, f (hpq.mpr h) = g h) : finprod f = finprod g :=
  by
  subst q
  exact finprod_congr hfg
#align finprod_congr_Prop finprod_congr_Prop
#align finsum_congr_Prop finsum_congr_Prop
-/

attribute [congr] finsum_congr_Prop

/- warning: finprod_induction -> finprod_induction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Sort.{u2}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} (p : M -> Prop), (p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) x y))) -> (forall (i : α), p (f i)) -> (p (finprod.{u1, u2} M α _inst_1 (fun (i : α) => f i)))
but is expected to have type
  forall {M : Type.{u2}} {α : Sort.{u1}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} (p : M -> Prop), (p (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y))) -> (forall (i : α), p (f i)) -> (p (finprod.{u2, u1} M α _inst_1 (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_induction finprod_inductionₓ'. -/
/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on the factors. -/
@[to_additive
      "To prove a property of a finite sum, it suffices to prove that the property is\nadditive and holds on the summands."]
theorem finprod_induction {f : α → M} (p : M → Prop) (hp₀ : p 1)
    (hp₁ : ∀ x y, p x → p y → p (x * y)) (hp₂ : ∀ i, p (f i)) : p (∏ᶠ i, f i) :=
  by
  rw [finprod]
  split_ifs
  exacts[Finset.prod_induction _ _ hp₁ hp₀ fun i hi => hp₂ _, hp₀]
#align finprod_induction finprod_induction
#align finsum_induction finsum_induction

/- warning: finprod_nonneg -> finprod_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {R : Type.{u2}} [_inst_3 : OrderedCommSemiring.{u2} R] {f : α -> R}, (forall (x : α), LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3))))))))) (f x)) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3))))))))) (finprod.{u2, u1} R α (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3)) (fun (x : α) => f x)))
but is expected to have type
  forall {α : Sort.{u1}} {R : Type.{u2}} [_inst_3 : OrderedCommSemiring.{u2} R] {f : α -> R}, (forall (x : α), LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedSemiring.toPartialOrder.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3))))) (f x)) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedSemiring.toPartialOrder.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3))))) (finprod.{u2, u1} R α (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3)) (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finprod_nonneg finprod_nonnegₓ'. -/
theorem finprod_nonneg {R : Type _} [OrderedCommSemiring R] {f : α → R} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∏ᶠ x, f x :=
  finprod_induction (fun x => 0 ≤ x) zero_le_one (fun x y => mul_nonneg) hf
#align finprod_nonneg finprod_nonneg

/- warning: one_le_finprod' -> one_le_finprod' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {M : Type.{u2}} [_inst_3 : OrderedCommMonoid.{u2} M] {f : α -> M}, (forall (i : α), LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M _inst_3))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3))))))) (f i)) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M _inst_3))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3))))))) (finprod.{u2, u1} M α (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3) (fun (i : α) => f i)))
but is expected to have type
  forall {α : Sort.{u1}} {M : Type.{u2}} [_inst_3 : OrderedCommMonoid.{u2} M] {f : α -> M}, (forall (i : α), LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M _inst_3))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3))))) (f i)) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M _inst_3))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3))))) (finprod.{u2, u1} M α (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3) (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align one_le_finprod' one_le_finprod'ₓ'. -/
@[to_additive finsum_nonneg]
theorem one_le_finprod' {M : Type _} [OrderedCommMonoid M] {f : α → M} (hf : ∀ i, 1 ≤ f i) :
    1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ => one_le_mul) hf
#align one_le_finprod' one_le_finprod'
#align finsum_nonneg finsum_nonneg

/- warning: monoid_hom.map_finprod_plift -> MonoidHom.map_finprod_pLift is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Sort.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : CommMonoid.{u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (g : α -> M), (Set.Finite.{u3} (PLift.{u3} α) (Function.mulSupport.{u3, u1} (PLift.{u3} α) M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Function.comp.{succ u3, u3, succ u1} (PLift.{u3} α) α M g (PLift.down.{u3} α)))) -> (Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) f (finprod.{u1, u3} M α _inst_1 (fun (x : α) => g x))) (finprod.{u2, u3} N α _inst_2 (fun (x : α) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) f (g x))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {α : Sort.{u1}} [_inst_1 : CommMonoid.{u3} M] [_inst_2 : CommMonoid.{u2} N] (f : MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (g : α -> M), (Set.Finite.{u1} (PLift.{u1} α) (Function.mulSupport.{u1, u3} (PLift.{u1} α) M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Function.comp.{succ u1, u1, succ u3} (PLift.{u1} α) α M g (PLift.down.{u1} α)))) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u3, u1} M α _inst_1 (fun (x : α) => g x))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) f (finprod.{u3, u1} M α _inst_1 (fun (x : α) => g x))) (finprod.{u2, u1} N α _inst_2 (fun (x : α) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) f (g x))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_finprod_plift MonoidHom.map_finprod_pLiftₓ'. -/
@[to_additive]
theorem MonoidHom.map_finprod_pLift (f : M →* N) (g : α → M)
    (h : (mulSupport <| g ∘ PLift.down).Finite) : f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) :=
  by
  rw [finprod_eq_prod_pLift_of_mulSupport_subset h.coe_to_finset.ge,
    finprod_eq_prod_pLift_of_mulSupport_subset, f.map_prod]
  rw [h.coe_to_finset]
  exact mul_support_comp_subset f.map_one (g ∘ PLift.down)
#align monoid_hom.map_finprod_plift MonoidHom.map_finprod_pLift
#align add_monoid_hom.map_finsum_plift AddMonoidHom.map_finsum_pLift

/- warning: monoid_hom.map_finprod_Prop -> MonoidHom.map_finprod_Prop is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : CommMonoid.{u2} N] {p : Prop} (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (g : p -> M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) f (finprod.{u1, 0} M p _inst_1 (fun (x : p) => g x))) (finprod.{u2, 0} N p _inst_2 (fun (x : p) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) f (g x)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : CommMonoid.{u1} N] {p : Prop} (f : MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) (g : p -> M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u2, 0} M p _inst_1 (fun (x : p) => g x))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))))) f (finprod.{u2, 0} M p _inst_1 (fun (x : p) => g x))) (finprod.{u1, 0} N p _inst_2 (fun (x : p) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))))) f (g x)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_finprod_Prop MonoidHom.map_finprod_Propₓ'. -/
@[to_additive]
theorem MonoidHom.map_finprod_Prop {p : Prop} (f : M →* N) (g : p → M) :
    f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) :=
  f.map_finprod_pLift g (Set.toFinite _)
#align monoid_hom.map_finprod_Prop MonoidHom.map_finprod_Prop
#align add_monoid_hom.map_finsum_Prop AddMonoidHom.map_finsum_Prop

/- warning: monoid_hom.map_finprod_of_preimage_one -> MonoidHom.map_finprod_of_preimage_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Sort.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : CommMonoid.{u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))), (forall (x : M), (Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) f x) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))))) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))))) -> (forall (g : α -> M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) f (finprod.{u1, u3} M α _inst_1 (fun (i : α) => g i))) (finprod.{u2, u3} N α _inst_2 (fun (i : α) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) f (g i))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {α : Sort.{u1}} [_inst_1 : CommMonoid.{u3} M] [_inst_2 : CommMonoid.{u2} N] (f : MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))), (forall (x : M), (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) f x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (Monoid.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (CommMonoid.toMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) _inst_2))))) -> (Eq.{succ u3} M x (OfNat.ofNat.{u3} M 1 (One.toOfNat1.{u3} M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)))))) -> (forall (g : α -> M), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u3, u1} M α _inst_1 (fun (i : α) => g i))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) f (finprod.{u3, u1} M α _inst_1 (fun (i : α) => g i))) (finprod.{u2, u1} N α _inst_2 (fun (i : α) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) f (g i))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_finprod_of_preimage_one MonoidHom.map_finprod_of_preimage_oneₓ'. -/
@[to_additive]
theorem MonoidHom.map_finprod_of_preimage_one (f : M →* N) (hf : ∀ x, f x = 1 → x = 1) (g : α → M) :
    f (∏ᶠ i, g i) = ∏ᶠ i, f (g i) :=
  by
  by_cases hg : (mul_support <| g ∘ PLift.down).Finite; · exact f.map_finprod_plift g hg
  rw [finprod, dif_neg, f.map_one, finprod, dif_neg]
  exacts[infinite.mono (fun x hx => mt (hf (g x.down)) hx) hg, hg]
#align monoid_hom.map_finprod_of_preimage_one MonoidHom.map_finprod_of_preimage_one
#align add_monoid_hom.map_finsum_of_preimage_zero AddMonoidHom.map_finsum_of_preimage_zero

/- warning: monoid_hom.map_finprod_of_injective -> MonoidHom.map_finprod_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Sort.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : CommMonoid.{u2} N] (g : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))), (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) g)) -> (forall (f : α -> M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) g (finprod.{u1, u3} M α _inst_1 (fun (i : α) => f i))) (finprod.{u2, u3} N α _inst_2 (fun (i : α) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) g (f i))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {α : Sort.{u1}} [_inst_1 : CommMonoid.{u3} M] [_inst_2 : CommMonoid.{u2} N] (g : MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))), (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g)) -> (forall (f : α -> M), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u3, u1} M α _inst_1 (fun (i : α) => f i))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g (finprod.{u3, u1} M α _inst_1 (fun (i : α) => f i))) (finprod.{u2, u1} N α _inst_2 (fun (i : α) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g (f i))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_finprod_of_injective MonoidHom.map_finprod_of_injectiveₓ'. -/
@[to_additive]
theorem MonoidHom.map_finprod_of_injective (g : M →* N) (hg : Injective g) (f : α → M) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_of_preimage_one (fun x => (hg.eq_iff' g.map_one).mp) f
#align monoid_hom.map_finprod_of_injective MonoidHom.map_finprod_of_injective
#align add_monoid_hom.map_finsum_of_injective AddMonoidHom.map_finsum_of_injective

/- warning: mul_equiv.map_finprod -> MulEquiv.map_finprod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Sort.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : CommMonoid.{u2} N] (g : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) (f : α -> M), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) g (finprod.{u1, u3} M α _inst_1 (fun (i : α) => f i))) (finprod.{u2, u3} N α _inst_2 (fun (i : α) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) g (f i)))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {α : Sort.{u1}} [_inst_1 : CommMonoid.{u3} M] [_inst_2 : CommMonoid.{u2} N] (g : MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) (f : α -> M), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u3, u1} M α _inst_1 (fun (i : α) => f i))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MulEquivClass.instMonoidHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))))) g (finprod.{u3, u1} M α _inst_1 (fun (i : α) => f i))) (finprod.{u2, u1} N α _inst_2 (fun (i : α) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MulEquivClass.instMonoidHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))))) g (f i)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_finprod MulEquiv.map_finprodₓ'. -/
@[to_additive]
theorem MulEquiv.map_finprod (g : M ≃* N) (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.toMonoidHom.map_finprod_of_injective g.Injective f
#align mul_equiv.map_finprod MulEquiv.map_finprod
#align add_equiv.map_finsum AddEquiv.map_finsum

/- warning: finsum_smul -> finsum_smul is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_3 : Ring.{u2} R] [_inst_4 : AddCommGroup.{u3} M] [_inst_5 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_3) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)] [_inst_6 : NoZeroSMulDivisors.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_3))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (SubNegMonoid.toAddMonoid.{u3} M (AddGroup.toSubNegMonoid.{u3} M (AddCommGroup.toAddGroup.{u3} M _inst_4))))) (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_3) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) _inst_5))))] (f : ι -> R) (x : M), Eq.{succ u3} M (SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_3) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) _inst_5)))) (finsum.{u2, u1} R ι (AddCommGroup.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_3)))) (fun (i : ι) => f i)) x) (finsum.{u3, u1} M ι (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) (fun (i : ι) => SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_3) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) _inst_5)))) (f i) x))
but is expected to have type
  forall {ι : Sort.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_3 : Ring.{u3} R] [_inst_4 : AddCommGroup.{u2} M] [_inst_5 : Module.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4)] [_inst_6 : NoZeroSMulDivisors.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (SMulZeroClass.toSMul.{u3, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (Module.toMulActionWithZero.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) _inst_5))))] (f : ι -> R) (x : M), Eq.{succ u2} M (HSMul.hSMul.{u3, u2, u2} R M M (instHSMul.{u3, u2} R M (SMulZeroClass.toSMul.{u3, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (Module.toMulActionWithZero.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) _inst_5))))) (finsum.{u3, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R _inst_3)))) (fun (i : ι) => f i)) x) (finsum.{u2, u1} M ι (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) (fun (i : ι) => HSMul.hSMul.{u3, u2, u2} R M M (instHSMul.{u3, u2} R M (SMulZeroClass.toSMul.{u3, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (Module.toMulActionWithZero.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) _inst_5))))) (f i) x))
Case conversion may be inaccurate. Consider using '#align finsum_smul finsum_smulₓ'. -/
theorem finsum_smul {R M : Type _} [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    (f : ι → R) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x :=
  by
  rcases eq_or_ne x 0 with (rfl | hx); · simp
  exact ((smulAddHom R M).flip x).map_finsum_of_injective (smul_left_injective R hx) _
#align finsum_smul finsum_smul

/- warning: smul_finsum -> smul_finsum is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_3 : Ring.{u2} R] [_inst_4 : AddCommGroup.{u3} M] [_inst_5 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_3) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)] [_inst_6 : NoZeroSMulDivisors.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_3))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (SubNegMonoid.toAddMonoid.{u3} M (AddGroup.toSubNegMonoid.{u3} M (AddCommGroup.toAddGroup.{u3} M _inst_4))))) (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_3) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) _inst_5))))] (c : R) (f : ι -> M), Eq.{succ u3} M (SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_3) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) _inst_5)))) c (finsum.{u3, u1} M ι (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) (fun (i : ι) => f i))) (finsum.{u3, u1} M ι (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) (fun (i : ι) => SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_3)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_3) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) _inst_5)))) c (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_3 : Ring.{u3} R] [_inst_4 : AddCommGroup.{u2} M] [_inst_5 : Module.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4)] [_inst_6 : NoZeroSMulDivisors.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (SMulZeroClass.toSMul.{u3, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (Module.toMulActionWithZero.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) _inst_5))))] (c : R) (f : ι -> M), Eq.{succ u2} M (HSMul.hSMul.{u3, u2, u2} R M M (instHSMul.{u3, u2} R M (SMulZeroClass.toSMul.{u3, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (Module.toMulActionWithZero.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) _inst_5))))) c (finsum.{u2, u1} M ι (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) (fun (i : ι) => f i))) (finsum.{u2, u1} M ι (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) (fun (i : ι) => HSMul.hSMul.{u3, u2, u2} R M M (instHSMul.{u3, u2} R M (SMulZeroClass.toSMul.{u3, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3))) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_3)) (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (Module.toMulActionWithZero.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) _inst_5))))) c (f i)))
Case conversion may be inaccurate. Consider using '#align smul_finsum smul_finsumₓ'. -/
theorem smul_finsum {R M : Type _} [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    (c : R) (f : ι → M) : (c • ∑ᶠ i, f i) = ∑ᶠ i, c • f i :=
  by
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  exact (smulAddHom R M c).map_finsum_of_injective (smul_right_injective M hc) _
#align smul_finsum smul_finsum

/- warning: finprod_inv_distrib -> finprod_inv_distrib is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Sort.{u2}} [_inst_3 : DivisionCommMonoid.{u1} G] (f : α -> G), Eq.{succ u1} G (finprod.{u1, u2} G α (DivisionCommMonoid.toCommMonoid.{u1} G _inst_3) (fun (x : α) => Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_3))) (f x))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_3))) (finprod.{u1, u2} G α (DivisionCommMonoid.toCommMonoid.{u1} G _inst_3) (fun (x : α) => f x)))
but is expected to have type
  forall {G : Type.{u2}} {α : Sort.{u1}} [_inst_3 : DivisionCommMonoid.{u2} G] (f : α -> G), Eq.{succ u2} G (finprod.{u2, u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (x : α) => Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (f x))) (Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (finprod.{u2, u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finprod_inv_distrib finprod_inv_distribₓ'. -/
@[to_additive]
theorem finprod_inv_distrib [DivisionCommMonoid G] (f : α → G) : (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod f).symm
#align finprod_inv_distrib finprod_inv_distrib
#align finsum_neg_distrib finsum_neg_distrib

end Sort

section Type

variable {α β ι G M N : Type _} [CommMonoid M] [CommMonoid N]

open BigOperators

/- warning: finprod_eq_mul_indicator_apply -> finprod_eq_mulIndicator_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (s : Set.{u1} α) (f : α -> M) (a : α), Eq.{succ u2} M (finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) _inst_1 (fun (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) s f a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (s : Set.{u2} α) (f : α -> M) (a : α), Eq.{succ u1} M (finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) _inst_1 (fun (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => f a)) (Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) s f a)
Case conversion may be inaccurate. Consider using '#align finprod_eq_mul_indicator_apply finprod_eq_mulIndicator_applyₓ'. -/
@[to_additive]
theorem finprod_eq_mulIndicator_apply (s : Set α) (f : α → M) (a : α) :
    (∏ᶠ h : a ∈ s, f a) = mulIndicator s f a := by convert finprod_eq_if
#align finprod_eq_mul_indicator_apply finprod_eq_mulIndicator_apply
#align finsum_eq_indicator_apply finsum_eq_indicator_apply

/- warning: finprod_mem_mul_support -> finprod_mem_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (a : α), Eq.{succ u2} M (finprod.{u2, 0} M (Ne.{succ u2} M (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) _inst_1 (fun (h : Ne.{succ u2} M (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) => f a)) (f a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (a : α), Eq.{succ u1} M (finprod.{u1, 0} M (Ne.{succ u1} M (f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))) _inst_1 (fun (h : Ne.{succ u1} M (f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))) => f a)) (f a)
Case conversion may be inaccurate. Consider using '#align finprod_mem_mul_support finprod_mem_mulSupportₓ'. -/
@[simp, to_additive]
theorem finprod_mem_mulSupport (f : α → M) (a : α) : (∏ᶠ h : f a ≠ 1, f a) = f a := by
  rw [← mem_mul_support, finprod_eq_mulIndicator_apply, mul_indicator_mul_support]
#align finprod_mem_mul_support finprod_mem_mulSupport
#align finsum_mem_support finsum_mem_support

/- warning: finprod_mem_def -> finprod_mem_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (s : Set.{u1} α) (f : α -> M), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (a : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))) (finprod.{u2, succ u1} M α _inst_1 (fun (a : α) => Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) s f a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (s : Set.{u2} α) (f : α -> M), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => f a))) (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) s f a))
Case conversion may be inaccurate. Consider using '#align finprod_mem_def finprod_mem_defₓ'. -/
@[to_additive]
theorem finprod_mem_def (s : Set α) (f : α → M) : (∏ᶠ a ∈ s, f a) = ∏ᶠ a, mulIndicator s f a :=
  finprod_congr <| finprod_eq_mulIndicator_apply s f
#align finprod_mem_def finprod_mem_def
#align finsum_mem_def finsum_mem_def

/- warning: finprod_eq_prod_of_mul_support_subset -> finprod_eq_prod_of_mulSupport_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) {s : Finset.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u2, u1} M α _inst_1 s (fun (i : α) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) {s : Finset.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f) (Finset.toSet.{u2} α s)) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M α _inst_1 s (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_eq_prod_of_mul_support_subset finprod_eq_prod_of_mulSupport_subsetₓ'. -/
@[to_additive]
theorem finprod_eq_prod_of_mulSupport_subset (f : α → M) {s : Finset α} (h : mulSupport f ⊆ s) :
    (∏ᶠ i, f i) = ∏ i in s, f i :=
  by
  have A : mul_support (f ∘ PLift.down) = equiv.plift.symm '' mul_support f :=
    by
    rw [mul_support_comp_eq_preimage]
    exact (equiv.plift.symm.image_eq_preimage _).symm
  have : mul_support (f ∘ PLift.down) ⊆ s.map equiv.plift.symm.to_embedding :=
    by
    rw [A, Finset.coe_map]
    exact image_subset _ h
  rw [finprod_eq_prod_pLift_of_mulSupport_subset this]
  simp
#align finprod_eq_prod_of_mul_support_subset finprod_eq_prod_of_mulSupport_subset
#align finsum_eq_sum_of_support_subset finsum_eq_sum_of_support_subset

/- warning: finprod_eq_prod_of_mul_support_to_finset_subset -> finprod_eq_prod_of_mulSupport_toFinset_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (hf : Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) {s : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Set.Finite.toFinset.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f) hf) s) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u2, u1} M α _inst_1 s (fun (i : α) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (hf : Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) {s : Finset.{u2} α}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Set.Finite.toFinset.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f) hf) s) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M α _inst_1 s (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_eq_prod_of_mul_support_to_finset_subset finprod_eq_prod_of_mulSupport_toFinset_subsetₓ'. -/
@[to_additive]
theorem finprod_eq_prod_of_mulSupport_toFinset_subset (f : α → M) (hf : (mulSupport f).Finite)
    {s : Finset α} (h : hf.toFinset ⊆ s) : (∏ᶠ i, f i) = ∏ i in s, f i :=
  finprod_eq_prod_of_mulSupport_subset _ fun x hx => h <| hf.mem_toFinset.2 hx
#align finprod_eq_prod_of_mul_support_to_finset_subset finprod_eq_prod_of_mulSupport_toFinset_subset
#align finsum_eq_sum_of_support_to_finset_subset finsum_eq_sum_of_support_toFinset_subset

/- warning: finprod_eq_finset_prod_of_mul_support_subset -> finprod_eq_finset_prod_of_mulSupport_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) {s : Finset.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u2, u1} M α _inst_1 s (fun (i : α) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) {s : Finset.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f) (Finset.toSet.{u2} α s)) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M α _inst_1 s (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_eq_finset_prod_of_mul_support_subset finprod_eq_finset_prod_of_mulSupport_subsetₓ'. -/
@[to_additive]
theorem finprod_eq_finset_prod_of_mulSupport_subset (f : α → M) {s : Finset α}
    (h : mulSupport f ⊆ (s : Set α)) : (∏ᶠ i, f i) = ∏ i in s, f i :=
  haveI h' : (s.finite_to_set.subset h).toFinset ⊆ s := by
    simpa [← Finset.coe_subset, Set.coe_toFinset]
  finprod_eq_prod_of_mulSupport_toFinset_subset _ _ h'
#align finprod_eq_finset_prod_of_mul_support_subset finprod_eq_finset_prod_of_mulSupport_subset
#align finsum_eq_finset_sum_of_support_subset finsum_eq_finset_sum_of_support_subset

/- warning: finprod_def -> finprod_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) [_inst_3 : Decidable (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))], Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (dite.{succ u2} M (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) _inst_3 (fun (h : Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) => Finset.prod.{u2, u1} M α _inst_1 (Set.Finite.toFinset.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f) h) (fun (i : α) => f i)) (fun (h : Not (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) => OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) [_inst_3 : Decidable (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))], Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) (dite.{succ u1} M (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) _inst_3 (fun (h : Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) => Finset.prod.{u1, u2} M α _inst_1 (Set.Finite.toFinset.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f) h) (fun (i : α) => f i)) (fun (h : Not (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finprod_def finprod_defₓ'. -/
@[to_additive]
theorem finprod_def (f : α → M) [Decidable (mulSupport f).Finite] :
    (∏ᶠ i : α, f i) = if h : (mulSupport f).Finite then ∏ i in h.toFinset, f i else 1 :=
  by
  split_ifs
  · exact finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.Subset.refl _)
  · rw [finprod, dif_neg]
    rw [mul_support_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage equiv.plift.surjective) h
#align finprod_def finprod_def
#align finsum_def finsum_def

/- warning: finprod_of_infinite_mul_support -> finprod_of_infinite_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M}, (Set.Infinite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M}, (Set.Infinite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finprod_of_infinite_mul_support finprod_of_infinite_mulSupportₓ'. -/
@[to_additive]
theorem finprod_of_infinite_mulSupport {f : α → M} (hf : (mulSupport f).Infinite) :
    (∏ᶠ i, f i) = 1 := by classical rw [finprod_def, dif_neg hf]
#align finprod_of_infinite_mul_support finprod_of_infinite_mulSupport
#align finsum_of_infinite_support finsum_of_infinite_support

/- warning: finprod_eq_prod -> finprod_eq_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (hf : Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u2, u1} M α _inst_1 (Set.Finite.toFinset.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f) hf) (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (hf : Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M α _inst_1 (Set.Finite.toFinset.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f) hf) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_eq_prod finprod_eq_prodₓ'. -/
@[to_additive]
theorem finprod_eq_prod (f : α → M) (hf : (mulSupport f).Finite) :
    (∏ᶠ i : α, f i) = ∏ i in hf.toFinset, f i := by classical rw [finprod_def, dif_pos hf]
#align finprod_eq_prod finprod_eq_prod
#align finsum_eq_sum finsum_eq_sum

/- warning: finprod_eq_prod_of_fintype -> finprod_eq_prod_of_fintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] [_inst_3 : Fintype.{u1} α] (f : α -> M), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u2, u1} M α _inst_1 (Finset.univ.{u1} α _inst_3) (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] [_inst_3 : Fintype.{u2} α] (f : α -> M), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) (Finset.prod.{u1, u2} M α _inst_1 (Finset.univ.{u2} α _inst_3) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_eq_prod_of_fintype finprod_eq_prod_of_fintypeₓ'. -/
@[to_additive]
theorem finprod_eq_prod_of_fintype [Fintype α] (f : α → M) : (∏ᶠ i : α, f i) = ∏ i, f i :=
  finprod_eq_prod_of_mulSupport_toFinset_subset _ (Set.toFinite _) <| Finset.subset_univ _
#align finprod_eq_prod_of_fintype finprod_eq_prod_of_fintype
#align finsum_eq_sum_of_fintype finsum_eq_sum_of_fintype

/- warning: finprod_cond_eq_prod_of_cond_iff -> finprod_cond_eq_prod_of_cond_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) {p : α -> Prop} {t : Finset.{u1} α}, (forall {x : α}, (Ne.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) -> (Iff (p x) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (p i) _inst_1 (fun (hi : p i) => f i))) (Finset.prod.{u2, u1} M α _inst_1 t (fun (i : α) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) {p : α -> Prop} {t : Finset.{u2} α}, (forall {x : α}, (Ne.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))) -> (Iff (p x) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (p i) _inst_1 (fun (hi : p i) => f i))) (Finset.prod.{u1, u2} M α _inst_1 t (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_cond_eq_prod_of_cond_iff finprod_cond_eq_prod_of_cond_iffₓ'. -/
@[to_additive]
theorem finprod_cond_eq_prod_of_cond_iff (f : α → M) {p : α → Prop} {t : Finset α}
    (h : ∀ {x}, f x ≠ 1 → (p x ↔ x ∈ t)) : (∏ᶠ (i) (hi : p i), f i) = ∏ i in t, f i :=
  by
  set s := { x | p x }
  have : mul_support (s.mul_indicator f) ⊆ t :=
    by
    rw [Set.mulSupport_mulIndicator]
    intro x hx
    exact (h hx.2).1 hx.1
  erw [finprod_mem_def, finprod_eq_prod_of_mulSupport_subset _ this]
  refine' Finset.prod_congr rfl fun x hx => mul_indicator_apply_eq_self.2 fun hxs => _
  contrapose! hxs
  exact (h hxs).2 hx
#align finprod_cond_eq_prod_of_cond_iff finprod_cond_eq_prod_of_cond_iff
#align finsum_cond_eq_sum_of_cond_iff finsum_cond_eq_sum_of_cond_iff

/- warning: finprod_cond_ne -> finprod_cond_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (a : α) [_inst_3 : DecidableEq.{succ u1} α] (hf : Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Ne.{succ u1} α i a) _inst_1 (fun (H : Ne.{succ u1} α i a) => f i))) (Finset.prod.{u2, u1} M α _inst_1 (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_3 a b) (Set.Finite.toFinset.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f) hf) a) (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (a : α) [_inst_3 : DecidableEq.{succ u2} α] (hf : Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Ne.{succ u2} α i a) _inst_1 (fun (H : Ne.{succ u2} α i a) => f i))) (Finset.prod.{u1, u2} M α _inst_1 (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_3 a b) (Set.Finite.toFinset.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f) hf) a) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_cond_ne finprod_cond_neₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (i «expr ≠ » a) -/
@[to_additive]
theorem finprod_cond_ne (f : α → M) (a : α) [DecidableEq α] (hf : (mulSupport f).Finite) :
    (∏ᶠ (i) (_ : i ≠ a), f i) = ∏ i in hf.toFinset.eraseₓ a, f i :=
  by
  apply finprod_cond_eq_prod_of_cond_iff
  intro x hx
  rw [Finset.mem_erase, finite.mem_to_finset, mem_mul_support]
  exact ⟨fun h => And.intro h hx, fun h => h.1⟩
#align finprod_cond_ne finprod_cond_ne
#align finsum_cond_ne finsum_cond_ne

/- warning: finprod_mem_eq_prod_of_inter_mul_support_eq -> finprod_mem_eq_prod_of_inter_mulSupport_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) {s : Set.{u1} α} {t : Finset.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (Finset.prod.{u2, u1} M α _inst_1 t (fun (i : α) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) {s : Set.{u2} α} {t : Finset.{u2} α}, (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Finset.toSet.{u2} α t) (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (Finset.prod.{u1, u2} M α _inst_1 t (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_prod_of_inter_mul_support_eq finprod_mem_eq_prod_of_inter_mulSupport_eqₓ'. -/
@[to_additive]
theorem finprod_mem_eq_prod_of_inter_mulSupport_eq (f : α → M) {s : Set α} {t : Finset α}
    (h : s ∩ mulSupport f = t ∩ mulSupport f) : (∏ᶠ i ∈ s, f i) = ∏ i in t, f i :=
  finprod_cond_eq_prod_of_cond_iff _ <| by simpa [Set.ext_iff] using h
#align finprod_mem_eq_prod_of_inter_mul_support_eq finprod_mem_eq_prod_of_inter_mulSupport_eq
#align finsum_mem_eq_sum_of_inter_support_eq finsum_mem_eq_sum_of_inter_support_eq

/- warning: finprod_mem_eq_prod_of_subset -> finprod_mem_eq_prod_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) {s : Set.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) s) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (Finset.prod.{u2, u1} M α _inst_1 t (fun (i : α) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) {s : Set.{u2} α} {t : Finset.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) (Finset.toSet.{u2} α t)) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α t) s) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (Finset.prod.{u1, u2} M α _inst_1 t (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_prod_of_subset finprod_mem_eq_prod_of_subsetₓ'. -/
@[to_additive]
theorem finprod_mem_eq_prod_of_subset (f : α → M) {s : Set α} {t : Finset α}
    (h₁ : s ∩ mulSupport f ⊆ t) (h₂ : ↑t ⊆ s) : (∏ᶠ i ∈ s, f i) = ∏ i in t, f i :=
  finprod_cond_eq_prod_of_cond_iff _ fun x hx => ⟨fun h => h₁ ⟨h, hx⟩, fun h => h₂ h⟩
#align finprod_mem_eq_prod_of_subset finprod_mem_eq_prod_of_subset
#align finsum_mem_eq_sum_of_subset finsum_mem_eq_sum_of_subset

/- warning: finprod_mem_eq_prod -> finprod_mem_eq_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) {s : Set.{u1} α} (hf : Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (Finset.prod.{u2, u1} M α _inst_1 (Set.Finite.toFinset.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) hf) (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) {s : Set.{u2} α} (hf : Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (Finset.prod.{u1, u2} M α _inst_1 (Set.Finite.toFinset.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) hf) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_prod finprod_mem_eq_prodₓ'. -/
@[to_additive]
theorem finprod_mem_eq_prod (f : α → M) {s : Set α} (hf : (s ∩ mulSupport f).Finite) :
    (∏ᶠ i ∈ s, f i) = ∏ i in hf.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by simp [inter_assoc]
#align finprod_mem_eq_prod finprod_mem_eq_prod
#align finsum_mem_eq_sum finsum_mem_eq_sum

/- warning: finprod_mem_eq_prod_filter -> finprod_mem_eq_prod_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (s : Set.{u1} α) [_inst_3 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)] (hf : Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (Finset.prod.{u2, u1} M α _inst_1 (Finset.filter.{u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s) (fun (a : α) => _inst_3 a) (Set.Finite.toFinset.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f) hf)) (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (s : Set.{u2} α) [_inst_3 : DecidablePred.{succ u2} α (fun (_x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) _x s)] (hf : Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (Finset.prod.{u1, u2} M α _inst_1 (Finset.filter.{u2} α (fun (_x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) _x s) (fun (a : α) => _inst_3 a) (Set.Finite.toFinset.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f) hf)) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_prod_filter finprod_mem_eq_prod_filterₓ'. -/
@[to_additive]
theorem finprod_mem_eq_prod_filter (f : α → M) (s : Set α) [DecidablePred (· ∈ s)]
    (hf : (mulSupport f).Finite) :
    (∏ᶠ i ∈ s, f i) = ∏ i in Finset.filter (· ∈ s) hf.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by simp [inter_comm, inter_left_comm]
#align finprod_mem_eq_prod_filter finprod_mem_eq_prod_filter
#align finsum_mem_eq_sum_filter finsum_mem_eq_sum_filter

/- warning: finprod_mem_eq_to_finset_prod -> finprod_mem_eq_toFinset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (s : Set.{u1} α) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (Finset.prod.{u2, u1} M α _inst_1 (Set.toFinset.{u1} α s _inst_3) (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (s : Set.{u2} α) [_inst_3 : Fintype.{u2} (Set.Elem.{u2} α s)], Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (Finset.prod.{u1, u2} M α _inst_1 (Set.toFinset.{u2} α s _inst_3) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_to_finset_prod finprod_mem_eq_toFinset_prodₓ'. -/
@[to_additive]
theorem finprod_mem_eq_toFinset_prod (f : α → M) (s : Set α) [Fintype s] :
    (∏ᶠ i ∈ s, f i) = ∏ i in s.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by rw [coe_to_finset]
#align finprod_mem_eq_to_finset_prod finprod_mem_eq_toFinset_prod
#align finsum_mem_eq_to_finset_sum finsum_mem_eq_toFinset_sum

/- warning: finprod_mem_eq_finite_to_finset_prod -> finprod_mem_eq_finite_toFinset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) {s : Set.{u1} α} (hs : Set.Finite.{u1} α s), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (Finset.prod.{u2, u1} M α _inst_1 (Set.Finite.toFinset.{u1} α s hs) (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) {s : Set.{u2} α} (hs : Set.Finite.{u2} α s), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (Finset.prod.{u1, u2} M α _inst_1 (Set.Finite.toFinset.{u2} α s hs) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_finite_to_finset_prod finprod_mem_eq_finite_toFinset_prodₓ'. -/
@[to_additive]
theorem finprod_mem_eq_finite_toFinset_prod (f : α → M) {s : Set α} (hs : s.Finite) :
    (∏ᶠ i ∈ s, f i) = ∏ i in hs.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by rw [hs.coe_to_finset]
#align finprod_mem_eq_finite_to_finset_prod finprod_mem_eq_finite_toFinset_prod
#align finsum_mem_eq_finite_to_finset_sum finsum_mem_eq_finite_toFinset_sum

/- warning: finprod_mem_finset_eq_prod -> finprod_mem_finset_eq_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (s : Finset.{u1} α), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) => f i))) (Finset.prod.{u2, u1} M α _inst_1 s (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (s : Finset.{u2} α), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) => f i))) (Finset.prod.{u1, u2} M α _inst_1 s (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_mem_finset_eq_prod finprod_mem_finset_eq_prodₓ'. -/
@[to_additive]
theorem finprod_mem_finset_eq_prod (f : α → M) (s : Finset α) : (∏ᶠ i ∈ s, f i) = ∏ i in s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl
#align finprod_mem_finset_eq_prod finprod_mem_finset_eq_prod
#align finsum_mem_finset_eq_sum finsum_mem_finset_eq_sum

/- warning: finprod_mem_coe_finset -> finprod_mem_coe_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (s : Finset.{u1} α), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => f i))) (Finset.prod.{u2, u1} M α _inst_1 s (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (s : Finset.{u2} α), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Finset.toSet.{u2} α s)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Finset.toSet.{u2} α s)) => f i))) (Finset.prod.{u1, u2} M α _inst_1 s (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finprod_mem_coe_finset finprod_mem_coe_finsetₓ'. -/
@[to_additive]
theorem finprod_mem_coe_finset (f : α → M) (s : Finset α) :
    (∏ᶠ i ∈ (s : Set α), f i) = ∏ i in s, f i :=
  finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl
#align finprod_mem_coe_finset finprod_mem_coe_finset
#align finsum_mem_coe_finset finsum_mem_coe_finset

/- warning: finprod_mem_eq_one_of_infinite -> finprod_mem_eq_one_of_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α}, (Set.Infinite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α}, (Set.Infinite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_one_of_infinite finprod_mem_eq_one_of_infiniteₓ'. -/
@[to_additive]
theorem finprod_mem_eq_one_of_infinite {f : α → M} {s : Set α} (hs : (s ∩ mulSupport f).Infinite) :
    (∏ᶠ i ∈ s, f i) = 1 := by
  rw [finprod_mem_def]
  apply finprod_of_infinite_mulSupport
  rwa [← mul_support_mul_indicator] at hs
#align finprod_mem_eq_one_of_infinite finprod_mem_eq_one_of_infinite
#align finsum_mem_eq_zero_of_infinite finsum_mem_eq_zero_of_infinite

/- warning: finprod_mem_eq_one_of_forall_eq_one -> finprod_mem_eq_one_of_forall_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α}, (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_one_of_forall_eq_one finprod_mem_eq_one_of_forall_eq_oneₓ'. -/
@[to_additive]
theorem finprod_mem_eq_one_of_forall_eq_one {f : α → M} {s : Set α} (h : ∀ x ∈ s, f x = 1) :
    (∏ᶠ i ∈ s, f i) = 1 := by simp (config := { contextual := true }) [h]
#align finprod_mem_eq_one_of_forall_eq_one finprod_mem_eq_one_of_forall_eq_one
#align finsum_mem_eq_zero_of_forall_eq_zero finsum_mem_eq_zero_of_forall_eq_zero

/- warning: finprod_mem_inter_mul_support -> finprod_mem_inter_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (s : Set.{u1} α), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (s : Set.{u2} α), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_mem_inter_mul_support finprod_mem_inter_mulSupportₓ'. -/
@[to_additive]
theorem finprod_mem_inter_mulSupport (f : α → M) (s : Set α) :
    (∏ᶠ i ∈ s ∩ mulSupport f, f i) = ∏ᶠ i ∈ s, f i := by
  rw [finprod_mem_def, finprod_mem_def, mul_indicator_inter_mul_support]
#align finprod_mem_inter_mul_support finprod_mem_inter_mulSupport
#align finsum_mem_inter_support finsum_mem_inter_support

/- warning: finprod_mem_inter_mul_support_eq -> finprod_mem_inter_mulSupport_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (s : Set.{u1} α) (t : Set.{u1} α), (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (s : Set.{u2} α) (t : Set.{u2} α), (Eq.{succ u2} (Set.{u2} α) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_inter_mul_support_eq finprod_mem_inter_mulSupport_eqₓ'. -/
@[to_additive]
theorem finprod_mem_inter_mulSupport_eq (f : α → M) (s t : Set α)
    (h : s ∩ mulSupport f = t ∩ mulSupport f) : (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport, h, finprod_mem_inter_mulSupport]
#align finprod_mem_inter_mul_support_eq finprod_mem_inter_mulSupport_eq
#align finsum_mem_inter_support_eq finsum_mem_inter_support_eq

/- warning: finprod_mem_inter_mul_support_eq' -> finprod_mem_inter_mulSupport_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (s : Set.{u1} α) (t : Set.{u1} α), (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) -> (Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (s : Set.{u2} α) (t : Set.{u2} α), (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) -> (Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_inter_mul_support_eq' finprod_mem_inter_mulSupport_eq'ₓ'. -/
@[to_additive]
theorem finprod_mem_inter_mulSupport_eq' (f : α → M) (s t : Set α)
    (h : ∀ x ∈ mulSupport f, x ∈ s ↔ x ∈ t) : (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ t, f i :=
  by
  apply finprod_mem_inter_mulSupport_eq
  ext x
  exact and_congr_left (h x)
#align finprod_mem_inter_mul_support_eq' finprod_mem_inter_mulSupport_eq'
#align finsum_mem_inter_support_eq' finsum_mem_inter_support_eq'

#print finprod_mem_univ /-
@[to_additive]
theorem finprod_mem_univ (f : α → M) : (∏ᶠ i ∈ @Set.univ α, f i) = ∏ᶠ i : α, f i :=
  finprod_congr fun i => finprod_true _
#align finprod_mem_univ finprod_mem_univ
#align finsum_mem_univ finsum_mem_univ
-/

variable {f g : α → M} {a b : α} {s t : Set α}

/- warning: finprod_mem_congr -> finprod_mem_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {g : α -> M} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) s t) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (Eq.{succ u2} M (f x) (g x))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => g i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {g : α -> M} {s : Set.{u2} α} {t : Set.{u2} α}, (Eq.{succ u2} (Set.{u2} α) s t) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) -> (Eq.{succ u1} M (f x) (g x))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => g i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_congr finprod_mem_congrₓ'. -/
@[to_additive]
theorem finprod_mem_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) :
    (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ t, g i :=
  h₀.symm ▸ finprod_congr fun i => finprod_congr_Prop rfl (h₁ i)
#align finprod_mem_congr finprod_mem_congr
#align finsum_mem_congr finsum_mem_congr

/- warning: finprod_eq_one_of_forall_eq_one -> finprod_eq_one_of_forall_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M}, (forall (x : α), Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M}, (forall (x : α), Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finprod_eq_one_of_forall_eq_one finprod_eq_one_of_forall_eq_oneₓ'. -/
@[to_additive]
theorem finprod_eq_one_of_forall_eq_one {f : α → M} (h : ∀ x, f x = 1) : (∏ᶠ i, f i) = 1 := by
  simp (config := { contextual := true }) [h]
#align finprod_eq_one_of_forall_eq_one finprod_eq_one_of_forall_eq_one
#align finsum_eq_zero_of_forall_eq_zero finsum_eq_zero_of_forall_eq_zero

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/


/- warning: finprod_mul_distrib -> finprod_mul_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {g : α -> M}, (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) -> (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) g)) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (f i) (g i))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => g i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {g : α -> M}, (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) -> (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) g)) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f i) (g i))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => g i))))
Case conversion may be inaccurate. Consider using '#align finprod_mul_distrib finprod_mul_distribₓ'. -/
/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i * g i` equals
the product of `f i` multiplied by the product of `g i`. -/
@[to_additive
      "If the additive supports of `f` and `g` are finite, then the sum of `f i + g i`\nequals the sum of `f i` plus the sum of `g i`."]
theorem finprod_mul_distrib (hf : (mulSupport f).Finite) (hg : (mulSupport g).Finite) :
    (∏ᶠ i, f i * g i) = (∏ᶠ i, f i) * ∏ᶠ i, g i := by
  classical
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_union_left _ _),
      finprod_eq_prod_of_mulSupport_toFinset_subset _ hg (Finset.subset_union_right _ _), ←
      Finset.prod_mul_distrib]
    refine' finprod_eq_prod_of_mulSupport_subset _ _
    simp [mul_support_mul]
#align finprod_mul_distrib finprod_mul_distrib
#align finsum_add_distrib finsum_add_distrib

/- warning: finprod_div_distrib -> finprod_div_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_3 : DivisionCommMonoid.{u2} G] {f : α -> G} {g : α -> G}, (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3))))) f)) -> (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3))))) g)) -> (Eq.{succ u2} G (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (f i) (g i))) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => f i)) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => g i))))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_3 : DivisionCommMonoid.{u2} G] {f : α -> G} {g : α -> G}, (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α G (InvOneClass.toOne.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) f)) -> (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α G (InvOneClass.toOne.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) g)) -> (Eq.{succ u2} G (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (f i) (g i))) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => f i)) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => g i))))
Case conversion may be inaccurate. Consider using '#align finprod_div_distrib finprod_div_distribₓ'. -/
/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i / g i`
equals the product of `f i` divided by the product of `g i`. -/
@[to_additive
      "If the additive supports of `f` and `g` are finite, then the sum of `f i - g i`\nequals the sum of `f i` minus the sum of `g i`."]
theorem finprod_div_distrib [DivisionCommMonoid G] {f g : α → G} (hf : (mulSupport f).Finite)
    (hg : (mulSupport g).Finite) : (∏ᶠ i, f i / g i) = (∏ᶠ i, f i) / ∏ᶠ i, g i := by
  simp only [div_eq_mul_inv, finprod_mul_distrib hf ((mul_support_inv g).symm.rec hg),
    finprod_inv_distrib]
#align finprod_div_distrib finprod_div_distrib
#align finsum_sub_distrib finsum_sub_distrib

/- warning: finprod_mem_mul_distrib' -> finprod_mem_mul_distrib' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {g : α -> M} {s : Set.{u1} α}, (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) g))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (f i) (g i)))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => g i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {g : α -> M} {s : Set.{u2} α}, (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) g))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f i) (g i)))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => g i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_mul_distrib' finprod_mem_mul_distrib'ₓ'. -/
/-- A more general version of `finprod_mem_mul_distrib` that only requires `s ∩ mul_support f` and
`s ∩ mul_support g` rather than `s` to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_add_distrib` that only requires `s ∩ support f`\nand `s ∩ support g` rather than `s` to be finite."]
theorem finprod_mem_mul_distrib' (hf : (s ∩ mulSupport f).Finite) (hg : (s ∩ mulSupport g).Finite) :
    (∏ᶠ i ∈ s, f i * g i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
  by
  rw [← mul_support_mul_indicator] at hf hg
  simp only [finprod_mem_def, mul_indicator_mul, finprod_mul_distrib hf hg]
#align finprod_mem_mul_distrib' finprod_mem_mul_distrib'
#align finsum_mem_add_distrib' finsum_mem_add_distrib'

/- warning: finprod_mem_one -> finprod_mem_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (s : Set.{u1} α), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (s : Set.{u2} α), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_one finprod_mem_oneₓ'. -/
/-- The product of the constant function `1` over any set equals `1`. -/
@[to_additive "The product of the constant function `0` over any set equals `0`."]
theorem finprod_mem_one (s : Set α) : (∏ᶠ i ∈ s, (1 : M)) = 1 := by simp
#align finprod_mem_one finprod_mem_one
#align finsum_mem_zero finsum_mem_zero

/- warning: finprod_mem_of_eq_on_one -> finprod_mem_of_eqOn_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α}, (Set.EqOn.{u1, u2} α M f (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) s) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α}, (Set.EqOn.{u2, u1} α M f (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Data.Set.Function._hyg.1349 : α) => M) (fun (i : α) => Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))) s) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_of_eq_on_one finprod_mem_of_eqOn_oneₓ'. -/
/-- If a function `f` equals `1` on a set `s`, then the product of `f i` over `i ∈ s` equals `1`. -/
@[to_additive
      "If a function `f` equals `0` on a set `s`, then the product of `f i` over `i ∈ s`\nequals `0`."]
theorem finprod_mem_of_eqOn_one (hf : s.EqOn f 1) : (∏ᶠ i ∈ s, f i) = 1 :=
  by
  rw [← finprod_mem_one s]
  exact finprod_mem_congr rfl hf
#align finprod_mem_of_eq_on_one finprod_mem_of_eqOn_one
#align finsum_mem_of_eq_on_zero finsum_mem_of_eqOn_zero

/- warning: exists_ne_one_of_finprod_mem_ne_one -> exists_ne_one_of_finprod_mem_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α}, (Ne.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Ne.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α}, (Ne.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => f i))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Ne.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align exists_ne_one_of_finprod_mem_ne_one exists_ne_one_of_finprod_mem_ne_oneₓ'. -/
/-- If the product of `f i` over `i ∈ s` is not equal to `1`, then there is some `x ∈ s` such that
`f x ≠ 1`. -/
@[to_additive
      "If the product of `f i` over `i ∈ s` is not equal to `0`, then there is some `x ∈ s`\nsuch that `f x ≠ 0`."]
theorem exists_ne_one_of_finprod_mem_ne_one (h : (∏ᶠ i ∈ s, f i) ≠ 1) : ∃ x ∈ s, f x ≠ 1 :=
  by
  by_contra' h'
  exact h (finprod_mem_of_eqOn_one h')
#align exists_ne_one_of_finprod_mem_ne_one exists_ne_one_of_finprod_mem_ne_one
#align exists_ne_zero_of_finsum_mem_ne_zero exists_ne_zero_of_finsum_mem_ne_zero

/- warning: finprod_mem_mul_distrib -> finprod_mem_mul_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {g : α -> M} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (f i) (g i)))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => g i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {g : α -> M} {s : Set.{u2} α}, (Set.Finite.{u2} α s) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f i) (g i)))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => g i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_mul_distrib finprod_mem_mul_distribₓ'. -/
/-- Given a finite set `s`, the product of `f i * g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` times the product of `g i` over `i ∈ s`. -/
@[to_additive
      "Given a finite set `s`, the sum of `f i + g i` over `i ∈ s` equals the sum of `f i`\nover `i ∈ s` plus the sum of `g i` over `i ∈ s`."]
theorem finprod_mem_mul_distrib (hs : s.Finite) :
    (∏ᶠ i ∈ s, f i * g i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
  finprod_mem_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)
#align finprod_mem_mul_distrib finprod_mem_mul_distrib
#align finsum_mem_add_distrib finsum_mem_add_distrib

/- warning: monoid_hom.map_finprod -> MonoidHom.map_finprod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : CommMonoid.{u3} N] {f : α -> M} (g : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))), (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) -> (Eq.{succ u3} N (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) (fun (_x : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) g (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i))) (finprod.{u3, succ u1} N α _inst_2 (fun (i : α) => coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) (fun (_x : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) g (f i))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : CommMonoid.{u3} M] [_inst_2 : CommMonoid.{u2} N] {f : α -> M} (g : MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))), (Set.Finite.{u1} α (Function.mulSupport.{u1, u3} α M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) f)) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => f i))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => f i))) (finprod.{u2, succ u1} N α _inst_2 (fun (i : α) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g (f i))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_finprod MonoidHom.map_finprodₓ'. -/
@[to_additive]
theorem MonoidHom.map_finprod {f : α → M} (g : M →* N) (hf : (mulSupport f).Finite) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_pLift f <| hf.Preimage <| Equiv.plift.Injective.InjOn _
#align monoid_hom.map_finprod MonoidHom.map_finprod
#align add_monoid_hom.map_finsum AddMonoidHom.map_finsum

/- warning: finprod_pow -> finprod_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M}, (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) -> (forall (n : Nat), Eq.{succ u2} M (HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)) n) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (f i) n)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M}, (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) -> (forall (n : Nat), Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)) n) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (f i) n)))
Case conversion may be inaccurate. Consider using '#align finprod_pow finprod_powₓ'. -/
@[to_additive]
theorem finprod_pow (hf : (mulSupport f).Finite) (n : ℕ) : (∏ᶠ i, f i) ^ n = ∏ᶠ i, f i ^ n :=
  (powMonoidHom n).map_finprod hf
#align finprod_pow finprod_pow
#align finsum_nsmul finsum_nsmul

/- warning: monoid_hom.map_finprod_mem' -> MonoidHom.map_finprod_mem' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : CommMonoid.{u3} N] {s : Set.{u1} α} {f : α -> M} (g : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))), (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u3} N (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) (fun (_x : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) g (finprod.{u2, succ u1} M α _inst_1 (fun (j : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s) => f j)))) (finprod.{u3, succ u1} N α _inst_2 (fun (i : α) => finprod.{u3, 0} N (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_2 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) (fun (_x : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) g (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : CommMonoid.{u3} M] [_inst_2 : CommMonoid.{u2} N] {s : Set.{u1} α} {f : α -> M} (g : MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))), (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Function.mulSupport.{u1, u3} α M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) f))) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u3, succ u1} M α _inst_1 (fun (j : α) => finprod.{u3, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s) _inst_1 (fun (h._@.Mathlib.Algebra.BigOperators.Finprod._hyg.7270 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s) => f j)))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g (finprod.{u3, succ u1} M α _inst_1 (fun (j : α) => finprod.{u3, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s) => f j)))) (finprod.{u2, succ u1} N α _inst_2 (fun (i : α) => finprod.{u2, 0} N (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_2 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g (f i)))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_finprod_mem' MonoidHom.map_finprod_mem'ₓ'. -/
/-- A more general version of `monoid_hom.map_finprod_mem` that requires `s ∩ mul_support f` rather
than `s` to be finite. -/
@[to_additive
      "A more general version of `add_monoid_hom.map_finsum_mem` that requires\n`s ∩ support f` rather than `s` to be finite."]
theorem MonoidHom.map_finprod_mem' {f : α → M} (g : M →* N) (h₀ : (s ∩ mulSupport f).Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) :=
  by
  rw [g.map_finprod]
  · simp only [g.map_finprod_Prop]
  · simpa only [finprod_eq_mulIndicator_apply, mul_support_mul_indicator]
#align monoid_hom.map_finprod_mem' MonoidHom.map_finprod_mem'
#align add_monoid_hom.map_finsum_mem' AddMonoidHom.map_finsum_mem'

/- warning: monoid_hom.map_finprod_mem -> MonoidHom.map_finprod_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : CommMonoid.{u3} N] {s : Set.{u1} α} (f : α -> M) (g : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))), (Set.Finite.{u1} α s) -> (Eq.{succ u3} N (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) (fun (_x : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) g (finprod.{u2, succ u1} M α _inst_1 (fun (j : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s) => f j)))) (finprod.{u3, succ u1} N α _inst_2 (fun (i : α) => finprod.{u3, 0} N (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_2 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) (fun (_x : MonoidHom.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u2, u3} M N (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2))) g (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : CommMonoid.{u3} M] [_inst_2 : CommMonoid.{u2} N] {s : Set.{u1} α} (f : α -> M) (g : MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))), (Set.Finite.{u1} α s) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u3, succ u1} M α _inst_1 (fun (j : α) => finprod.{u3, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s) _inst_1 (fun (h._@.Mathlib.Algebra.BigOperators.Finprod._hyg.7415 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s) => f j)))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g (finprod.{u3, succ u1} M α _inst_1 (fun (j : α) => finprod.{u3, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) j s) => f j)))) (finprod.{u2, succ u1} N α _inst_2 (fun (i : α) => finprod.{u2, 0} N (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_2 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MonoidHom.monoidHomClass.{u3, u2} M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))) g (f i)))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_finprod_mem MonoidHom.map_finprod_memₓ'. -/
/-- Given a monoid homomorphism `g : M →* N` and a function `f : α → M`, the value of `g` at the
product of `f i` over `i ∈ s` equals the product of `g (f i)` over `s`. -/
@[to_additive
      "Given an additive monoid homomorphism `g : M →* N` and a function `f : α → M`, the\nvalue of `g` at the sum of `f i` over `i ∈ s` equals the sum of `g (f i)` over `s`."]
theorem MonoidHom.map_finprod_mem (f : α → M) (g : M →* N) (hs : s.Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) :=
  g.map_finprod_mem' (hs.inter_of_left _)
#align monoid_hom.map_finprod_mem MonoidHom.map_finprod_mem
#align add_monoid_hom.map_finsum_mem AddMonoidHom.map_finsum_mem

/- warning: mul_equiv.map_finprod_mem -> MulEquiv.map_finprod_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : CommMonoid.{u3} N] (g : MulEquiv.{u2, u3} M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2)))) (f : α -> M) {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Eq.{succ u3} N (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulEquiv.{u2, u3} M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2)))) (fun (_x : MulEquiv.{u2, u3} M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2)))) => M -> N) (MulEquiv.hasCoeToFun.{u2, u3} M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2)))) g (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i)))) (finprod.{u3, succ u1} N α _inst_2 (fun (i : α) => finprod.{u3, 0} N (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_2 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulEquiv.{u2, u3} M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2)))) (fun (_x : MulEquiv.{u2, u3} M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2)))) => M -> N) (MulEquiv.hasCoeToFun.{u2, u3} M N (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N _inst_2)))) g (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : CommMonoid.{u3} M] [_inst_2 : CommMonoid.{u2} N] (g : MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) (f : α -> M) {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_1 (fun (h._@.Mathlib.Algebra.BigOperators.Finprod._hyg.7528 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => f i)))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MulEquivClass.instMonoidHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))))) g (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => f i)))) (finprod.{u2, succ u1} N α _inst_2 (fun (i : α) => finprod.{u2, 0} N (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_2 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MulEquivClass.instMonoidHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)))) M N (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)) (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))))))) g (f i)))))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_finprod_mem MulEquiv.map_finprod_memₓ'. -/
@[to_additive]
theorem MulEquiv.map_finprod_mem (g : M ≃* N) (f : α → M) {s : Set α} (hs : s.Finite) :
    g (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ s, g (f i) :=
  g.toMonoidHom.map_finprod_mem f hs
#align mul_equiv.map_finprod_mem MulEquiv.map_finprod_mem
#align add_equiv.map_finsum_mem AddEquiv.map_finsum_mem

/- warning: finprod_mem_inv_distrib -> finprod_mem_inv_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} {s : Set.{u1} α} [_inst_3 : DivisionCommMonoid.{u2} G] (f : α -> G), (Set.Finite.{u1} α s) -> (Eq.{succ u2} G (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (x : α) => finprod.{u2, 0} G (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3))) (f x)))) (Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3))) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (x : α) => finprod.{u2, 0} G (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => f x)))))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} {s : Set.{u1} α} [_inst_3 : DivisionCommMonoid.{u2} G] (f : α -> G), (Set.Finite.{u1} α s) -> (Eq.{succ u2} G (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (x : α) => finprod.{u2, 0} G (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (f x)))) (Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (x : α) => finprod.{u2, 0} G (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => f x)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_inv_distrib finprod_mem_inv_distribₓ'. -/
@[to_additive]
theorem finprod_mem_inv_distrib [DivisionCommMonoid G] (f : α → G) (hs : s.Finite) :
    (∏ᶠ x ∈ s, (f x)⁻¹) = (∏ᶠ x ∈ s, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod_mem f hs).symm
#align finprod_mem_inv_distrib finprod_mem_inv_distrib
#align finsum_mem_neg_distrib finsum_mem_neg_distrib

/- warning: finprod_mem_div_distrib -> finprod_mem_div_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} {s : Set.{u1} α} [_inst_3 : DivisionCommMonoid.{u2} G] (f : α -> G) (g : α -> G), (Set.Finite.{u1} α s) -> (Eq.{succ u2} G (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => finprod.{u2, 0} G (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (f i) (g i)))) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => finprod.{u2, 0} G (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => finprod.{u2, 0} G (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => g i)))))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} {s : Set.{u1} α} [_inst_3 : DivisionCommMonoid.{u2} G] (f : α -> G) (g : α -> G), (Set.Finite.{u1} α s) -> (Eq.{succ u2} G (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => finprod.{u2, 0} G (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (f i) (g i)))) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (DivisionMonoid.toDivInvMonoid.{u2} G (DivisionCommMonoid.toDivisionMonoid.{u2} G _inst_3)))) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => finprod.{u2, 0} G (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => f i))) (finprod.{u2, succ u1} G α (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (i : α) => finprod.{u2, 0} G (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) (DivisionCommMonoid.toCommMonoid.{u2} G _inst_3) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => g i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_div_distrib finprod_mem_div_distribₓ'. -/
/-- Given a finite set `s`, the product of `f i / g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` divided by the product of `g i` over `i ∈ s`. -/
@[to_additive
      "Given a finite set `s`, the sum of `f i / g i` over `i ∈ s` equals the sum of `f i`\nover `i ∈ s` minus the sum of `g i` over `i ∈ s`."]
theorem finprod_mem_div_distrib [DivisionCommMonoid G] (f g : α → G) (hs : s.Finite) :
    (∏ᶠ i ∈ s, f i / g i) = (∏ᶠ i ∈ s, f i) / ∏ᶠ i ∈ s, g i := by
  simp only [div_eq_mul_inv, finprod_mem_mul_distrib hs, finprod_mem_inv_distrib g hs]
#align finprod_mem_div_distrib finprod_mem_div_distrib
#align finsum_mem_sub_distrib finsum_mem_sub_distrib

/-!
### `∏ᶠ x ∈ s, f x` and set operations
-/


/- warning: finprod_mem_empty -> finprod_mem_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M}, Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) => f i))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M}, Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) => f i))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_empty finprod_mem_emptyₓ'. -/
/-- The product of any function over an empty set is `1`. -/
@[to_additive "The sum of any function over an empty set is `0`."]
theorem finprod_mem_empty : (∏ᶠ i ∈ (∅ : Set α), f i) = 1 := by simp
#align finprod_mem_empty finprod_mem_empty
#align finsum_mem_empty finsum_mem_empty

/- warning: nonempty_of_finprod_mem_ne_one -> nonempty_of_finprod_mem_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α}, (Ne.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) -> (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α}, (Ne.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => f i))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) -> (Set.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align nonempty_of_finprod_mem_ne_one nonempty_of_finprod_mem_ne_oneₓ'. -/
/-- A set `s` is nonempty if the product of some function over `s` is not equal to `1`. -/
@[to_additive "A set `s` is nonempty if the sum of some function over `s` is not equal to `0`."]
theorem nonempty_of_finprod_mem_ne_one (h : (∏ᶠ i ∈ s, f i) ≠ 1) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ finprod_mem_empty
#align nonempty_of_finprod_mem_ne_one nonempty_of_finprod_mem_ne_one
#align nonempty_of_finsum_mem_ne_zero nonempty_of_finsum_mem_ne_zero

/- warning: finprod_mem_union_inter -> finprod_mem_union_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Finite.{u1} α t) -> (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) => f i)))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} {t : Set.{u2} α}, (Set.Finite.{u2} α s) -> (Set.Finite.{u2} α t) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) => f i)))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_union_inter finprod_mem_union_interₓ'. -/
/-- Given finite sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` times the product of
`f i` over `i ∈ s ∩ t` equals the product of `f i` over `i ∈ s` times the product of `f i`
over `i ∈ t`. -/
@[to_additive
      "Given finite sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` plus the sum of\n`f i` over `i ∈ s ∩ t` equals the sum of `f i` over `i ∈ s` plus the sum of `f i` over `i ∈ t`."]
theorem finprod_mem_union_inter (hs : s.Finite) (ht : t.Finite) :
    ((∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
  by
  lift s to Finset α using hs; lift t to Finset α using ht
  classical
    rw [← Finset.coe_union, ← Finset.coe_inter]
    simp only [finprod_mem_coe_finset, Finset.prod_union_inter]
#align finprod_mem_union_inter finprod_mem_union_inter
#align finsum_mem_union_inter finsum_mem_union_inter

/- warning: finprod_mem_union_inter' -> finprod_mem_union_inter' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) => f i)))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} {t : Set.{u2} α}, (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) => f i)))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_union_inter' finprod_mem_union_inter'ₓ'. -/
/-- A more general version of `finprod_mem_union_inter` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` rather than `s` and `t` to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_union_inter` that requires `s ∩ support f` and\n`t ∩ support f` rather than `s` and `t` to be finite."]
theorem finprod_mem_union_inter' (hs : (s ∩ mulSupport f).Finite) (ht : (t ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
  by
  rw [← finprod_mem_inter_mulSupport f s, ← finprod_mem_inter_mulSupport f t, ←
    finprod_mem_union_inter hs ht, ← union_inter_distrib_right, finprod_mem_inter_mulSupport, ←
    finprod_mem_inter_mulSupport f (s ∩ t)]
  congr 2
  rw [inter_left_comm, inter_assoc, inter_assoc, inter_self, inter_left_comm]
#align finprod_mem_union_inter' finprod_mem_union_inter'
#align finsum_mem_union_inter' finsum_mem_union_inter'

/- warning: finprod_mem_union' -> finprod_mem_union' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) => f i))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} {t : Set.{u2} α}, (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s t) -> (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) => f i))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_union' finprod_mem_union'ₓ'. -/
/-- A more general version of `finprod_mem_union` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` rather than `s` and `t` to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_union` that requires `s ∩ support f` and\n`t ∩ support f` rather than `s` and `t` to be finite."]
theorem finprod_mem_union' (hst : Disjoint s t) (hs : (s ∩ mulSupport f).Finite)
    (ht : (t ∩ mulSupport f).Finite) : (∏ᶠ i ∈ s ∪ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_union_inter' hs ht, disjoint_iff_inter_eq_empty.1 hst, finprod_mem_empty,
    mul_one]
#align finprod_mem_union' finprod_mem_union'
#align finsum_mem_union' finsum_mem_union'

/- warning: finprod_mem_union -> finprod_mem_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Set.Finite.{u1} α s) -> (Set.Finite.{u1} α t) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) => f i))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} {t : Set.{u2} α}, (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s t) -> (Set.Finite.{u2} α s) -> (Set.Finite.{u2} α t) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) => f i))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_union finprod_mem_unionₓ'. -/
/-- Given two finite disjoint sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` equals the
product of `f i` over `i ∈ s` times the product of `f i` over `i ∈ t`. -/
@[to_additive
      "Given two finite disjoint sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` equals\nthe sum of `f i` over `i ∈ s` plus the sum of `f i` over `i ∈ t`."]
theorem finprod_mem_union (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite) :
    (∏ᶠ i ∈ s ∪ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
  finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)
#align finprod_mem_union finprod_mem_union
#align finsum_mem_union finsum_mem_union

/- warning: finprod_mem_union'' -> finprod_mem_union'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) => f i))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} {t : Set.{u2} α}, (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) => f i))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_union'' finprod_mem_union''ₓ'. -/
/-- A more general version of `finprod_mem_union'` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` rather than `s` and `t` to be disjoint -/
@[to_additive
      "A more general version of `finsum_mem_union'` that requires `s ∩ support f` and\n`t ∩ support f` rather than `s` and `t` to be disjoint"]
theorem finprod_mem_union'' (hst : Disjoint (s ∩ mulSupport f) (t ∩ mulSupport f))
    (hs : (s ∩ mulSupport f).Finite) (ht : (t ∩ mulSupport f).Finite) :
    (∏ᶠ i ∈ s ∪ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport f s, ← finprod_mem_inter_mulSupport f t, ←
    finprod_mem_union hst hs ht, ← union_inter_distrib_right, finprod_mem_inter_mulSupport]
#align finprod_mem_union'' finprod_mem_union''
#align finsum_mem_union'' finsum_mem_union''

#print finprod_mem_singleton /-
/-- The product of `f i` over `i ∈ {a}` equals `f a`. -/
@[to_additive "The sum of `f i` over `i ∈ {a}` equals `f a`."]
theorem finprod_mem_singleton : (∏ᶠ i ∈ ({a} : Set α), f i) = f a := by
  rw [← Finset.coe_singleton, finprod_mem_coe_finset, Finset.prod_singleton]
#align finprod_mem_singleton finprod_mem_singleton
#align finsum_mem_singleton finsum_mem_singleton
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (i «expr = » a) -/
#print finprod_cond_eq_left /-
@[simp, to_additive]
theorem finprod_cond_eq_left : (∏ᶠ (i) (_ : i = a), f i) = f a :=
  finprod_mem_singleton
#align finprod_cond_eq_left finprod_cond_eq_left
#align finsum_cond_eq_left finsum_cond_eq_left
-/

#print finprod_cond_eq_right /-
@[simp, to_additive]
theorem finprod_cond_eq_right : (∏ᶠ (i) (hi : a = i), f i) = f a := by simp [@eq_comm _ a]
#align finprod_cond_eq_right finprod_cond_eq_right
#align finsum_cond_eq_right finsum_cond_eq_right
-/

/- warning: finprod_mem_insert' -> finprod_mem_insert' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {a : α} {s : Set.{u1} α} (f : α -> M), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) => f i))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (f a) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {a : α} {s : Set.{u2} α} (f : α -> M), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) => f i))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f a) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_insert' finprod_mem_insert'ₓ'. -/
/-- A more general version of `finprod_mem_insert` that requires `s ∩ mul_support f` rather than `s`
to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_insert` that requires `s ∩ support f` rather\nthan `s` to be finite."]
theorem finprod_mem_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ mulSupport f).Finite) :
    (∏ᶠ i ∈ insert a s, f i) = f a * ∏ᶠ i ∈ s, f i :=
  by
  rw [insert_eq, finprod_mem_union' _ _ hs, finprod_mem_singleton]
  · rwa [disjoint_singleton_left]
  · exact (finite_singleton a).inter_of_left _
#align finprod_mem_insert' finprod_mem_insert'
#align finsum_mem_insert' finsum_mem_insert'

/- warning: finprod_mem_insert -> finprod_mem_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {a : α} {s : Set.{u1} α} (f : α -> M), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Set.Finite.{u1} α s) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) => f i))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (f a) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {a : α} {s : Set.{u2} α} (f : α -> M), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (Set.Finite.{u2} α s) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) => f i))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f a) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_insert finprod_mem_insertₓ'. -/
/-- Given a finite set `s` and an element `a ∉ s`, the product of `f i` over `i ∈ insert a s` equals
`f a` times the product of `f i` over `i ∈ s`. -/
@[to_additive
      "Given a finite set `s` and an element `a ∉ s`, the sum of `f i` over `i ∈ insert a s`\nequals `f a` plus the sum of `f i` over `i ∈ s`."]
theorem finprod_mem_insert (f : α → M) (h : a ∉ s) (hs : s.Finite) :
    (∏ᶠ i ∈ insert a s, f i) = f a * ∏ᶠ i ∈ s, f i :=
  finprod_mem_insert' f h <| hs.inter_of_left _
#align finprod_mem_insert finprod_mem_insert
#align finsum_mem_insert finsum_mem_insert

/- warning: finprod_mem_insert_of_eq_one_if_not_mem -> finprod_mem_insert_of_eq_one_if_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {a : α} {s : Set.{u1} α}, ((Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ u2} M (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {a : α} {s : Set.{u2} α}, ((Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (Eq.{succ u1} M (f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s)) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_insert_of_eq_one_if_not_mem finprod_mem_insert_of_eq_one_if_not_memₓ'. -/
/-- If `f a = 1` when `a ∉ s`, then the product of `f i` over `i ∈ insert a s` equals the product of
`f i` over `i ∈ s`. -/
@[to_additive
      "If `f a = 0` when `a ∉ s`, then the sum of `f i` over `i ∈ insert a s` equals the sum\nof `f i` over `i ∈ s`."]
theorem finprod_mem_insert_of_eq_one_if_not_mem (h : a ∉ s → f a = 1) :
    (∏ᶠ i ∈ insert a s, f i) = ∏ᶠ i ∈ s, f i :=
  by
  refine' finprod_mem_inter_mulSupport_eq' _ _ _ fun x hx => ⟨_, Or.inr⟩
  rintro (rfl | hxs)
  exacts[not_imp_comm.1 h hx, hxs]
#align finprod_mem_insert_of_eq_one_if_not_mem finprod_mem_insert_of_eq_one_if_not_mem
#align finsum_mem_insert_of_eq_zero_if_not_mem finsum_mem_insert_of_eq_zero_if_not_mem

/- warning: finprod_mem_insert_one -> finprod_mem_insert_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {a : α} {s : Set.{u1} α}, (Eq.{succ u2} M (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {a : α} {s : Set.{u1} α}, (Eq.{succ u2} M (f a) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_insert_one finprod_mem_insert_oneₓ'. -/
/-- If `f a = 1`, then the product of `f i` over `i ∈ insert a s` equals the product of `f i` over
`i ∈ s`. -/
@[to_additive
      "If `f a = 0`, then the sum of `f i` over `i ∈ insert a s` equals the sum of `f i`\nover `i ∈ s`."]
theorem finprod_mem_insert_one (h : f a = 1) : (∏ᶠ i ∈ insert a s, f i) = ∏ᶠ i ∈ s, f i :=
  finprod_mem_insert_of_eq_one_if_not_mem fun _ => h
#align finprod_mem_insert_one finprod_mem_insert_one
#align finsum_mem_insert_zero finsum_mem_insert_zero

/- warning: finprod_mem_dvd -> finprod_mem_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_2 : CommMonoid.{u2} N] {f : α -> N} (a : α), (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) f)) -> (Dvd.Dvd.{u2} N (semigroupDvd.{u2} N (Monoid.toSemigroup.{u2} N (CommMonoid.toMonoid.{u2} N _inst_2))) (f a) (finprod.{u2, succ u1} N α _inst_2 f))
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [_inst_2 : CommMonoid.{u1} N] {f : α -> N} (a : α), (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2)) f)) -> (Dvd.dvd.{u1} N (semigroupDvd.{u1} N (Monoid.toSemigroup.{u1} N (CommMonoid.toMonoid.{u1} N _inst_2))) (f a) (finprod.{u1, succ u2} N α _inst_2 f))
Case conversion may be inaccurate. Consider using '#align finprod_mem_dvd finprod_mem_dvdₓ'. -/
/-- If the multiplicative support of `f` is finite, then for every `x` in the domain of `f`, `f x`
divides `finprod f`.  -/
theorem finprod_mem_dvd {f : α → N} (a : α) (hf : (mulSupport f).Finite) : f a ∣ finprod f :=
  by
  by_cases ha : a ∈ mul_support f
  · rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Set.Subset.refl _)]
    exact Finset.dvd_prod_of_mem f ((finite.mem_to_finset hf).mpr ha)
  · rw [nmem_mul_support.mp ha]
    exact one_dvd (finprod f)
#align finprod_mem_dvd finprod_mem_dvd

/- warning: finprod_mem_pair -> finprod_mem_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {a : α} {b : α}, (Ne.{succ u1} α a b) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) => f i))) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (f a) (f b)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {a : α} {b : α}, (Ne.{succ u2} α a b) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) b))) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) b))) => f i))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align finprod_mem_pair finprod_mem_pairₓ'. -/
/-- The product of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a * f b`. -/
@[to_additive "The sum of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a + f b`."]
theorem finprod_mem_pair (h : a ≠ b) : (∏ᶠ i ∈ ({a, b} : Set α), f i) = f a * f b :=
  by
  rw [finprod_mem_insert, finprod_mem_singleton]
  exacts[h, finite_singleton b]
#align finprod_mem_pair finprod_mem_pair
#align finsum_mem_pair finsum_mem_pair

/- warning: finprod_mem_image' -> finprod_mem_image' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {f : α -> M} {s : Set.{u2} β} {g : β -> α}, (Set.InjOn.{u2, u1} β α g (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s (Function.mulSupport.{u2, u3} β M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (Function.comp.{succ u2, succ u1, succ u3} β α M f g)))) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Set.image.{u2, u1} β α g s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Set.image.{u2, u1} β α g s)) => f i))) (finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => finprod.{u3, 0} M (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j s) _inst_1 (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j s) => f (g j)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u3} β} {g : β -> α}, (Set.InjOn.{u3, u2} β α g (Inter.inter.{u3} (Set.{u3} β) (Set.instInterSet.{u3} β) s (Function.mulSupport.{u3, u1} β M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Function.comp.{succ u3, succ u2, succ u1} β α M f g)))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Set.image.{u3, u2} β α g s)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Set.image.{u3, u2} β α g s)) => f i))) (finprod.{u1, succ u3} M β _inst_1 (fun (j : β) => finprod.{u1, 0} M (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) j s) _inst_1 (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) j s) => f (g j)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_image' finprod_mem_image'ₓ'. -/
/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s ∩ mul_support (f ∘ g)`. -/
@[to_additive
      "The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that\n`g` is injective on `s ∩ support (f ∘ g)`."]
theorem finprod_mem_image' {s : Set β} {g : β → α} (hg : (s ∩ mulSupport (f ∘ g)).InjOn g) :
    (∏ᶠ i ∈ g '' s, f i) = ∏ᶠ j ∈ s, f (g j) := by
  classical
    by_cases hs : (s ∩ mul_support (f ∘ g)).Finite
    · have hg : ∀ x ∈ hs.to_finset, ∀ y ∈ hs.to_finset, g x = g y → x = y := by
        simpa only [hs.mem_to_finset]
      rw [finprod_mem_eq_prod _ hs, ← Finset.prod_image hg]
      refine' finprod_mem_eq_prod_of_inter_mulSupport_eq f _
      rw [Finset.coe_image, hs.coe_to_finset, ← image_inter_mul_support_eq, inter_assoc, inter_self]
    · rw [finprod_mem_eq_one_of_infinite hs, finprod_mem_eq_one_of_infinite]
      rwa [image_inter_mul_support_eq, infinite_image_iff hg]
#align finprod_mem_image' finprod_mem_image'
#align finsum_mem_image' finsum_mem_image'

/- warning: finprod_mem_image -> finprod_mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {f : α -> M} {s : Set.{u2} β} {g : β -> α}, (Set.InjOn.{u2, u1} β α g s) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Set.image.{u2, u1} β α g s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Set.image.{u2, u1} β α g s)) => f i))) (finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => finprod.{u3, 0} M (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j s) _inst_1 (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j s) => f (g j)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u3} β} {g : β -> α}, (Set.InjOn.{u3, u2} β α g s) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Set.image.{u3, u2} β α g s)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Set.image.{u3, u2} β α g s)) => f i))) (finprod.{u1, succ u3} M β _inst_1 (fun (j : β) => finprod.{u1, 0} M (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) j s) _inst_1 (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) j s) => f (g j)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_image finprod_mem_imageₓ'. -/
/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s` provided that
`g` is injective on `s`. -/
@[to_additive
      "The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that\n`g` is injective on `s`."]
theorem finprod_mem_image {s : Set β} {g : β → α} (hg : s.InjOn g) :
    (∏ᶠ i ∈ g '' s, f i) = ∏ᶠ j ∈ s, f (g j) :=
  finprod_mem_image' <| hg.mono <| inter_subset_left _ _
#align finprod_mem_image finprod_mem_image
#align finsum_mem_image finsum_mem_image

/- warning: finprod_mem_range' -> finprod_mem_range' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {f : α -> M} {g : β -> α}, (Set.InjOn.{u2, u1} β α g (Function.mulSupport.{u2, u3} β M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (Function.comp.{succ u2, succ u1, succ u3} β α M f g))) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Set.range.{u1, succ u2} α β g)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Set.range.{u1, succ u2} α β g)) => f i))) (finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => f (g j))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {g : β -> α}, (Set.InjOn.{u3, u2} β α g (Function.mulSupport.{u3, u1} β M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Function.comp.{succ u3, succ u2, succ u1} β α M f g))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Set.range.{u2, succ u3} α β g)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Set.range.{u2, succ u3} α β g)) => f i))) (finprod.{u1, succ u3} M β _inst_1 (fun (j : β) => f (g j))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_range' finprod_mem_range'ₓ'. -/
/-- The product of `f y` over `y ∈ set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective on `mul_support (f ∘ g)`. -/
@[to_additive
      "The sum of `f y` over `y ∈ set.range g` equals the sum of `f (g i)` over all `i`\nprovided that `g` is injective on `support (f ∘ g)`."]
theorem finprod_mem_range' {g : β → α} (hg : (mulSupport (f ∘ g)).InjOn g) :
    (∏ᶠ i ∈ range g, f i) = ∏ᶠ j, f (g j) :=
  by
  rw [← image_univ, finprod_mem_image', finprod_mem_univ]
  rwa [univ_inter]
#align finprod_mem_range' finprod_mem_range'
#align finsum_mem_range' finsum_mem_range'

/- warning: finprod_mem_range -> finprod_mem_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {f : α -> M} {g : β -> α}, (Function.Injective.{succ u2, succ u1} β α g) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Set.range.{u1, succ u2} α β g)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Set.range.{u1, succ u2} α β g)) => f i))) (finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => f (g j))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {g : β -> α}, (Function.Injective.{succ u3, succ u2} β α g) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Set.range.{u2, succ u3} α β g)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Set.range.{u2, succ u3} α β g)) => f i))) (finprod.{u1, succ u3} M β _inst_1 (fun (j : β) => f (g j))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_range finprod_mem_rangeₓ'. -/
/-- The product of `f y` over `y ∈ set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective. -/
@[to_additive
      "The sum of `f y` over `y ∈ set.range g` equals the sum of `f (g i)` over all `i`\nprovided that `g` is injective."]
theorem finprod_mem_range {g : β → α} (hg : Injective g) : (∏ᶠ i ∈ range g, f i) = ∏ᶠ j, f (g j) :=
  finprod_mem_range' (hg.InjOn _)
#align finprod_mem_range finprod_mem_range
#align finsum_mem_range finsum_mem_range

/- warning: finprod_mem_eq_of_bij_on -> finprod_mem_eq_of_bijOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> M} {g : β -> M} (e : α -> β), (Set.BijOn.{u1, u2} α β e s t) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u3} M (f x) (g (e x)))) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => finprod.{u3, 0} M (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j t) _inst_1 (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j t) => g j))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {s : Set.{u3} α} {t : Set.{u2} β} {f : α -> M} {g : β -> M} (e : α -> β), (Set.BijOn.{u3, u2} α β e s t) -> (forall (x : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) -> (Eq.{succ u1} M (f x) (g (e x)))) -> (Eq.{succ u1} M (finprod.{u1, succ u3} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) i s) _inst_1 (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) i s) => f i))) (finprod.{u1, succ u2} M β _inst_1 (fun (j : β) => finprod.{u1, 0} M (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) j t) _inst_1 (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) j t) => g j))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_eq_of_bij_on finprod_mem_eq_of_bijOnₓ'. -/
/-- See also `finset.prod_bij`. -/
@[to_additive "See also `finset.sum_bij`."]
theorem finprod_mem_eq_of_bijOn {s : Set α} {t : Set β} {f : α → M} {g : β → M} (e : α → β)
    (he₀ : s.BijOn e t) (he₁ : ∀ x ∈ s, f x = g (e x)) : (∏ᶠ i ∈ s, f i) = ∏ᶠ j ∈ t, g j :=
  by
  rw [← Set.BijOn.image_eq he₀, finprod_mem_image he₀.2.1]
  exact finprod_mem_congr rfl he₁
#align finprod_mem_eq_of_bij_on finprod_mem_eq_of_bijOn
#align finsum_mem_eq_of_bij_on finsum_mem_eq_of_bijOn

/- warning: finprod_eq_of_bijective -> finprod_eq_of_bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {f : α -> M} {g : β -> M} (e : α -> β), (Function.Bijective.{succ u1, succ u2} α β e) -> (forall (x : α), Eq.{succ u3} M (f x) (g (e x))) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => f i)) (finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => g j)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {g : β -> M} (e : α -> β), (Function.Bijective.{succ u3, succ u2} α β e) -> (forall (x : α), Eq.{succ u1} M (f x) (g (e x))) -> (Eq.{succ u1} M (finprod.{u1, succ u3} M α _inst_1 (fun (i : α) => f i)) (finprod.{u1, succ u2} M β _inst_1 (fun (j : β) => g j)))
Case conversion may be inaccurate. Consider using '#align finprod_eq_of_bijective finprod_eq_of_bijectiveₓ'. -/
/-- See `finprod_comp`, `fintype.prod_bijective` and `finset.prod_bij`. -/
@[to_additive "See `finsum_comp`, `fintype.sum_bijective` and `finset.sum_bij`."]
theorem finprod_eq_of_bijective {f : α → M} {g : β → M} (e : α → β) (he₀ : Bijective e)
    (he₁ : ∀ x, f x = g (e x)) : (∏ᶠ i, f i) = ∏ᶠ j, g j :=
  by
  rw [← finprod_mem_univ f, ← finprod_mem_univ g]
  exact finprod_mem_eq_of_bijOn _ (bijective_iff_bij_on_univ.mp he₀) fun x _ => he₁ x
#align finprod_eq_of_bijective finprod_eq_of_bijective
#align finsum_eq_of_bijective finsum_eq_of_bijective

/- warning: finprod_comp -> finprod_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {g : β -> M} (e : α -> β), (Function.Bijective.{succ u1, succ u2} α β e) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => g (e i))) (finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => g j)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {g : β -> M} (e : α -> β), (Function.Bijective.{succ u3, succ u2} α β e) -> (Eq.{succ u1} M (finprod.{u1, succ u3} M α _inst_1 (fun (i : α) => g (e i))) (finprod.{u1, succ u2} M β _inst_1 (fun (j : β) => g j)))
Case conversion may be inaccurate. Consider using '#align finprod_comp finprod_compₓ'. -/
/-- See also `finprod_eq_of_bijective`, `fintype.prod_bijective` and `finset.prod_bij`. -/
@[to_additive "See also `finsum_eq_of_bijective`, `fintype.sum_bijective` and `finset.sum_bij`."]
theorem finprod_comp {g : β → M} (e : α → β) (he₀ : Function.Bijective e) :
    (∏ᶠ i, g (e i)) = ∏ᶠ j, g j :=
  finprod_eq_of_bijective e he₀ fun x => rfl
#align finprod_comp finprod_comp
#align finsum_comp finsum_comp

/- warning: finprod_comp_equiv -> finprod_comp_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (e : Equiv.{succ u1, succ u2} α β) {f : β -> M}, Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => f (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e i))) (finprod.{u3, succ u2} M β _inst_1 (fun (i' : β) => f i'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (e : Equiv.{succ u3, succ u2} α β) {f : β -> M}, Eq.{succ u1} M (finprod.{u1, succ u3} M α _inst_1 (fun (i : α) => f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} α β) e i))) (finprod.{u1, succ u2} M β _inst_1 (fun (i' : β) => f i'))
Case conversion may be inaccurate. Consider using '#align finprod_comp_equiv finprod_comp_equivₓ'. -/
@[to_additive]
theorem finprod_comp_equiv (e : α ≃ β) {f : β → M} : (∏ᶠ i, f (e i)) = ∏ᶠ i', f i' :=
  finprod_comp e e.Bijective
#align finprod_comp_equiv finprod_comp_equiv
#align finsum_comp_equiv finsum_comp_equiv

/- warning: finprod_set_coe_eq_finprod_mem -> finprod_set_coe_eq_finprod_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} (s : Set.{u1} α), Eq.{succ u2} M (finprod.{u2, succ u1} M (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) _inst_1 (fun (j : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) j))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} (s : Set.{u2} α), Eq.{succ u1} M (finprod.{u1, succ u2} M (Set.Elem.{u2} α s) _inst_1 (fun (j : Set.Elem.{u2} α s) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) j))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i)))
Case conversion may be inaccurate. Consider using '#align finprod_set_coe_eq_finprod_mem finprod_set_coe_eq_finprod_memₓ'. -/
@[to_additive]
theorem finprod_set_coe_eq_finprod_mem (s : Set α) : (∏ᶠ j : s, f j) = ∏ᶠ i ∈ s, f i :=
  by
  rw [← finprod_mem_range, Subtype.range_coe]
  exact Subtype.coe_injective
#align finprod_set_coe_eq_finprod_mem finprod_set_coe_eq_finprod_mem
#align finsum_set_coe_eq_finsum_mem finsum_set_coe_eq_finsum_mem

#print finprod_subtype_eq_finprod_cond /-
@[to_additive]
theorem finprod_subtype_eq_finprod_cond (p : α → Prop) :
    (∏ᶠ j : Subtype p, f j) = ∏ᶠ (i) (hi : p i), f i :=
  finprod_set_coe_eq_finprod_mem { i | p i }
#align finprod_subtype_eq_finprod_cond finprod_subtype_eq_finprod_cond
#align finsum_subtype_eq_finsum_cond finsum_subtype_eq_finsum_cond
-/

/- warning: finprod_mem_inter_mul_diff' -> finprod_mem_inter_mul_diff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} (t : Set.{u1} α), (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) => f i)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} (t : Set.{u2} α), (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s t)) => f i)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_inter_mul_diff' finprod_mem_inter_mul_diff'ₓ'. -/
@[to_additive]
theorem finprod_mem_inter_mul_diff' (t : Set α) (h : (s ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i :=
  by
  rw [← finprod_mem_union', inter_union_diff]
  rw [disjoint_iff_inf_le]
  exacts[fun x hx => hx.2.2 hx.1.2, h.subset fun x hx => ⟨hx.1.1, hx.2⟩,
    h.subset fun x hx => ⟨hx.1.1, hx.2⟩]
#align finprod_mem_inter_mul_diff' finprod_mem_inter_mul_diff'
#align finsum_mem_inter_add_diff' finsum_mem_inter_add_diff'

/- warning: finprod_mem_inter_mul_diff -> finprod_mem_inter_mul_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} (t : Set.{u1} α), (Set.Finite.{u1} α s) -> (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) => f i)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} (t : Set.{u2} α), (Set.Finite.{u2} α s) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s t)) => f i)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_inter_mul_diff finprod_mem_inter_mul_diffₓ'. -/
@[to_additive]
theorem finprod_mem_inter_mul_diff (t : Set α) (h : s.Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i :=
  finprod_mem_inter_mul_diff' _ <| h.inter_of_left _
#align finprod_mem_inter_mul_diff finprod_mem_inter_mul_diff
#align finsum_mem_inter_add_diff finsum_mem_inter_add_diff

/- warning: finprod_mem_mul_diff' -> finprod_mem_mul_diff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f))) -> (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) => f i)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} {t : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (Set.Finite.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f))) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) t s)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) t s)) => f i)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_mul_diff' finprod_mem_mul_diff'ₓ'. -/
/-- A more general version of `finprod_mem_mul_diff` that requires `t ∩ mul_support f` rather than
`t` to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_add_diff` that requires `t ∩ support f` rather\nthan `t` to be finite."]
theorem finprod_mem_mul_diff' (hst : s ⊆ t) (ht : (t ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mul_diff' _ ht, inter_eq_self_of_subset_right hst]
#align finprod_mem_mul_diff' finprod_mem_mul_diff'
#align finsum_mem_add_diff' finsum_mem_add_diff'

/- warning: finprod_mem_mul_diff -> finprod_mem_mul_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Set.Finite.{u1} α t) -> (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) => f i)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i t) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {s : Set.{u2} α} {t : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (Set.Finite.{u2} α t) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) => f i))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) t s)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) t s)) => f i)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i t) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_mul_diff finprod_mem_mul_diffₓ'. -/
/-- Given a finite set `t` and a subset `s` of `t`, the product of `f i` over `i ∈ s`
times the product of `f i` over `t \ s` equals the product of `f i` over `i ∈ t`. -/
@[to_additive
      "Given a finite set `t` and a subset `s` of `t`, the sum of `f i` over `i ∈ s` plus\nthe sum of `f i` over `t \\ s` equals the sum of `f i` over `i ∈ t`."]
theorem finprod_mem_mul_diff (hst : s ⊆ t) (ht : t.Finite) :
    ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i :=
  finprod_mem_mul_diff' hst (ht.inter_of_left _)
#align finprod_mem_mul_diff finprod_mem_mul_diff
#align finsum_mem_add_diff finsum_mem_add_diff

/- warning: finprod_mem_Union -> finprod_mem_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {f : α -> M} [_inst_3 : Finite.{succ u2} ι] {t : ι -> (Set.{u1} α)}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) t)) -> (forall (i : ι), Set.Finite.{u1} α (t i)) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => t i))) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => t i))) => f a))) (finprod.{u3, succ u2} M ι _inst_1 (fun (i : ι) => finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (t i)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (t i)) => f a)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} [_inst_3 : Finite.{succ u3} ι] {t : ι -> (Set.{u2} α)}, (Pairwise.{u3} ι (Function.onFun.{succ u3, succ u2, 1} ι (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) t)) -> (forall (i : ι), Set.Finite.{u2} α (t i)) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.unionᵢ.{u2, succ u3} α ι (fun (i : ι) => t i))) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.unionᵢ.{u2, succ u3} α ι (fun (i : ι) => t i))) => f a))) (finprod.{u1, succ u3} M ι _inst_1 (fun (i : ι) => finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (t i)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (t i)) => f a)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_Union finprod_mem_unionᵢₓ'. -/
/-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the product of
`f a` over the union `⋃ i, t i` is equal to the product over all indexes `i` of the products of
`f a` over `a ∈ t i`. -/
@[to_additive
      "Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the\nsum of `f a` over the union `⋃ i, t i` is equal to the sum over all indexes `i` of the sums of `f a`\nover `a ∈ t i`."]
theorem finprod_mem_unionᵢ [Finite ι] {t : ι → Set α} (h : Pairwise (Disjoint on t))
    (ht : ∀ i, (t i).Finite) : (∏ᶠ a ∈ ⋃ i : ι, t i, f a) = ∏ᶠ i, ∏ᶠ a ∈ t i, f a :=
  by
  cases nonempty_fintype ι
  lift t to ι → Finset α using ht
  classical
    rw [← bUnion_univ, ← Finset.coe_univ, ← Finset.coe_bunionᵢ, finprod_mem_coe_finset,
      Finset.prod_bunionᵢ]
    · simp only [finprod_mem_coe_finset, finprod_eq_prod_of_fintype]
    · exact fun x _ y _ hxy => Finset.disjoint_coe.1 (h hxy)
#align finprod_mem_Union finprod_mem_unionᵢ
#align finsum_mem_Union finsum_mem_unionᵢ

/- warning: finprod_mem_bUnion -> finprod_mem_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {f : α -> M} {I : Set.{u2} ι} {t : ι -> (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) I t) -> (Set.Finite.{u2} ι I) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) -> (Set.Finite.{u1} α (t i))) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, succ u2} α ι (fun (x : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I) => t x)))) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionᵢ.{u1, succ u2} α ι (fun (x : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x I) => t x)))) => f a))) (finprod.{u3, succ u2} M ι _inst_1 (fun (i : ι) => finprod.{u3, 0} M (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) _inst_1 (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) => finprod.{u3, succ u1} M α _inst_1 (fun (j : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j (t i)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j (t i)) => f j))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {I : Set.{u3} ι} {t : ι -> (Set.{u2} α)}, (Set.PairwiseDisjoint.{u2, u3} (Set.{u2} α) ι (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) I t) -> (Set.Finite.{u3} ι I) -> (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i I) -> (Set.Finite.{u2} α (t i))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.unionᵢ.{u2, succ u3} α ι (fun (x : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) => t x)))) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.unionᵢ.{u2, succ u3} α ι (fun (x : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) x I) => t x)))) => f a))) (finprod.{u1, succ u3} M ι _inst_1 (fun (i : ι) => finprod.{u1, 0} M (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i I) _inst_1 (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i I) => finprod.{u1, succ u2} M α _inst_1 (fun (j : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j (t i)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j (t i)) => f j))))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_bUnion finprod_mem_bunionᵢₓ'. -/
/-- Given a family of sets `t : ι → set α`, a finite set `I` in the index type such that all sets
`t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the product of `f a`
over `a ∈ ⋃ i ∈ I, t i` is equal to the product over `i ∈ I` of the products of `f a` over
`a ∈ t i`. -/
@[to_additive
      "Given a family of sets `t : ι → set α`, a finite set `I` in the index type such that\nall sets `t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the sum of\n`f a` over `a ∈ ⋃ i ∈ I, t i` is equal to the sum over `i ∈ I` of the sums of `f a` over\n`a ∈ t i`."]
theorem finprod_mem_bunionᵢ {I : Set ι} {t : ι → Set α} (h : I.PairwiseDisjoint t) (hI : I.Finite)
    (ht : ∀ i ∈ I, (t i).Finite) : (∏ᶠ a ∈ ⋃ x ∈ I, t x, f a) = ∏ᶠ i ∈ I, ∏ᶠ j ∈ t i, f j :=
  by
  haveI := hI.fintype
  rw [bUnion_eq_Union, finprod_mem_unionᵢ, ← finprod_set_coe_eq_finprod_mem]
  exacts[fun x y hxy => h x.2 y.2 (subtype.coe_injective.ne hxy), fun b => ht b b.2]
#align finprod_mem_bUnion finprod_mem_bunionᵢ
#align finsum_mem_bUnion finsum_mem_bunionᵢ

/- warning: finprod_mem_sUnion -> finprod_mem_unionₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {t : Set.{u1} (Set.{u1} α)}, (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t (id.{succ u1} (Set.{u1} α))) -> (Set.Finite.{u1} (Set.{u1} α) t) -> (forall (x : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x t) -> (Set.Finite.{u1} α x)) -> (Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (a : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionₛ.{u1} α t)) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Set.unionₛ.{u1} α t)) => f a))) (finprod.{u2, succ u1} M (Set.{u1} α) _inst_1 (fun (s : Set.{u1} α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s t) _inst_1 (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s t) => finprod.{u2, succ u1} M α _inst_1 (fun (a : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} {t : Set.{u2} (Set.{u2} α)}, (Set.PairwiseDisjoint.{u2, u2} (Set.{u2} α) (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) t (id.{succ u2} (Set.{u2} α))) -> (Set.Finite.{u2} (Set.{u2} α) t) -> (forall (x : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) x t) -> (Set.Finite.{u2} α x)) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.unionₛ.{u2} α t)) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Set.unionₛ.{u2} α t)) => f a))) (finprod.{u1, succ u2} M (Set.{u2} α) _inst_1 (fun (s : Set.{u2} α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s t) _inst_1 (fun (H : Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s t) => finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) _inst_1 (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => f a))))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_sUnion finprod_mem_unionₛₓ'. -/
/-- If `t` is a finite set of pairwise disjoint finite sets, then the product of `f a`
over `a ∈ ⋃₀ t` is the product over `s ∈ t` of the products of `f a` over `a ∈ s`. -/
@[to_additive
      "If `t` is a finite set of pairwise disjoint finite sets, then the sum of `f a` over\n`a ∈ ⋃₀ t` is the sum over `s ∈ t` of the sums of `f a` over `a ∈ s`."]
theorem finprod_mem_unionₛ {t : Set (Set α)} (h : t.PairwiseDisjoint id) (ht₀ : t.Finite)
    (ht₁ : ∀ x ∈ t, Set.Finite x) : (∏ᶠ a ∈ ⋃₀ t, f a) = ∏ᶠ s ∈ t, ∏ᶠ a ∈ s, f a :=
  by
  rw [Set.unionₛ_eq_bunionᵢ]
  exact finprod_mem_bunionᵢ h ht₀ ht₁
#align finprod_mem_sUnion finprod_mem_unionₛ
#align finsum_mem_sUnion finsum_mem_unionₛ

/- warning: mul_finprod_cond_ne -> mul_finprod_cond_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} (a : α), (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) f)) -> (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (f a) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Ne.{succ u1} α i a) _inst_1 (fun (H : Ne.{succ u1} α i a) => f i)))) (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> M} (a : α), (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f a) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Ne.{succ u2} α i a) _inst_1 (fun (H : Ne.{succ u2} α i a) => f i)))) (finprod.{u1, succ u2} M α _inst_1 (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align mul_finprod_cond_ne mul_finprod_cond_neₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (i «expr ≠ » a) -/
@[to_additive]
theorem mul_finprod_cond_ne (a : α) (hf : (mulSupport f).Finite) :
    (f a * ∏ᶠ (i) (_ : i ≠ a), f i) = ∏ᶠ i, f i := by
  classical
    rw [finprod_eq_prod _ hf]
    have h : ∀ x : α, f x ≠ 1 → (x ≠ a ↔ x ∈ hf.to_finset \ {a}) :=
      by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_singleton, finite.mem_to_finset, mem_mul_support]
      exact ⟨fun h => And.intro hx h, fun h => h.2⟩
    rw [finprod_cond_eq_prod_of_cond_iff f h, Finset.sdiff_singleton_eq_erase]
    by_cases ha : a ∈ mul_support f
    · apply Finset.mul_prod_erase _ _ ((finite.mem_to_finset _).mpr ha)
    · rw [mem_mul_support, Classical.not_not] at ha
      rw [ha, one_mul]
      apply Finset.prod_erase _ ha
#align mul_finprod_cond_ne mul_finprod_cond_ne
#align add_finsum_cond_ne add_finsum_cond_ne

/- warning: finprod_mem_comm -> finprod_mem_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {s : Set.{u1} α} {t : Set.{u2} β} (f : α -> β -> M), (Set.Finite.{u1} α s) -> (Set.Finite.{u2} β t) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => finprod.{u3, 0} M (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j t) _inst_1 (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j t) => f i j))))) (finprod.{u3, succ u2} M β _inst_1 (fun (j : β) => finprod.{u3, 0} M (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j t) _inst_1 (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) j t) => finprod.{u3, succ u1} M α _inst_1 (fun (i : α) => finprod.{u3, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i j))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {s : Set.{u3} α} {t : Set.{u2} β} (f : α -> β -> M), (Set.Finite.{u3} α s) -> (Set.Finite.{u2} β t) -> (Eq.{succ u1} M (finprod.{u1, succ u3} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) i s) _inst_1 (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) i s) => finprod.{u1, succ u2} M β _inst_1 (fun (j : β) => finprod.{u1, 0} M (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) j t) _inst_1 (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) j t) => f i j))))) (finprod.{u1, succ u2} M β _inst_1 (fun (j : β) => finprod.{u1, 0} M (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) j t) _inst_1 (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) j t) => finprod.{u1, succ u3} M α _inst_1 (fun (i : α) => finprod.{u1, 0} M (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) i s) _inst_1 (fun (H : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) i s) => f i j))))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_comm finprod_mem_commₓ'. -/
/-- If `s : set α` and `t : set β` are finite sets, then taking the product over `s` commutes with
taking the product over `t`. -/
@[to_additive
      "If `s : set α` and `t : set β` are finite sets, then summing over `s` commutes with\nsumming over `t`."]
theorem finprod_mem_comm {s : Set α} {t : Set β} (f : α → β → M) (hs : s.Finite) (ht : t.Finite) :
    (∏ᶠ i ∈ s, ∏ᶠ j ∈ t, f i j) = ∏ᶠ j ∈ t, ∏ᶠ i ∈ s, f i j :=
  by
  lift s to Finset α using hs; lift t to Finset β using ht
  simp only [finprod_mem_coe_finset]
  exact Finset.prod_comm
#align finprod_mem_comm finprod_mem_comm
#align finsum_mem_comm finsum_mem_comm

/- warning: finprod_mem_induction -> finprod_mem_induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} (p : M -> Prop), (p (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (p (f x))) -> (p (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) _inst_1 (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => f i))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {f : α -> M} {s : Set.{u1} α} (p : M -> Prop), (p (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y))) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (p (f x))) -> (p (finprod.{u2, succ u1} M α _inst_1 (fun (i : α) => finprod.{u2, 0} M (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) _inst_1 (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => f i))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_induction finprod_mem_inductionₓ'. -/
/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on factors. -/
@[to_additive
      "To prove a property of a finite sum, it suffices to prove that the property is\nadditive and holds on summands."]
theorem finprod_mem_induction (p : M → Prop) (hp₀ : p 1) (hp₁ : ∀ x y, p x → p y → p (x * y))
    (hp₂ : ∀ x ∈ s, p <| f x) : p (∏ᶠ i ∈ s, f i) :=
  finprod_induction _ hp₀ hp₁ fun x => finprod_induction _ hp₀ hp₁ <| hp₂ x
#align finprod_mem_induction finprod_mem_induction
#align finsum_mem_induction finsum_mem_induction

/- warning: finprod_cond_nonneg -> finprod_cond_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_3 : OrderedCommSemiring.{u2} R] {p : α -> Prop} {f : α -> R}, (forall (x : α), (p x) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3))))))))) (f x))) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3))))))))) (finprod.{u2, succ u1} R α (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3)) (fun (x : α) => finprod.{u2, 0} R (p x) (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3)) (fun (h : p x) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_3 : OrderedCommSemiring.{u2} R] {p : α -> Prop} {f : α -> R}, (forall (x : α), (p x) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedSemiring.toPartialOrder.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3))))) (f x))) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedSemiring.toPartialOrder.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_3)))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3))))) (finprod.{u2, succ u1} R α (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3)) (fun (x : α) => finprod.{u2, 0} R (p x) (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_3)) (fun (h : p x) => f x))))
Case conversion may be inaccurate. Consider using '#align finprod_cond_nonneg finprod_cond_nonnegₓ'. -/
theorem finprod_cond_nonneg {R : Type _} [OrderedCommSemiring R] {p : α → Prop} {f : α → R}
    (hf : ∀ x, p x → 0 ≤ f x) : 0 ≤ ∏ᶠ (x) (h : p x), f x :=
  finprod_nonneg fun x => finprod_nonneg <| hf x
#align finprod_cond_nonneg finprod_cond_nonneg

/- warning: single_le_finprod -> single_le_finprod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_3 : OrderedCommMonoid.{u2} M] (i : α) {f : α -> M}, (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3)))) f)) -> (forall (j : α), LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M _inst_3))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3))))))) (f j)) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M _inst_3))) (f i) (finprod.{u2, succ u1} M α (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3) (fun (j : α) => f j)))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_3 : OrderedCommMonoid.{u2} M] (i : α) {f : α -> M}, (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3))) f)) -> (forall (j : α), LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M _inst_3))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3))))) (f j)) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M _inst_3))) (f i) (finprod.{u2, succ u1} M α (OrderedCommMonoid.toCommMonoid.{u2} M _inst_3) (fun (j : α) => f j)))
Case conversion may be inaccurate. Consider using '#align single_le_finprod single_le_finprodₓ'. -/
@[to_additive]
theorem single_le_finprod {M : Type _} [OrderedCommMonoid M] (i : α) {f : α → M}
    (hf : (mulSupport f).Finite) (h : ∀ j, 1 ≤ f j) : f i ≤ ∏ᶠ j, f j := by
  classical calc
      f i ≤ ∏ j in insert i hf.to_finset, f j :=
        Finset.single_le_prod' (fun j hj => h j) (Finset.mem_insert_self _ _)
      _ = ∏ᶠ j, f j :=
        (finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert _ _)).symm
      
#align single_le_finprod single_le_finprod
#align single_le_finsum single_le_finsum

/- warning: finprod_eq_zero -> finprod_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M₀ : Type.{u2}} [_inst_3 : CommMonoidWithZero.{u2} M₀] (f : α -> M₀) (x : α), (Eq.{succ u2} M₀ (f x) (OfNat.ofNat.{u2} M₀ 0 (OfNat.mk.{u2} M₀ 0 (Zero.zero.{u2} M₀ (MulZeroClass.toHasZero.{u2} M₀ (MulZeroOneClass.toMulZeroClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ (CommMonoidWithZero.toMonoidWithZero.{u2} M₀ _inst_3)))))))) -> (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M₀ (MulOneClass.toHasOne.{u2} M₀ (MulZeroOneClass.toMulOneClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ (CommMonoidWithZero.toMonoidWithZero.{u2} M₀ _inst_3)))) f)) -> (Eq.{succ u2} M₀ (finprod.{u2, succ u1} M₀ α (CommMonoidWithZero.toCommMonoid.{u2} M₀ _inst_3) (fun (x : α) => f x)) (OfNat.ofNat.{u2} M₀ 0 (OfNat.mk.{u2} M₀ 0 (Zero.zero.{u2} M₀ (MulZeroClass.toHasZero.{u2} M₀ (MulZeroOneClass.toMulZeroClass.{u2} M₀ (MonoidWithZero.toMulZeroOneClass.{u2} M₀ (CommMonoidWithZero.toMonoidWithZero.{u2} M₀ _inst_3))))))))
but is expected to have type
  forall {α : Type.{u1}} {M₀ : Type.{u2}} [_inst_3 : CommMonoidWithZero.{u2} M₀] (f : α -> M₀) (x : α), (Eq.{succ u2} M₀ (f x) (OfNat.ofNat.{u2} M₀ 0 (Zero.toOfNat0.{u2} M₀ (CommMonoidWithZero.toZero.{u2} M₀ _inst_3)))) -> (Set.Finite.{u1} α (Function.mulSupport.{u1, u2} α M₀ (Monoid.toOne.{u2} M₀ (MonoidWithZero.toMonoid.{u2} M₀ (CommMonoidWithZero.toMonoidWithZero.{u2} M₀ _inst_3))) f)) -> (Eq.{succ u2} M₀ (finprod.{u2, succ u1} M₀ α (CommMonoidWithZero.toCommMonoid.{u2} M₀ _inst_3) (fun (x : α) => f x)) (OfNat.ofNat.{u2} M₀ 0 (Zero.toOfNat0.{u2} M₀ (CommMonoidWithZero.toZero.{u2} M₀ _inst_3))))
Case conversion may be inaccurate. Consider using '#align finprod_eq_zero finprod_eq_zeroₓ'. -/
theorem finprod_eq_zero {M₀ : Type _} [CommMonoidWithZero M₀] (f : α → M₀) (x : α) (hx : f x = 0)
    (hf : (mulSupport f).Finite) : (∏ᶠ x, f x) = 0 :=
  by
  nontriviality
  rw [finprod_eq_prod f hf]
  refine' Finset.prod_eq_zero (hf.mem_to_finset.2 _) hx
  simp [hx]
#align finprod_eq_zero finprod_eq_zero

/- warning: finprod_prod_comm -> finprod_prod_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (s : Finset.{u2} β) (f : α -> β -> M), (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (Set.Finite.{u1} α (Function.mulSupport.{u1, u3} α M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (fun (a : α) => f a b)))) -> (Eq.{succ u3} M (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => Finset.prod.{u3, u2} M β _inst_1 s (fun (b : β) => f a b))) (Finset.prod.{u3, u2} M β _inst_1 s (fun (b : β) => finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => f a b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (s : Finset.{u3} β) (f : α -> β -> M), (forall (b : β), (Membership.mem.{u3, u3} β (Finset.{u3} β) (Finset.instMembershipFinset.{u3} β) b s) -> (Set.Finite.{u2} α (Function.mulSupport.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (fun (a : α) => f a b)))) -> (Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => Finset.prod.{u1, u3} M β _inst_1 s (fun (b : β) => f a b))) (Finset.prod.{u1, u3} M β _inst_1 s (fun (b : β) => finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => f a b))))
Case conversion may be inaccurate. Consider using '#align finprod_prod_comm finprod_prod_commₓ'. -/
@[to_additive]
theorem finprod_prod_comm (s : Finset β) (f : α → β → M)
    (h : ∀ b ∈ s, (mulSupport fun a => f a b).Finite) :
    (∏ᶠ a : α, ∏ b in s, f a b) = ∏ b in s, ∏ᶠ a : α, f a b :=
  by
  have hU :
    (mul_support fun a => ∏ b in s, f a b) ⊆
      (s.finite_to_set.bUnion fun b hb => h b (Finset.mem_coe.1 hb)).toFinset :=
    by
    rw [finite.coe_to_finset]
    intro x hx
    simp only [exists_prop, mem_Union, Ne.def, mem_mul_support, Finset.mem_coe]
    contrapose! hx
    rw [mem_mul_support, Classical.not_not, Finset.prod_congr rfl hx, Finset.prod_const_one]
  rw [finprod_eq_prod_of_mulSupport_subset _ hU, Finset.prod_comm]
  refine' Finset.prod_congr rfl fun b hb => (finprod_eq_prod_of_mulSupport_subset _ _).symm
  intro a ha
  simp only [finite.coe_to_finset, mem_Union]
  exact ⟨b, hb, ha⟩
#align finprod_prod_comm finprod_prod_comm
#align finsum_sum_comm finsum_sum_comm

/- warning: prod_finprod_comm -> prod_finprod_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (s : Finset.{u1} α) (f : α -> β -> M), (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Set.Finite.{u2} β (Function.mulSupport.{u2, u3} β M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (f a)))) -> (Eq.{succ u3} M (Finset.prod.{u3, u1} M α _inst_1 s (fun (a : α) => finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => f a b))) (finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => Finset.prod.{u3, u1} M α _inst_1 s (fun (a : α) => f a b))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (s : Finset.{u3} α) (f : α -> β -> M), (forall (a : α), (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) -> (Set.Finite.{u2} β (Function.mulSupport.{u2, u1} β M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (f a)))) -> (Eq.{succ u1} M (Finset.prod.{u1, u3} M α _inst_1 s (fun (a : α) => finprod.{u1, succ u2} M β _inst_1 (fun (b : β) => f a b))) (finprod.{u1, succ u2} M β _inst_1 (fun (b : β) => Finset.prod.{u1, u3} M α _inst_1 s (fun (a : α) => f a b))))
Case conversion may be inaccurate. Consider using '#align prod_finprod_comm prod_finprod_commₓ'. -/
@[to_additive]
theorem prod_finprod_comm (s : Finset α) (f : α → β → M) (h : ∀ a ∈ s, (mulSupport (f a)).Finite) :
    (∏ a in s, ∏ᶠ b : β, f a b) = ∏ᶠ b : β, ∏ a in s, f a b :=
  (finprod_prod_comm s (fun b a => f a b) h).symm
#align prod_finprod_comm prod_finprod_comm
#align sum_finsum_comm sum_finsum_comm

/- warning: mul_finsum -> mul_finsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_3 : Semiring.{u2} R] (f : α -> R) (r : R), (Set.Finite.{u1} α (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3)))) f)) -> (Eq.{succ u2} R (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))))) r (finsum.{u2, succ u1} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))) (fun (a : α) => f a))) (finsum.{u2, succ u1} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))) (fun (a : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))))) r (f a))))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_3 : Semiring.{u2} R] (f : α -> R) (r : R), (Set.Finite.{u1} α (Function.support.{u1, u2} α R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3)) f)) -> (Eq.{succ u2} R (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3)))) r (finsum.{u2, succ u1} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))) (fun (a : α) => f a))) (finsum.{u2, succ u1} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))) (fun (a : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3)))) r (f a))))
Case conversion may be inaccurate. Consider using '#align mul_finsum mul_finsumₓ'. -/
theorem mul_finsum {R : Type _} [Semiring R] (f : α → R) (r : R) (h : (support f).Finite) :
    (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a :=
  (AddMonoidHom.mulLeft r).map_finsum h
#align mul_finsum mul_finsum

/- warning: finsum_mul -> finsum_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_3 : Semiring.{u2} R] (f : α -> R) (r : R), (Set.Finite.{u1} α (Function.support.{u1, u2} α R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3)))) f)) -> (Eq.{succ u2} R (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))))) (finsum.{u2, succ u1} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))) (fun (a : α) => f a)) r) (finsum.{u2, succ u1} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))) (fun (a : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))))) (f a) r)))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_3 : Semiring.{u2} R] (f : α -> R) (r : R), (Set.Finite.{u1} α (Function.support.{u1, u2} α R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3)) f)) -> (Eq.{succ u2} R (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3)))) (finsum.{u2, succ u1} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))) (fun (a : α) => f a)) r) (finsum.{u2, succ u1} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))) (fun (a : α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3)))) (f a) r)))
Case conversion may be inaccurate. Consider using '#align finsum_mul finsum_mulₓ'. -/
theorem finsum_mul {R : Type _} [Semiring R] (f : α → R) (r : R) (h : (support f).Finite) :
    (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r :=
  (AddMonoidHom.mulRight r).map_finsum h
#align finsum_mul finsum_mul

/- warning: finset.mul_support_of_fiberwise_prod_subset_image -> Finset.mulSupport_of_fiberwise_prod_subset_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] [_inst_3 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> M) (g : α -> β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Function.mulSupport.{u2, u3} β M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (fun (b : β) => Finset.prod.{u3, u1} M α _inst_1 (Finset.filter.{u1} α (fun (a : α) => Eq.{succ u2} β (g a) b) (fun (a : α) => _inst_3 (g a) b) s) f)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_3 a b) g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] [_inst_3 : DecidableEq.{succ u3} β] (s : Finset.{u2} α) (f : α -> M) (g : α -> β), HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (Function.mulSupport.{u3, u1} β M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (fun (b : β) => Finset.prod.{u1, u2} M α _inst_1 (Finset.filter.{u2} α (fun (a : α) => Eq.{succ u3} β (g a) b) (fun (a : α) => _inst_3 (g a) b) s) f)) (Finset.toSet.{u3} β (Finset.image.{u2, u3} α β (fun (a : β) (b : β) => _inst_3 a b) g s))
Case conversion may be inaccurate. Consider using '#align finset.mul_support_of_fiberwise_prod_subset_image Finset.mulSupport_of_fiberwise_prod_subset_imageₓ'. -/
@[to_additive]
theorem Finset.mulSupport_of_fiberwise_prod_subset_image [DecidableEq β] (s : Finset α) (f : α → M)
    (g : α → β) : (mulSupport fun b => (s.filterₓ fun a => g a = b).Prod f) ⊆ s.image g :=
  by
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Function.support_subset_iff]
  intro b h
  suffices (s.filter fun a : α => g a = b).Nonempty by
    simpa only [s.fiber_nonempty_iff_mem_image g b, Finset.mem_image, exists_prop]
  exact Finset.nonempty_of_prod_ne_one h
#align finset.mul_support_of_fiberwise_prod_subset_image Finset.mulSupport_of_fiberwise_prod_subset_image
#align finset.support_of_fiberwise_sum_subset_image Finset.support_of_fiberwise_sum_subset_image

/- warning: finprod_mem_finset_product' -> finprod_mem_finset_product' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : DecidableEq.{succ u2} β] (s : Finset.{max u1 u2} (Prod.{u1, u2} α β)) (f : (Prod.{u1, u2} α β) -> M), Eq.{succ u3} M (finprod.{u3, succ (max u1 u2)} M (Prod.{u1, u2} α β) _inst_1 (fun (ab : Prod.{u1, u2} α β) => finprod.{u3, 0} M (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) ab s) _inst_1 (fun (h : Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) ab s) => f ab))) (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => finprod.{u3, 0} M (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (fun (a : β) (b : β) => _inst_4 a b) (Prod.snd.{u1, u2} α β) (Finset.filter.{max u1 u2} (Prod.{u1, u2} α β) (fun (ab : Prod.{u1, u2} α β) => Eq.{succ u1} α (Prod.fst.{u1, u2} α β ab) a) (fun (a_1 : Prod.{u1, u2} α β) => _inst_3 (Prod.fst.{u1, u2} α β a_1) a) s))) _inst_1 (fun (h : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (fun (a : β) (b : β) => _inst_4 a b) (Prod.snd.{u1, u2} α β) (Finset.filter.{max u1 u2} (Prod.{u1, u2} α β) (fun (ab : Prod.{u1, u2} α β) => Eq.{succ u1} α (Prod.fst.{u1, u2} α β ab) a) (fun (a_1 : Prod.{u1, u2} α β) => _inst_3 (Prod.fst.{u1, u2} α β a_1) a) s))) => f (Prod.mk.{u1, u2} α β a b)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] [_inst_3 : DecidableEq.{succ u3} α] [_inst_4 : DecidableEq.{succ u2} β] (s : Finset.{max u2 u3} (Prod.{u3, u2} α β)) (f : (Prod.{u3, u2} α β) -> M), Eq.{succ u1} M (finprod.{u1, succ (max u3 u2)} M (Prod.{u3, u2} α β) _inst_1 (fun (ab : Prod.{u3, u2} α β) => finprod.{u1, 0} M (Membership.mem.{max u3 u2, max u3 u2} (Prod.{u3, u2} α β) (Finset.{max u2 u3} (Prod.{u3, u2} α β)) (Finset.instMembershipFinset.{max u3 u2} (Prod.{u3, u2} α β)) ab s) _inst_1 (fun (h : Membership.mem.{max u3 u2, max u3 u2} (Prod.{u3, u2} α β) (Finset.{max u2 u3} (Prod.{u3, u2} α β)) (Finset.instMembershipFinset.{max u3 u2} (Prod.{u3, u2} α β)) ab s) => f ab))) (finprod.{u1, succ u3} M α _inst_1 (fun (a : α) => finprod.{u1, succ u2} M β _inst_1 (fun (b : β) => finprod.{u1, 0} M (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.image.{max u2 u3, u2} (Prod.{u3, u2} α β) β (fun (a : β) (b : β) => _inst_4 a b) (Prod.snd.{u3, u2} α β) (Finset.filter.{max u2 u3} (Prod.{u3, u2} α β) (fun (ab : Prod.{u3, u2} α β) => Eq.{succ u3} α (Prod.fst.{u3, u2} α β ab) a) (fun (a_1 : Prod.{u3, u2} α β) => _inst_3 (Prod.fst.{u3, u2} α β a_1) a) s))) _inst_1 (fun (h : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.image.{max u2 u3, u2} (Prod.{u3, u2} α β) β (fun (a : β) (b : β) => _inst_4 a b) (Prod.snd.{u3, u2} α β) (Finset.filter.{max u2 u3} (Prod.{u3, u2} α β) (fun (ab : Prod.{u3, u2} α β) => Eq.{succ u3} α (Prod.fst.{u3, u2} α β ab) a) (fun (a_1 : Prod.{u3, u2} α β) => _inst_3 (Prod.fst.{u3, u2} α β a_1) a) s))) => f (Prod.mk.{u3, u2} α β a b)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_finset_product' finprod_mem_finset_product'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/-- Note that `b ∈ (s.filter (λ ab, prod.fst ab = a)).image prod.snd` iff `(a, b) ∈ s` so we can
simplify the right hand side of this lemma. However the form stated here is more useful for
iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/
@[to_additive
      "Note that `b ∈ (s.filter (λ ab, prod.fst ab = a)).image prod.snd` iff `(a, b) ∈ s` so\nwe can simplify the right hand side of this lemma. However the form stated here is more useful for\niterating this lemma, e.g., if we have `f : α × β × γ → M`."]
theorem finprod_mem_finset_product' [DecidableEq α] [DecidableEq β] (s : Finset (α × β))
    (f : α × β → M) :
    (∏ᶠ (ab) (h : ab ∈ s), f ab) =
      ∏ᶠ (a) (b) (h : b ∈ (s.filterₓ fun ab => Prod.fst ab = a).image Prod.snd), f (a, b) :=
  by
  have :
    ∀ a,
      (∏ i : β in (s.filter fun ab => Prod.fst ab = a).image Prod.snd, f (a, i)) =
        (Finset.filter (fun ab => Prod.fst ab = a) s).Prod f :=
    by
    refine' fun a => Finset.prod_bij (fun b _ => (a, b)) _ _ _ _ <;>-- `finish` closes these goals
      try simp; done
    suffices ∀ a' b, (a', b) ∈ s → a' = a → (a, b) ∈ s ∧ a' = a by simpa
    rintro a' b hp rfl
    exact ⟨hp, rfl⟩
  rw [finprod_mem_finset_eq_prod]
  simp_rw [finprod_mem_finset_eq_prod, this]
  rw [finprod_eq_prod_of_mulSupport_subset _
      (s.mul_support_of_fiberwise_prod_subset_image f Prod.fst),
    ← Finset.prod_fiberwise_of_maps_to _ f]
  -- `finish` could close the goal here
  simp only [Finset.mem_image, Prod.mk.eta]
  exact fun x hx => ⟨x, hx, rfl⟩
#align finprod_mem_finset_product' finprod_mem_finset_product'
#align finsum_mem_finset_product' finsum_mem_finset_product'

/- warning: finprod_mem_finset_product -> finprod_mem_finset_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (s : Finset.{max u1 u2} (Prod.{u1, u2} α β)) (f : (Prod.{u1, u2} α β) -> M), Eq.{succ u3} M (finprod.{u3, succ (max u1 u2)} M (Prod.{u1, u2} α β) _inst_1 (fun (ab : Prod.{u1, u2} α β) => finprod.{u3, 0} M (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) ab s) _inst_1 (fun (h : Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) ab s) => f ab))) (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => finprod.{u3, 0} M (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) s) _inst_1 (fun (h : Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) s) => f (Prod.mk.{u1, u2} α β a b)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (s : Finset.{max u3 u2} (Prod.{u2, u3} α β)) (f : (Prod.{u2, u3} α β) -> M), Eq.{succ u1} M (finprod.{u1, succ (max u2 u3)} M (Prod.{u2, u3} α β) _inst_1 (fun (ab : Prod.{u2, u3} α β) => finprod.{u1, 0} M (Membership.mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} α β) (Finset.{max u3 u2} (Prod.{u2, u3} α β)) (Finset.instMembershipFinset.{max u2 u3} (Prod.{u2, u3} α β)) ab s) _inst_1 (fun (h : Membership.mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} α β) (Finset.{max u3 u2} (Prod.{u2, u3} α β)) (Finset.instMembershipFinset.{max u2 u3} (Prod.{u2, u3} α β)) ab s) => f ab))) (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, succ u3} M β _inst_1 (fun (b : β) => finprod.{u1, 0} M (Membership.mem.{max u3 u2, max u2 u3} (Prod.{u2, u3} α β) (Finset.{max u3 u2} (Prod.{u2, u3} α β)) (Finset.instMembershipFinset.{max u3 u2} (Prod.{u2, u3} α β)) (Prod.mk.{u2, u3} α β a b) s) _inst_1 (fun (h : Membership.mem.{max u3 u2, max u2 u3} (Prod.{u2, u3} α β) (Finset.{max u3 u2} (Prod.{u2, u3} α β)) (Finset.instMembershipFinset.{max u3 u2} (Prod.{u2, u3} α β)) (Prod.mk.{u2, u3} α β a b) s) => f (Prod.mk.{u2, u3} α β a b)))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_finset_product finprod_mem_finset_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/-- See also `finprod_mem_finset_product'`. -/
@[to_additive "See also `finsum_mem_finset_product'`."]
theorem finprod_mem_finset_product (s : Finset (α × β)) (f : α × β → M) :
    (∏ᶠ (ab) (h : ab ∈ s), f ab) = ∏ᶠ (a) (b) (h : (a, b) ∈ s), f (a, b) := by
  classical
    rw [finprod_mem_finset_product']
    simp
#align finprod_mem_finset_product finprod_mem_finset_product
#align finsum_mem_finset_product finsum_mem_finset_product

/- warning: finprod_mem_finset_product₃ -> finprod_mem_finset_product₃ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {γ : Type.{u4}} (s : Finset.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) (f : (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) -> M), Eq.{succ u3} M (finprod.{u3, succ (max u1 u2 u4)} M (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) _inst_1 (fun (abc : Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) => finprod.{u3, 0} M (Membership.Mem.{max u1 u2 u4, max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) (Finset.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) (Finset.hasMem.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) abc s) _inst_1 (fun (h : Membership.Mem.{max u1 u2 u4, max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) (Finset.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) (Finset.hasMem.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) abc s) => f abc))) (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => finprod.{u3, succ u4} M γ _inst_1 (fun (c : γ) => finprod.{u3, 0} M (Membership.Mem.{max u1 u2 u4, max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) (Finset.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) (Finset.hasMem.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) (Prod.mk.{u1, max u2 u4} α (Prod.{u2, u4} β γ) a (Prod.mk.{u2, u4} β γ b c)) s) _inst_1 (fun (h : Membership.Mem.{max u1 u2 u4, max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) (Finset.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) (Finset.hasMem.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ))) (Prod.mk.{u1, max u2 u4} α (Prod.{u2, u4} β γ) a (Prod.mk.{u2, u4} β γ b c)) s) => f (Prod.mk.{u1, max u2 u4} α (Prod.{u2, u4} β γ) a (Prod.mk.{u2, u4} β γ b c)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {γ : Type.{u4}} (s : Finset.{max (max u4 u3) u2} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) (f : (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ)) -> M), Eq.{succ u1} M (finprod.{u1, succ (max (max u2 u3) u4)} M (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ)) _inst_1 (fun (abc : Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ)) => finprod.{u1, 0} M (Membership.mem.{max (max u2 u3) u4, max (max u2 u3) u4} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ)) (Finset.{max (max u4 u3) u2} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) (Finset.instMembershipFinset.{max (max u2 u3) u4} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) abc s) _inst_1 (fun (h : Membership.mem.{max (max u2 u3) u4, max (max u2 u3) u4} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ)) (Finset.{max (max u4 u3) u2} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) (Finset.instMembershipFinset.{max (max u2 u3) u4} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) abc s) => f abc))) (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, succ u3} M β _inst_1 (fun (b : β) => finprod.{u1, succ u4} M γ _inst_1 (fun (c : γ) => finprod.{u1, 0} M (Membership.mem.{max (max u4 u3) u2, max (max u2 u3) u4} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ)) (Finset.{max (max u4 u3) u2} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) (Finset.instMembershipFinset.{max (max u2 u4) u3} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) (Prod.mk.{u2, max u4 u3} α (Prod.{u3, u4} β γ) a (Prod.mk.{u3, u4} β γ b c)) s) _inst_1 (fun (h : Membership.mem.{max (max u4 u3) u2, max (max u2 u3) u4} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ)) (Finset.{max (max u4 u3) u2} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) (Finset.instMembershipFinset.{max (max u2 u4) u3} (Prod.{u2, max u4 u3} α (Prod.{u3, u4} β γ))) (Prod.mk.{u2, max u4 u3} α (Prod.{u3, u4} β γ) a (Prod.mk.{u3, u4} β γ b c)) s) => f (Prod.mk.{u2, max u3 u4} α (Prod.{u3, u4} β γ) a (Prod.mk.{u3, u4} β γ b c)))))))
Case conversion may be inaccurate. Consider using '#align finprod_mem_finset_product₃ finprod_mem_finset_product₃ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b c) -/
@[to_additive]
theorem finprod_mem_finset_product₃ {γ : Type _} (s : Finset (α × β × γ)) (f : α × β × γ → M) :
    (∏ᶠ (abc) (h : abc ∈ s), f abc) = ∏ᶠ (a) (b) (c) (h : (a, b, c) ∈ s), f (a, b, c) := by
  classical
    rw [finprod_mem_finset_product']
    simp_rw [finprod_mem_finset_product']
    simp
#align finprod_mem_finset_product₃ finprod_mem_finset_product₃
#align finsum_mem_finset_product₃ finsum_mem_finset_product₃

/- warning: finprod_curry -> finprod_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (f : (Prod.{u1, u2} α β) -> M), (Set.Finite.{max u1 u2} (Prod.{u1, u2} α β) (Function.mulSupport.{max u1 u2, u3} (Prod.{u1, u2} α β) M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) f)) -> (Eq.{succ u3} M (finprod.{u3, max (succ u1) (succ u2)} M (Prod.{u1, u2} α β) _inst_1 (fun (ab : Prod.{u1, u2} α β) => f ab)) (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => f (Prod.mk.{u1, u2} α β a b)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : (Prod.{u3, u2} α β) -> M), (Set.Finite.{max u3 u2} (Prod.{u3, u2} α β) (Function.mulSupport.{max u3 u2, u1} (Prod.{u3, u2} α β) M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) -> (Eq.{succ u1} M (finprod.{u1, max (succ u3) (succ u2)} M (Prod.{u3, u2} α β) _inst_1 (fun (ab : Prod.{u3, u2} α β) => f ab)) (finprod.{u1, succ u3} M α _inst_1 (fun (a : α) => finprod.{u1, succ u2} M β _inst_1 (fun (b : β) => f (Prod.mk.{u3, u2} α β a b)))))
Case conversion may be inaccurate. Consider using '#align finprod_curry finprod_curryₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
@[to_additive]
theorem finprod_curry (f : α × β → M) (hf : (mulSupport f).Finite) :
    (∏ᶠ ab, f ab) = ∏ᶠ (a) (b), f (a, b) :=
  by
  have h₁ : ∀ a, (∏ᶠ h : a ∈ hf.to_finset, f a) = f a := by simp
  have h₂ : (∏ᶠ a, f a) = ∏ᶠ (a) (h : a ∈ hf.to_finset), f a := by simp
  simp_rw [h₂, finprod_mem_finset_product, h₁]
#align finprod_curry finprod_curry
#align finsum_curry finsum_curry

/- warning: finprod_curry₃ -> finprod_curry₃ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {γ : Type.{u4}} (f : (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) -> M), (Set.Finite.{max u1 u2 u4} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) (Function.mulSupport.{max u1 u2 u4, u3} (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) f)) -> (Eq.{succ u3} M (finprod.{u3, max (succ u1) (succ (max u2 u4))} M (Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) _inst_1 (fun (abc : Prod.{u1, max u2 u4} α (Prod.{u2, u4} β γ)) => f abc)) (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => finprod.{u3, succ u4} M γ _inst_1 (fun (c : γ) => f (Prod.mk.{u1, max u2 u4} α (Prod.{u2, u4} β γ) a (Prod.mk.{u2, u4} β γ b c)))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {γ : Type.{u4}} (f : (Prod.{u3, max u4 u2} α (Prod.{u2, u4} β γ)) -> M), (Set.Finite.{max (max u3 u2) u4} (Prod.{u3, max u4 u2} α (Prod.{u2, u4} β γ)) (Function.mulSupport.{max (max u3 u2) u4, u1} (Prod.{u3, max u4 u2} α (Prod.{u2, u4} β γ)) M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) f)) -> (Eq.{succ u1} M (finprod.{u1, max (max (succ u3) (succ u2)) (succ u4)} M (Prod.{u3, max u4 u2} α (Prod.{u2, u4} β γ)) _inst_1 (fun (abc : Prod.{u3, max u4 u2} α (Prod.{u2, u4} β γ)) => f abc)) (finprod.{u1, succ u3} M α _inst_1 (fun (a : α) => finprod.{u1, succ u2} M β _inst_1 (fun (b : β) => finprod.{u1, succ u4} M γ _inst_1 (fun (c : γ) => f (Prod.mk.{u3, max u2 u4} α (Prod.{u2, u4} β γ) a (Prod.mk.{u2, u4} β γ b c)))))))
Case conversion may be inaccurate. Consider using '#align finprod_curry₃ finprod_curry₃ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b c) -/
@[to_additive]
theorem finprod_curry₃ {γ : Type _} (f : α × β × γ → M) (h : (mulSupport f).Finite) :
    (∏ᶠ abc, f abc) = ∏ᶠ (a) (b) (c), f (a, b, c) :=
  by
  rw [finprod_curry f h]
  congr
  ext a
  rw [finprod_curry]
  simp [h]
#align finprod_curry₃ finprod_curry₃
#align finsum_curry₃ finsum_curry₃

/- warning: finprod_dmem -> finprod_dmem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {s : Set.{u1} α} [_inst_3 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)] (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> M), Eq.{succ u2} M (finprod.{u2, succ u1} M α _inst_1 (fun (a : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) _inst_1 (fun (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a h))) (finprod.{u2, succ u1} M α _inst_1 (fun (a : α) => finprod.{u2, 0} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) _inst_1 (fun (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => dite.{succ u2} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (_inst_3 a) (fun (h' : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a h') (fun (h' : Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) => OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {s : Set.{u2} α} [_inst_3 : DecidablePred.{succ u2} α (fun (_x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) _x s)] (f : forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> M), Eq.{succ u1} M (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) _inst_1 (fun (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => f a h))) (finprod.{u1, succ u2} M α _inst_1 (fun (a : α) => finprod.{u1, 0} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) _inst_1 (fun (h : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => dite.{succ u1} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (_inst_3 a) (fun (h' : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => f a h') (fun (h' : Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align finprod_dmem finprod_dmemₓ'. -/
@[to_additive]
theorem finprod_dmem {s : Set α} [DecidablePred (· ∈ s)] (f : ∀ a : α, a ∈ s → M) :
    (∏ᶠ (a : α) (h : a ∈ s), f a h) = ∏ᶠ (a : α) (h : a ∈ s), if h' : a ∈ s then f a h' else 1 :=
  finprod_congr fun a => finprod_congr fun ha => (dif_pos ha).symm
#align finprod_dmem finprod_dmem
#align finsum_dmem finsum_dmem

/- warning: finprod_emb_domain' -> finprod_emb_domain' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall [_inst_3 : DecidablePred.{succ u2} β (fun (_x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) _x (Set.range.{u2, succ u1} β α f))] (g : α -> M), Eq.{succ u3} M (finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => dite.{succ u3} M (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α f)) (_inst_3 b) (fun (h : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α f)) => g (Classical.choose.{succ u1} α (fun (y : α) => Eq.{succ u2} β (f y) b) h)) (fun (h : Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α f))) => OfNat.ofNat.{u3} M 1 (OfNat.mk.{u3} M 1 (One.one.{u3} M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)))))))) (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => g a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {f : α -> β}, (Function.Injective.{succ u3, succ u2} α β f) -> (forall [_inst_3 : DecidablePred.{succ u2} β (fun (_x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) _x (Set.range.{u2, succ u3} β α f))] (g : α -> M), Eq.{succ u1} M (finprod.{u1, succ u2} M β _inst_1 (fun (b : β) => dite.{succ u1} M (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, succ u3} β α f)) (_inst_3 b) (fun (h : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, succ u3} β α f)) => g (Classical.choose.{succ u3} α (fun (y : α) => Eq.{succ u2} β (f y) b) h)) (fun (h : Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, succ u3} β α f))) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))) (finprod.{u1, succ u3} M α _inst_1 (fun (a : α) => g a)))
Case conversion may be inaccurate. Consider using '#align finprod_emb_domain' finprod_emb_domain'ₓ'. -/
@[to_additive]
theorem finprod_emb_domain' {f : α → β} (hf : Injective f) [DecidablePred (· ∈ Set.range f)]
    (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a :=
  by
  simp_rw [← finprod_eq_dif]
  rw [finprod_dmem, finprod_mem_range hf, finprod_congr fun a => _]
  rw [dif_pos (Set.mem_range_self a), hf (Classical.choose_spec (Set.mem_range_self a))]
#align finprod_emb_domain' finprod_emb_domain'
#align finsum_emb_domain' finsum_emb_domain'

/- warning: finprod_emb_domain -> finprod_emb_domain is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (f : Function.Embedding.{succ u1, succ u2} α β) [_inst_3 : DecidablePred.{succ u2} β (fun (_x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) _x (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f)))] (g : α -> M), Eq.{succ u3} M (finprod.{u3, succ u2} M β _inst_1 (fun (b : β) => dite.{succ u3} M (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) (_inst_3 b) (fun (h : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) => g (Classical.choose.{succ u1} α (fun (y : α) => Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f y) b) h)) (fun (h : Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f)))) => OfNat.ofNat.{u3} M 1 (OfNat.mk.{u3} M 1 (One.one.{u3} M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1)))))))) (finprod.{u3, succ u1} M α _inst_1 (fun (a : α) => g a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : Function.Embedding.{succ u3, succ u2} α β) [_inst_3 : DecidablePred.{succ u2} β (fun (_x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) _x (Set.range.{u2, succ u3} β α (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f)))] (g : α -> M), Eq.{succ u1} M (finprod.{u1, succ u2} M β _inst_1 (fun (b : β) => dite.{succ u1} M (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, succ u3} β α (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f))) (_inst_3 b) (fun (h : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, succ u3} β α (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f))) => g (Classical.choose.{succ u3} α (fun (y : α) => Eq.{succ u2} β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f y) b) h)) (fun (h : Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, succ u3} β α (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f)))) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))))) (finprod.{u1, succ u3} M α _inst_1 (fun (a : α) => g a))
Case conversion may be inaccurate. Consider using '#align finprod_emb_domain finprod_emb_domainₓ'. -/
@[to_additive]
theorem finprod_emb_domain (f : α ↪ β) [DecidablePred (· ∈ Set.range f)] (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a :=
  finprod_emb_domain' f.Injective g
#align finprod_emb_domain finprod_emb_domain
#align finsum_emb_domain finsum_emb_domain

end Type

