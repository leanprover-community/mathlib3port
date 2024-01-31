/-
Copyright (c) 2022 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import GroupTheory.OrderOfElement
import Data.Finset.NoncommProd
import Data.Fintype.BigOperators
import Data.Nat.Gcd.BigOperators
import Order.SupIndep

#align_import group_theory.noncomm_pi_coprod from "leanprover-community/mathlib"@"ef7acf407d265ad4081c8998687e994fa80ba70c"

/-!
# Canonical homomorphism from a finite family of monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the construction of the canonical homomorphism from a family of monoids.

Given a family of morphisms `ϕ i : N i →* M` for each `i : ι` where elements in the
images of different morphisms commute, we obtain a canonical morphism
`monoid_hom.noncomm_pi_coprod : (Π i, N i) →* M` that coincides with `ϕ`

## Main definitions

* `monoid_hom.noncomm_pi_coprod : (Π i, N i) →* M` is the main homomorphism
* `subgroup.noncomm_pi_coprod : (Π i, H i) →* G` is the specialization to `H i : subgroup G`
   and the subgroup embedding.

## Main theorems

* `monoid_hom.noncomm_pi_coprod` coincides with `ϕ i` when restricted to `N i`
* `monoid_hom.noncomm_pi_coprod_mrange`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : ι), (ϕ i).mrange`
* `monoid_hom.noncomm_pi_coprod_range`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : ι), (ϕ i).range`
* `subgroup.noncomm_pi_coprod_range`: The range of `subgroup.noncomm_pi_coprod` is `⨆ (i : ι), H i`.
* `monoid_hom.injective_noncomm_pi_coprod_of_independent`: in the case of groups, `pi_hom.hom` is
   injective if the `ϕ` are injective and the ranges of the `ϕ` are independent.
* `monoid_hom.independent_range_of_coprime_order`: If the `N i` have coprime orders, then the ranges
   of the `ϕ` are independent.
* `subgroup.independent_of_coprime_order`: If commuting normal subgroups `H i` have coprime orders,
   they are independent.

-/


open scoped BigOperators

namespace Subgroup

variable {G : Type _} [Group G]

#print Subgroup.eq_one_of_noncommProd_eq_one_of_independent /-
/-- `finset.noncomm_prod` is “injective” in `f` if `f` maps into independent subgroups.  This
generalizes (one direction of) `subgroup.disjoint_iff_mul_eq_one`. -/
@[to_additive
      "`finset.noncomm_sum` is “injective” in `f` if `f` maps into independent subgroups.\nThis generalizes (one direction of) `add_subgroup.disjoint_iff_add_eq_zero`. "]
theorem eq_one_of_noncommProd_eq_one_of_independent {ι : Type _} (s : Finset ι) (f : ι → G) (comm)
    (K : ι → Subgroup G) (hind : CompleteLattice.Independent K) (hmem : ∀ x ∈ s, f x ∈ K x)
    (heq1 : s.noncommProd f comm = 1) : ∀ i ∈ s, f i = 1 := by classical
#align subgroup.eq_one_of_noncomm_prod_eq_one_of_independent Subgroup.eq_one_of_noncommProd_eq_one_of_independent
#align add_subgroup.eq_zero_of_noncomm_sum_eq_zero_of_independent AddSubgroup.eq_zero_of_noncommSum_eq_zero_of_independent
-/

end Subgroup

section FamilyOfMonoids

variable {M : Type _} [Monoid M]

-- We have a family of monoids
-- The fintype assumption is not always used, but declared here, to keep things in order
variable {ι : Type _} [hdec : DecidableEq ι] [Fintype ι]

variable {N : ι → Type _} [∀ i, Monoid (N i)]

-- And morphisms ϕ into G
variable (ϕ : ∀ i : ι, N i →* M)

-- We assume that the elements of different morphism commute
variable (hcomm : Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y))

-- We use `f` and `g` to denote elements of `Π (i : ι), N i`
variable (f g : ∀ i : ι, N i)

namespace MonoidHom

#print MonoidHom.noncommPiCoprod /-
/-- The canonical homomorphism from a family of monoids. -/
@[to_additive
      "The canonical homomorphism from a family of additive monoids.\n\nSee also `linear_map.lsum` for a linear version without the commutativity assumption."]
def noncommPiCoprod : (∀ i : ι, N i) →* M
    where
  toFun f := Finset.univ.noncommProd (fun i => ϕ i (f i)) fun i _ j _ h => hcomm h _ _
  map_one' := by apply (Finset.noncommProd_eq_pow_card _ _ _ _ _).trans (one_pow _); simp
  map_mul' f g := by classical
#align monoid_hom.noncomm_pi_coprod MonoidHom.noncommPiCoprod
#align add_monoid_hom.noncomm_pi_coprod AddMonoidHom.noncommPiCoprod
-/

variable {hcomm}

#print MonoidHom.noncommPiCoprod_mulSingle /-
@[simp, to_additive]
theorem noncommPiCoprod_mulSingle (i : ι) (y : N i) :
    noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y :=
  by
  change finset.univ.noncomm_prod (fun j => ϕ j (Pi.mulSingle i y j)) _ = ϕ i y
  simp (config := { singlePass := true }) only [← Finset.insert_erase (Finset.mem_univ i)]
  rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ (Finset.not_mem_erase i _)]
  rw [Pi.mulSingle_eq_same]
  rw [Finset.noncommProd_eq_pow_card]
  · rw [one_pow]; exact mul_one _
  · intro j hj; simp only [Finset.mem_erase] at hj ; simp [hj]
#align monoid_hom.noncomm_pi_coprod_mul_single MonoidHom.noncommPiCoprod_mulSingle
#align add_monoid_hom.noncomm_pi_coprod_single AddMonoidHom.noncommPiCoprod_single
-/

#print MonoidHom.noncommPiCoprodEquiv /-
/-- The universal property of `noncomm_pi_coprod` -/
@[to_additive "The universal property of `noncomm_pi_coprod`"]
def noncommPiCoprodEquiv :
    { ϕ : ∀ i, N i →* M // Pairwise fun i j => ∀ x y, Commute (ϕ i x) (ϕ j y) } ≃ ((∀ i, N i) →* M)
    where
  toFun ϕ := noncommPiCoprod ϕ.1 ϕ.2
  invFun f :=
    ⟨fun i => f.comp (MonoidHom.single N i), fun i j hij x y =>
      Commute.map (Pi.mulSingle_commute hij x y) f⟩
  left_inv ϕ := by ext; simp
  right_inv f := pi_ext fun i x => by simp
#align monoid_hom.noncomm_pi_coprod_equiv MonoidHom.noncommPiCoprodEquiv
#align add_monoid_hom.noncomm_pi_coprod_equiv AddMonoidHom.noncommPiCoprodEquiv
-/

#print MonoidHom.noncommPiCoprod_mrange /-
@[to_additive]
theorem noncommPiCoprod_mrange : (noncommPiCoprod ϕ hcomm).mrange = ⨆ i : ι, (ϕ i).mrange := by
  classical
#align monoid_hom.noncomm_pi_coprod_mrange MonoidHom.noncommPiCoprod_mrange
#align add_monoid_hom.noncomm_pi_coprod_mrange AddMonoidHom.noncommPiCoprod_mrange
-/

end MonoidHom

end FamilyOfMonoids

section FamilyOfGroups

variable {G : Type _} [Group G]

variable {ι : Type _} [hdec : DecidableEq ι] [hfin : Fintype ι]

variable {H : ι → Type _} [∀ i, Group (H i)]

variable (ϕ : ∀ i : ι, H i →* G)

variable {hcomm : ∀ i j : ι, i ≠ j → ∀ (x : H i) (y : H j), Commute (ϕ i x) (ϕ j y)}

-- We use `f` and `g` to denote elements of `Π (i : ι), H i`
variable (f g : ∀ i : ι, H i)

namespace MonoidHom

#print MonoidHom.noncommPiCoprod_range /-
-- The subgroup version of `noncomm_pi_coprod_mrange`
@[to_additive]
theorem noncommPiCoprod_range : (noncommPiCoprod ϕ hcomm).range = ⨆ i : ι, (ϕ i).range := by
  classical
#align monoid_hom.noncomm_pi_coprod_range MonoidHom.noncommPiCoprod_range
#align add_monoid_hom.noncomm_pi_coprod_range AddMonoidHom.noncommPiCoprod_range
-/

#print MonoidHom.injective_noncommPiCoprod_of_independent /-
@[to_additive]
theorem injective_noncommPiCoprod_of_independent
    (hind : CompleteLattice.Independent fun i => (ϕ i).range)
    (hinj : ∀ i, Function.Injective (ϕ i)) : Function.Injective (noncommPiCoprod ϕ hcomm) := by
  classical
#align monoid_hom.injective_noncomm_pi_coprod_of_independent MonoidHom.injective_noncommPiCoprod_of_independent
#align add_monoid_hom.injective_noncomm_pi_coprod_of_independent AddMonoidHom.injective_noncommPiCoprod_of_independent
-/

variable (hcomm)

#print MonoidHom.independent_range_of_coprime_order /-
@[to_additive]
theorem independent_range_of_coprime_order [Finite ι] [∀ i, Fintype (H i)]
    (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    CompleteLattice.Independent fun i => (ϕ i).range :=
  by
  cases nonempty_fintype ι
  classical
#align monoid_hom.independent_range_of_coprime_order MonoidHom.independent_range_of_coprime_order
#align add_monoid_hom.independent_range_of_coprime_order AddMonoidHom.independent_range_of_coprime_order
-/

end MonoidHom

end FamilyOfGroups

namespace Subgroup

-- We have an family of subgroups
variable {G : Type _} [Group G]

variable {ι : Type _} [hdec : DecidableEq ι] [hfin : Fintype ι] {H : ι → Subgroup G}

-- Elements of `Π (i : ι), H i` are called `f` and `g` here
variable (f g : ∀ i : ι, H i)

section CommutingSubgroups

-- We assume that the elements of different subgroups commute
variable (hcomm : ∀ i j : ι, i ≠ j → ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)

#print Subgroup.commute_subtype_of_commute /-
@[to_additive]
theorem commute_subtype_of_commute (i j : ι) (hne : i ≠ j) :
    ∀ (x : H i) (y : H j), Commute ((H i).Subtype x) ((H j).Subtype y) := by rintro ⟨x, hx⟩ ⟨y, hy⟩;
  exact hcomm i j hne x y hx hy
#align subgroup.commute_subtype_of_commute Subgroup.commute_subtype_of_commute
#align add_subgroup.commute_subtype_of_commute AddSubgroup.addCommute_subtype_of_addCommute
-/

#print Subgroup.noncommPiCoprod /-
/-- The canonical homomorphism from a family of subgroups where elements from different subgroups
commute -/
@[to_additive
      "The canonical homomorphism from a family of additive subgroups where elements from\ndifferent subgroups commute"]
def noncommPiCoprod : (∀ i : ι, H i) →* G :=
  MonoidHom.noncommPiCoprod (fun i => (H i).Subtype) (commute_subtype_of_commute hcomm)
#align subgroup.noncomm_pi_coprod Subgroup.noncommPiCoprod
#align add_subgroup.noncomm_pi_coprod AddSubgroup.noncommPiCoprod
-/

variable {hcomm}

#print Subgroup.noncommPiCoprod_mulSingle /-
@[simp, to_additive]
theorem noncommPiCoprod_mulSingle (i : ι) (y : H i) :
    noncommPiCoprod hcomm (Pi.mulSingle i y) = y := by apply MonoidHom.noncommPiCoprod_mulSingle
#align subgroup.noncomm_pi_coprod_mul_single Subgroup.noncommPiCoprod_mulSingle
#align add_subgroup.noncomm_pi_coprod_single AddSubgroup.noncommPiCoprod_single
-/

#print Subgroup.noncommPiCoprod_range /-
@[to_additive]
theorem noncommPiCoprod_range : (noncommPiCoprod hcomm).range = ⨆ i : ι, H i := by
  simp [noncomm_pi_coprod, MonoidHom.noncommPiCoprod_range]
#align subgroup.noncomm_pi_coprod_range Subgroup.noncommPiCoprod_range
#align add_subgroup.noncomm_pi_coprod_range AddSubgroup.noncommPiCoprod_range
-/

#print Subgroup.injective_noncommPiCoprod_of_independent /-
@[to_additive]
theorem injective_noncommPiCoprod_of_independent (hind : CompleteLattice.Independent H) :
    Function.Injective (noncommPiCoprod hcomm) :=
  by
  apply MonoidHom.injective_noncommPiCoprod_of_independent
  · simpa using hind
  · intro i; exact Subtype.coe_injective
#align subgroup.injective_noncomm_pi_coprod_of_independent Subgroup.injective_noncommPiCoprod_of_independent
#align add_subgroup.injective_noncomm_pi_coprod_of_independent AddSubgroup.injective_noncommPiCoprod_of_independent
-/

variable (hcomm)

#print Subgroup.independent_of_coprime_order /-
@[to_additive]
theorem independent_of_coprime_order [Finite ι] [∀ i, Fintype (H i)]
    (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j))) :
    CompleteLattice.Independent H := by
  simpa using
    MonoidHom.independent_range_of_coprime_order (fun i => (H i).Subtype)
      (commute_subtype_of_commute hcomm) hcoprime
#align subgroup.independent_of_coprime_order Subgroup.independent_of_coprime_order
#align add_subgroup.independent_of_coprime_order AddSubgroup.independent_of_coprime_order
-/

end CommutingSubgroups

end Subgroup

