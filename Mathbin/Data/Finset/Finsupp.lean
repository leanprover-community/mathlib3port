/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finset.finsupp
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Finsupp
import Mathbin.Data.Finset.Pointwise
import Mathbin.Data.Finsupp.Indicator
import Mathbin.Data.Fintype.BigOperators

/-!
# Finitely supported product of finsets

This file defines the finitely supported product of finsets as a `finset (ι →₀ α)`.

## Main declarations

* `finset.finsupp`: Finitely supported product of finsets. `s.finset t` is the product of the `t i`
  over all `i ∈ s`.
* `finsupp.pi`: `f.pi` is the finset of `finsupp`s whose `i`-th value lies in `f i`. This is the
  special case of `finset.finsupp` where we take the product of the `f i` over the support of `f`.

## Implementation notes

We make heavy use of the fact that `0 : finset α` is `{0}`. This scalar actions convention turns out
to be precisely what we want here too.
-/


noncomputable section

open Finsupp

open BigOperators Classical Pointwise

variable {ι α : Type _} [Zero α] {s : Finset ι} {f : ι →₀ α}

namespace Finset

#print Finset.finsupp /-
/-- Finitely supported product of finsets. -/
protected def finsupp (s : Finset ι) (t : ι → Finset α) : Finset (ι →₀ α) :=
  (s.pi t).map ⟨indicator s, indicator_injective s⟩
#align finset.finsupp Finset.finsupp
-/

#print Finset.mem_finsupp_iff /-
theorem mem_finsupp_iff {t : ι → Finset α} : f ∈ s.Finsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i :=
  by
  refine' mem_map.trans ⟨_, _⟩
  · rintro ⟨f, hf, rfl⟩
    refine' ⟨support_indicator_subset _ _, fun i hi => _⟩
    convert mem_pi.1 hf i hi
    exact indicator_of_mem hi _
  · refine' fun h => ⟨fun i _ => f i, mem_pi.2 h.2, _⟩
    ext i
    exact ite_eq_left_iff.2 fun hi => (not_mem_support_iff.1 fun H => hi <| h.1 H).symm
#align finset.mem_finsupp_iff Finset.mem_finsupp_iff
-/

/- warning: finset.mem_finsupp_iff_of_support_subset -> Finset.mem_finsupp_iff_of_support_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] {s : Finset.{u1} ι} {f : Finsupp.{u1, u2} ι α _inst_1} {t : Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)}, (HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) (Finsupp.support.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1) t) s) -> (Iff (Membership.Mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι α _inst_1) (Finset.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_1)) (Finset.hasMem.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_1)) f (Finset.finsupp.{u1, u2} ι α _inst_1 s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) (fun (_x : Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) => ι -> (Finset.{u2} α)) (Finsupp.hasCoeToFun.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) t))) (forall (i : ι), Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_1) (fun (_x : Finsupp.{u1, u2} ι α _inst_1) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_1) f i) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) (fun (_x : Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) => ι -> (Finset.{u2} α)) (Finsupp.hasCoeToFun.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) t i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] {s : Finset.{u2} ι} {f : Finsupp.{u2, u1} ι α _inst_1} {t : Finsupp.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)}, (HasSubset.Subset.{u2} (Finset.{u2} ι) (Finset.instHasSubsetFinset.{u2} ι) (Finsupp.support.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1) t) s) -> (Iff (Membership.mem.{max u2 u1, max u2 u1} (Finsupp.{u2, u1} ι α _inst_1) (Finset.{max u1 u2} (Finsupp.{u2, u1} ι α _inst_1)) (Finset.instMembershipFinset.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_1)) f (Finset.finsupp.{u2, u1} ι α _inst_1 s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => Finset.{u1} α) _x) (Finsupp.funLike.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)) t))) (forall (i : ι), Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => Finset.{u1} α) i) (Finset.instMembershipFinset.{u1} α) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_1) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) _x) (Finsupp.funLike.{u2, u1} ι α _inst_1) f i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => Finset.{u1} α) _x) (Finsupp.funLike.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)) t i)))
Case conversion may be inaccurate. Consider using '#align finset.mem_finsupp_iff_of_support_subset Finset.mem_finsupp_iff_of_support_subsetₓ'. -/
/-- When `t` is supported on `s`, `f ∈ s.finsupp t` precisely means that `f` is pointwise in `t`. -/
@[simp]
theorem mem_finsupp_iff_of_support_subset {t : ι →₀ Finset α} (ht : t.support ⊆ s) :
    f ∈ s.Finsupp t ↔ ∀ i, f i ∈ t i :=
  by
  refine'
    mem_finsupp_iff.trans
      (forall_and_distrib.symm.trans <|
        forall_congr' fun i =>
          ⟨fun h => _, fun h =>
            ⟨fun hi => ht <| mem_support_iff.2 fun H => mem_support_iff.1 hi _, fun _ => h⟩⟩)
  · by_cases hi : i ∈ s
    · exact h.2 hi
    · rw [not_mem_support_iff.1 (mt h.1 hi), not_mem_support_iff.1 fun H => hi <| ht H]
      exact zero_mem_zero
  · rwa [H, mem_zero] at h
#align finset.mem_finsupp_iff_of_support_subset Finset.mem_finsupp_iff_of_support_subset

/- warning: finset.card_finsupp -> Finset.card_finsupp is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] (s : Finset.{u1} ι) (t : ι -> (Finset.{u2} α)), Eq.{1} Nat (Finset.card.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_1) (Finset.finsupp.{u1, u2} ι α _inst_1 s t)) (Finset.prod.{0, u1} Nat ι Nat.commMonoid s (fun (i : ι) => Finset.card.{u2} α (t i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] (s : Finset.{u2} ι) (t : ι -> (Finset.{u1} α)), Eq.{1} Nat (Finset.card.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_1) (Finset.finsupp.{u2, u1} ι α _inst_1 s t)) (Finset.prod.{0, u2} Nat ι Nat.commMonoid s (fun (i : ι) => Finset.card.{u1} α (t i)))
Case conversion may be inaccurate. Consider using '#align finset.card_finsupp Finset.card_finsuppₓ'. -/
@[simp]
theorem card_finsupp (s : Finset ι) (t : ι → Finset α) :
    (s.Finsupp t).card = ∏ i in s, (t i).card :=
  (card_map _).trans <| card_pi _ _
#align finset.card_finsupp Finset.card_finsupp

end Finset

open Finset

namespace Finsupp

#print Finsupp.pi /-
/-- Given a finitely supported function `f : ι →₀ finset α`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
def pi (f : ι →₀ Finset α) : Finset (ι →₀ α) :=
  f.support.Finsupp f
#align finsupp.pi Finsupp.pi
-/

/- warning: finsupp.mem_pi -> Finsupp.mem_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] {f : Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)} {g : Finsupp.{u1, u2} ι α _inst_1}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι α _inst_1) (Finset.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_1)) (Finset.hasMem.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_1)) g (Finsupp.pi.{u1, u2} ι α _inst_1 f)) (forall (i : ι), Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_1) (fun (_x : Finsupp.{u1, u2} ι α _inst_1) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_1) g i) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) (fun (_x : Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) => ι -> (Finset.{u2} α)) (Finsupp.hasCoeToFun.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) f i))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] {f : Finsupp.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)} {g : Finsupp.{u2, u1} ι α _inst_1}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Finsupp.{u2, u1} ι α _inst_1) (Finset.{max u1 u2} (Finsupp.{u2, u1} ι α _inst_1)) (Finset.instMembershipFinset.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_1)) g (Finsupp.pi.{u2, u1} ι α _inst_1 f)) (forall (i : ι), Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => Finset.{u1} α) i) (Finset.instMembershipFinset.{u1} α) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_1) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) _x) (Finsupp.funLike.{u2, u1} ι α _inst_1) g i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => Finset.{u1} α) _x) (Finsupp.funLike.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)) f i))
Case conversion may be inaccurate. Consider using '#align finsupp.mem_pi Finsupp.mem_piₓ'. -/
@[simp]
theorem mem_pi {f : ι →₀ Finset α} {g : ι →₀ α} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
  mem_finsupp_iff_of_support_subset <| Subset.refl _
#align finsupp.mem_pi Finsupp.mem_pi

/- warning: finsupp.card_pi -> Finsupp.card_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] (f : Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)), Eq.{1} Nat (Finset.card.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_1) (Finsupp.pi.{u1, u2} ι α _inst_1 f)) (Finsupp.prod.{u1, u2, 0} ι (Finset.{u2} α) Nat (Finset.zero.{u2} α _inst_1) Nat.commMonoid f (fun (i : ι) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat ((Finset.{u2} α) -> Nat) (HasLiftT.mk.{1, succ u2} Nat ((Finset.{u2} α) -> Nat) (CoeTCₓ.coe.{1, succ u2} Nat ((Finset.{u2} α) -> Nat) (Nat.castCoe.{u2} ((Finset.{u2} α) -> Nat) (Pi.hasNatCast.{u2, 0} (Finset.{u2} α) (fun (ᾰ : Finset.{u2} α) => Nat) (fun (a : Finset.{u2} α) => AddMonoidWithOne.toNatCast.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))))))) (Finset.card.{u2} α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) (fun (_x : Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) => ι -> (Finset.{u2} α)) (Finsupp.hasCoeToFun.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1)) f i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] (f : Finsupp.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)), Eq.{1} Nat (Finset.card.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_1) (Finsupp.pi.{u2, u1} ι α _inst_1 f)) (Finsupp.prod.{u2, u1, 0} ι (Finset.{u1} α) Nat (Finset.zero.{u1} α _inst_1) Nat.commMonoid f (fun (i : ι) => Nat.cast.{u1} ((Finset.{u1} α) -> Nat) (Pi.natCast.{u1, 0} (Finset.{u1} α) (fun (a._@.Mathlib.Algebra.BigOperators.Finsupp._hyg.437 : Finset.{u1} α) => Nat) (fun (a : Finset.{u1} α) => CanonicallyOrderedCommSemiring.toNatCast.{0} Nat Nat.canonicallyOrderedCommSemiring)) (Finset.card.{u1} α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => Finset.{u1} α) _x) (Finsupp.funLike.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1)) f i))))
Case conversion may be inaccurate. Consider using '#align finsupp.card_pi Finsupp.card_piₓ'. -/
@[simp]
theorem card_pi (f : ι →₀ Finset α) : f.pi.card = f.Prod fun i => (f i).card :=
  by
  rw [pi, card_finsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.nat_apply, Nat.cast_id]
#align finsupp.card_pi Finsupp.card_pi

end Finsupp

