/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang

! This file was ported from Lean 3 source module algebra.direct_sum.decomposition
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Algebra.Module.Submodule.Basic

/-!
# Decompositions of additive monoids, groups, and modules into direct sums

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `direct_sum.decomposition ℳ`: A typeclass to provide a constructive decomposition from
  an additive monoid `M` into a family of additive submonoids `ℳ`
* `direct_sum.decompose ℳ`: The canonical equivalence provided by the above typeclass


## Main statements

* `direct_sum.decomposition.is_internal`: The link to `direct_sum.is_internal`.

## Implementation details

As we want to talk about different types of decomposition (additive monoids, modules, rings, ...),
we choose to avoid heavily bundling `direct_sum.decompose`, instead making copies for the
`add_equiv`, `linear_equiv`, etc. This means we have to repeat statements that follow from these
bundled homs, but means we don't have to repeat statements for different types of decomposition.
-/


variable {ι R M σ : Type _}

open DirectSum BigOperators

namespace DirectSum

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

#print DirectSum.Decomposition /-
/-- A decomposition is an equivalence between an additive monoid `M` and a direct sum of additive
submonoids `ℳ i` of that `M`, such that the "recomposition" is canonical. This definition also
works for additive groups and modules.

This is a version of `direct_sum.is_internal` which comes with a constructive inverse to the
canonical "recomposition" rather than just a proof that the "recomposition" is bijective. -/
class Decomposition where
  decompose' : M → ⨁ i, ℳ i
  left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
  right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
#align direct_sum.decomposition DirectSum.Decomposition
-/

include M

/-- `direct_sum.decomposition` instances, while carrying data, are always equal. -/
instance : Subsingleton (Decomposition ℳ) :=
  ⟨fun x y => by
    cases' x with x xl xr
    cases' y with y yl yr
    congr
    exact Function.LeftInverse.eq_rightInverse xr yl⟩

variable [Decomposition ℳ]

/- warning: direct_sum.decomposition.is_internal -> DirectSum.Decomposition.isInternal is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {σ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u3, u2} σ M] [_inst_4 : AddSubmonoidClass.{u3, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], DirectSum.IsInternal.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ
but is expected to have type
  forall {ι : Type.{u3}} {M : Type.{u2}} {σ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u1, u2} σ M] [_inst_4 : AddSubmonoidClass.{u1, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u3, u2, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], DirectSum.IsInternal.{u3, u2, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ
Case conversion may be inaccurate. Consider using '#align direct_sum.decomposition.is_internal DirectSum.Decomposition.isInternalₓ'. -/
protected theorem Decomposition.isInternal : DirectSum.IsInternal ℳ :=
  ⟨Decomposition.right_inv.Injective, Decomposition.left_inv.Surjective⟩
#align direct_sum.decomposition.is_internal DirectSum.Decomposition.isInternal

#print DirectSum.decompose /-
/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
to a direct sum of components. This is the canonical spelling of the `decompose'` field. -/
def decompose : M ≃ ⨁ i, ℳ i where
  toFun := Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv
#align direct_sum.decompose DirectSum.decompose
-/

/- warning: direct_sum.decomposition.induction_on -> DirectSum.Decomposition.inductionOn is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {σ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u3, u2} σ M] [_inst_4 : AddSubmonoidClass.{u3, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ] {p : M -> Prop}, (p (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))))) -> (forall {i : ι} (m : coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)), p ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) M (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) M (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) M (coeBase.{succ u2, succ u2} (coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) M (coeSubtype.{succ u2} M (fun (x : M) => Membership.Mem.{u2, u3} M σ (SetLike.hasMem.{u3, u2} σ M _inst_3) x (ℳ i)))))) m)) -> (forall (m : M) (m' : M), (p m) -> (p m') -> (p (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) m m'))) -> (forall (m : M), p m)
but is expected to have type
  forall {ι : Type.{u3}} {M : Type.{u2}} {σ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u1, u2} σ M] [_inst_4 : AddSubmonoidClass.{u1, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u3, u2, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ] {p : M -> Prop}, (p (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) -> (forall {i : ι} (m : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))), p (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} σ M _inst_3 (ℳ i))) m)) -> (forall (m : M) (m' : M), (p m) -> (p m') -> (p (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) m m'))) -> (forall (m : M), p m)
Case conversion may be inaccurate. Consider using '#align direct_sum.decomposition.induction_on DirectSum.Decomposition.inductionOnₓ'. -/
protected theorem Decomposition.inductionOn {p : M → Prop} (h_zero : p 0)
    (h_homogeneous : ∀ {i} (m : ℳ i), p (m : M)) (h_add : ∀ m m' : M, p m → p m' → p (m + m')) :
    ∀ m, p m :=
  by
  let ℳ' : ι → AddSubmonoid M := fun i =>
    (⟨ℳ i, fun _ _ => AddMemClass.add_mem, ZeroMemClass.zero_mem _⟩ : AddSubmonoid M)
  haveI t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ => (decompose ℳ).left_inv _
      right_inv := fun _ => (decompose ℳ).right_inv _ }
  have mem : ∀ m, m ∈ iSup ℳ' := fun m =>
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (decomposition.is_internal ℳ')).symm ▸ trivial
  exact fun m =>
    AddSubmonoid.iSup_induction ℳ' (mem m) (fun i m h => h_homogeneous ⟨m, h⟩) h_zero h_add
#align direct_sum.decomposition.induction_on DirectSum.Decomposition.inductionOn

/- warning: direct_sum.decomposition.decompose'_eq -> DirectSum.Decomposition.decompose'_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {σ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u3, u2} σ M] [_inst_4 : AddSubmonoidClass.{u3, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], Eq.{max (succ u2) (succ (max u1 u2))} (M -> (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (DirectSum.Decomposition.decompose'.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 (fun (i : ι) => ℳ i) _inst_5) (coeFn.{max 1 (max (succ u2) (succ (max u1 u2))) (succ (max u1 u2)) (succ u2), max (succ u2) (succ (max u1 u2))} (Equiv.{succ u2, succ (max u1 u2)} M (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (fun (_x : Equiv.{succ u2, succ (max u1 u2)} M (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) => M -> (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (Equiv.hasCoeToFun.{succ u2, succ (max u1 u2)} M (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (DirectSum.decompose.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ _inst_5))
but is expected to have type
  forall {ι : Type.{u3}} {M : Type.{u2}} {σ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u1, u2} σ M] [_inst_4 : AddSubmonoidClass.{u1, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u3, u2, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], Eq.{max (succ u3) (succ u2)} (M -> (DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (DirectSum.Decomposition.decompose'.{u3, u2, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 (fun (i : ι) => ℳ i) _inst_5) (FunLike.coe.{max (succ u3) (succ u2), succ u2, max (succ u3) (succ u2)} (Equiv.{succ u2, max (succ u2) (succ u3)} M (DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) M (fun (_x : M) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : M) => DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) _x) (Equiv.instFunLikeEquiv.{succ u2, max (succ u3) (succ u2)} M (DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (DirectSum.decompose.{u3, u2, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ _inst_5))
Case conversion may be inaccurate. Consider using '#align direct_sum.decomposition.decompose'_eq DirectSum.Decomposition.decompose'_eqₓ'. -/
@[simp]
theorem Decomposition.decompose'_eq : Decomposition.decompose' = decompose ℳ :=
  rfl
#align direct_sum.decomposition.decompose'_eq DirectSum.Decomposition.decompose'_eq

/- warning: direct_sum.decompose_symm_of -> DirectSum.decompose_symm_of is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_symm_of DirectSum.decompose_symm_ofₓ'. -/
@[simp]
theorem decompose_symm_of {i : ι} (x : ℳ i) : (decompose ℳ).symm (DirectSum.of _ i x) = x :=
  DirectSum.coeAddMonoidHom_of ℳ _ _
#align direct_sum.decompose_symm_of DirectSum.decompose_symm_of

/- warning: direct_sum.decompose_coe -> DirectSum.decompose_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_coe DirectSum.decompose_coeₓ'. -/
@[simp]
theorem decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← decompose_symm_of, Equiv.apply_symm_apply]
#align direct_sum.decompose_coe DirectSum.decompose_coe

/- warning: direct_sum.decompose_of_mem -> DirectSum.decompose_of_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_of_mem DirectSum.decompose_of_memₓ'. -/
theorem decompose_of_mem {x : M} {i : ι} (hx : x ∈ ℳ i) :
    decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩ :=
  decompose_coe _ ⟨x, hx⟩
#align direct_sum.decompose_of_mem DirectSum.decompose_of_mem

/- warning: direct_sum.decompose_of_mem_same -> DirectSum.decompose_of_mem_same is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_of_mem_same DirectSum.decompose_of_mem_sameₓ'. -/
theorem decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) : (decompose ℳ x i : M) = x := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_same, Subtype.coe_mk]
#align direct_sum.decompose_of_mem_same DirectSum.decompose_of_mem_same

/- warning: direct_sum.decompose_of_mem_ne -> DirectSum.decompose_of_mem_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_of_mem_ne DirectSum.decompose_of_mem_neₓ'. -/
theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (decompose ℳ x j : M) = 0 := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ _ hij, ZeroMemClass.coe_zero]
#align direct_sum.decompose_of_mem_ne DirectSum.decompose_of_mem_ne

/- warning: direct_sum.decompose_add_equiv -> DirectSum.decomposeAddEquiv is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {σ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u3, u2} σ M] [_inst_4 : AddSubmonoidClass.{u3, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], AddEquiv.{u2, max u1 u2} M (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (AddZeroClass.toHasAdd.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddMonoid.toAddZeroClass.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddCommMonoid.toAddMonoid.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (DirectSum.addCommMonoid.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} {σ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u3, u2} σ M] [_inst_4 : AddSubmonoidClass.{u3, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], AddEquiv.{u2, max u2 u1} M (DirectSum.{u1, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u3} M σ (SetLike.instMembership.{u3, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (AddZeroClass.toAdd.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u3} M σ (SetLike.instMembership.{u3, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddMonoid.toAddZeroClass.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u3} M σ (SetLike.instMembership.{u3, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddCommMonoid.toAddMonoid.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u3} M σ (SetLike.instMembership.{u3, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (instAddCommMonoidDirectSum.{u1, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u3} M σ (SetLike.instMembership.{u3, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))))))
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_add_equiv DirectSum.decomposeAddEquivₓ'. -/
/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
an additive monoid to a direct sum of components. -/
@[simps (config := { fullyApplied := false })]
def decomposeAddEquiv : M ≃+ ⨁ i, ℳ i :=
  AddEquiv.symm { (decompose ℳ).symm with map_add' := map_add (DirectSum.coeAddMonoidHom ℳ) }
#align direct_sum.decompose_add_equiv DirectSum.decomposeAddEquiv

/- warning: direct_sum.decompose_zero -> DirectSum.decompose_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {σ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u3, u2} σ M] [_inst_4 : AddSubmonoidClass.{u3, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], Eq.{succ (max u1 u2)} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (coeFn.{max 1 (max (succ u2) (succ (max u1 u2))) (succ (max u1 u2)) (succ u2), max (succ u2) (succ (max u1 u2))} (Equiv.{succ u2, succ (max u1 u2)} M (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (fun (_x : Equiv.{succ u2, succ (max u1 u2)} M (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) => M -> (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (Equiv.hasCoeToFun.{succ u2, succ (max u1 u2)} M (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (DirectSum.decompose.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ _inst_5) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))))) (OfNat.ofNat.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) 0 (OfNat.mk.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) 0 (Zero.zero.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddZeroClass.toHasZero.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddMonoid.toAddZeroClass.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddCommMonoid.toAddMonoid.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (DirectSum.addCommMonoid.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))))))))
but is expected to have type
  forall {ι : Type.{u3}} {M : Type.{u2}} {σ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u1, u2} σ M] [_inst_4 : AddSubmonoidClass.{u1, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u3, u2, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], Eq.{max (succ u3) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : M) => DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (FunLike.coe.{max (succ u3) (succ u2), succ u2, max (succ u3) (succ u2)} (Equiv.{succ u2, max (succ u2) (succ u3)} M (DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) M (fun (_x : M) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : M) => DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) _x) (Equiv.instFunLikeEquiv.{succ u2, max (succ u3) (succ u2)} M (DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))) (DirectSum.decompose.{u3, u2, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ _inst_5) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (OfNat.ofNat.{max u3 u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : M) => DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) 0 (Zero.toOfNat0.{max u3 u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : M) => DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (AddMonoid.toZero.{max u3 u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : M) => DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (AddCommMonoid.toAddMonoid.{max u3 u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : M) => DirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (instAddCommMonoidDirectSum.{u3, u2} ι (fun (i : ι) => Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M σ (SetLike.instMembership.{u1, u2} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))))))
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_zero DirectSum.decompose_zeroₓ'. -/
@[simp]
theorem decompose_zero : decompose ℳ (0 : M) = 0 :=
  map_zero (decomposeAddEquiv ℳ)
#align direct_sum.decompose_zero DirectSum.decompose_zero

/- warning: direct_sum.decompose_symm_zero -> DirectSum.decompose_symm_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {σ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : SetLike.{u3, u2} σ M] [_inst_4 : AddSubmonoidClass.{u3, u2} σ M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], Eq.{succ u2} M (coeFn.{max 1 (max (succ (max u1 u2)) (succ u2)) (succ u2) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u2)} (Equiv.{succ (max u1 u2), succ u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) M) (fun (_x : Equiv.{succ (max u1 u2), succ u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) M) => (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) -> M) (Equiv.hasCoeToFun.{succ (max u1 u2), succ u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) M) (Equiv.symm.{succ u2, succ (max u1 u2)} M (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (DirectSum.decompose.{u1, u2, u3} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ _inst_5)) (OfNat.ofNat.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) 0 (OfNat.mk.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) 0 (Zero.zero.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddZeroClass.toHasZero.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddMonoid.toAddZeroClass.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddCommMonoid.toAddMonoid.{max u1 u2} (DirectSum.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (DirectSum.addCommMonoid.{u1, u2} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u2)} σ Type.{u2} (SetLike.hasCoeToSort.{u3, u2} σ M _inst_3) (ℳ i)) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u2, u3} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))))))))) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u3}} {σ : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : SetLike.{u1, u3} σ M] [_inst_4 : AddSubmonoidClass.{u1, u3} σ M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)) _inst_3] (ℳ : ι -> σ) [_inst_5 : DirectSum.Decomposition.{u2, u3, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ], Eq.{succ u3} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) => M) (OfNat.ofNat.{max u2 u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) 0 (Zero.toOfNat0.{max u2 u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddMonoid.toZero.{max u2 u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddCommMonoid.toAddMonoid.{max u2 u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (instAddCommMonoidDirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))))))) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), succ u3} (Equiv.{max (succ u2) (succ u3), succ u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) M) (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (fun (_x : DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) => M) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), succ u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) M) (Equiv.symm.{succ u3, max (succ u2) (succ u3)} M (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (DirectSum.decompose.{u2, u3, u1} ι M σ (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 _inst_3 _inst_4 ℳ _inst_5)) (OfNat.ofNat.{max u2 u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) 0 (Zero.toOfNat0.{max u2 u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddMonoid.toZero.{max u2 u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (AddCommMonoid.toAddMonoid.{max u2 u3} (DirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i))) (instAddCommMonoidDirectSum.{u2, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u1} M σ (SetLike.instMembership.{u1, u3} σ M _inst_3) x (ℳ i))) (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u1} M _inst_2 σ _inst_3 _inst_4 (ℳ i)))))))) (OfNat.ofNat.{u3} M 0 (Zero.toOfNat0.{u3} M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))))
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_symm_zero DirectSum.decompose_symm_zeroₓ'. -/
@[simp]
theorem decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M) :=
  map_zero (decomposeAddEquiv ℳ).symm
#align direct_sum.decompose_symm_zero DirectSum.decompose_symm_zero

/- warning: direct_sum.decompose_add -> DirectSum.decompose_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_add DirectSum.decompose_addₓ'. -/
@[simp]
theorem decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y :=
  map_add (decomposeAddEquiv ℳ) x y
#align direct_sum.decompose_add DirectSum.decompose_add

/- warning: direct_sum.decompose_symm_add -> DirectSum.decompose_symm_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_symm_add DirectSum.decompose_symm_addₓ'. -/
@[simp]
theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y :=
  map_add (decomposeAddEquiv ℳ).symm x y
#align direct_sum.decompose_symm_add DirectSum.decompose_symm_add

/- warning: direct_sum.decompose_sum -> DirectSum.decompose_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_sum DirectSum.decompose_sumₓ'. -/
@[simp]
theorem decompose_sum {ι'} (s : Finset ι') (f : ι' → M) :
    decompose ℳ (∑ i in s, f i) = ∑ i in s, decompose ℳ (f i) :=
  map_sum (decomposeAddEquiv ℳ) f s
#align direct_sum.decompose_sum DirectSum.decompose_sum

/- warning: direct_sum.decompose_symm_sum -> DirectSum.decompose_symm_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_symm_sum DirectSum.decompose_symm_sumₓ'. -/
@[simp]
theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' → ⨁ i, ℳ i) :
    (decompose ℳ).symm (∑ i in s, f i) = ∑ i in s, (decompose ℳ).symm (f i) :=
  map_sum (decomposeAddEquiv ℳ).symm f s
#align direct_sum.decompose_symm_sum DirectSum.decompose_symm_sum

/- warning: direct_sum.sum_support_decompose -> DirectSum.sum_support_decompose is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.sum_support_decompose DirectSum.sum_support_decomposeₓ'. -/
theorem sum_support_decompose [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) :
    (∑ i in (decompose ℳ r).support, (decompose ℳ r i : M)) = r :=
  by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r, ← sum_support_of (fun i => ℳ i) (decompose ℳ r)]
  rw [decompose_symm_sum]
  simp_rw [decompose_symm_of]
#align direct_sum.sum_support_decompose DirectSum.sum_support_decompose

end AddCommMonoid

#print DirectSum.addCommGroupSetLike /-
/-- The `-` in the statements below doesn't resolve without this line.

This seems to a be a problem of synthesized vs inferred typeclasses disagreeing. If we replace
the statement of `decompose_neg` with `@eq (⨁ i, ℳ i) (decompose ℳ (-x)) (-decompose ℳ x)`
instead of `decompose ℳ (-x) = -decompose ℳ x`, which forces the typeclasses needed by `⨁ i, ℳ i` to
be found by unification rather than synthesis, then everything works fine without this instance. -/
instance addCommGroupSetLike [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ) :
    AddCommGroup (⨁ i, ℳ i) := by infer_instance
#align direct_sum.add_comm_group_set_like DirectSum.addCommGroupSetLike
-/

section AddCommGroup

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

include M

/- warning: direct_sum.decompose_neg -> DirectSum.decompose_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_neg DirectSum.decompose_negₓ'. -/
@[simp]
theorem decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x :=
  map_neg (decomposeAddEquiv ℳ) x
#align direct_sum.decompose_neg DirectSum.decompose_neg

/- warning: direct_sum.decompose_symm_neg -> DirectSum.decompose_symm_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_symm_neg DirectSum.decompose_symm_negₓ'. -/
@[simp]
theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (decompose ℳ).symm (-x) = -(decompose ℳ).symm x :=
  map_neg (decomposeAddEquiv ℳ).symm x
#align direct_sum.decompose_symm_neg DirectSum.decompose_symm_neg

/- warning: direct_sum.decompose_sub -> DirectSum.decompose_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_sub DirectSum.decompose_subₓ'. -/
@[simp]
theorem decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y :=
  map_sub (decomposeAddEquiv ℳ) x y
#align direct_sum.decompose_sub DirectSum.decompose_sub

/- warning: direct_sum.decompose_symm_sub -> DirectSum.decompose_symm_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_symm_sub DirectSum.decompose_symm_subₓ'. -/
@[simp]
theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y :=
  map_sub (decomposeAddEquiv ℳ).symm x y
#align direct_sum.decompose_symm_sub DirectSum.decompose_symm_sub

end AddCommGroup

section Module

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]

variable (ℳ : ι → Submodule R M)

variable [Decomposition ℳ]

include M

/- warning: direct_sum.decompose_linear_equiv -> DirectSum.decomposeLinearEquiv is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Semiring.{u2} R] [_inst_3 : AddCommMonoid.{u3} M] [_inst_4 : Module.{u2, u3} R M _inst_2 _inst_3] (ℳ : ι -> (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4)) [_inst_5 : DirectSum.Decomposition.{u1, u3, u3} ι M (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_3 (Submodule.setLike.{u2, u3} R M _inst_2 _inst_3 _inst_4) (Submodule.addSubmonoidClass.{u2, u3} R M _inst_2 _inst_3 _inst_4) ℳ], LinearEquiv.{u2, u2, u3, max u1 u3} R R _inst_2 _inst_2 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (RingHomInvPair.ids.{u2} R _inst_2) (RingHomInvPair.ids.{u2} R _inst_2) M (DirectSum.{u1, u3} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u3)} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) Type.{u3} (SetLike.hasCoeToSort.{u3, u3} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) M (Submodule.setLike.{u2, u3} R M _inst_2 _inst_3 _inst_4)) (ℳ i)) (fun (i : ι) => Submodule.addCommMonoid.{u2, u3} R M _inst_2 _inst_3 _inst_4 (ℳ i))) _inst_3 (DirectSum.addCommMonoid.{u1, u3} ι (fun (i : ι) => coeSort.{succ u3, succ (succ u3)} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) Type.{u3} (SetLike.hasCoeToSort.{u3, u3} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) M (Submodule.setLike.{u2, u3} R M _inst_2 _inst_3 _inst_4)) (ℳ i)) (fun (i : ι) => Submodule.addCommMonoid.{u2, u3} R M _inst_2 _inst_3 _inst_4 (ℳ i))) _inst_4 (DirectSum.module.{u2, u1, u3} R _inst_2 ι (fun (i : ι) => coeSort.{succ u3, succ (succ u3)} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) Type.{u3} (SetLike.hasCoeToSort.{u3, u3} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) M (Submodule.setLike.{u2, u3} R M _inst_2 _inst_3 _inst_4)) (ℳ i)) (fun (i : ι) => Submodule.addCommMonoid.{u2, u3} R M _inst_2 _inst_3 _inst_4 (ℳ i)) (fun (i : ι) => Submodule.module.{u2, u3} R M _inst_2 _inst_3 _inst_4 (ℳ i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Semiring.{u2} R] [_inst_3 : AddCommMonoid.{u3} M] [_inst_4 : Module.{u2, u3} R M _inst_2 _inst_3] (ℳ : ι -> (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4)) [_inst_5 : DirectSum.Decomposition.{u1, u3, u3} ι M (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_3 (Submodule.setLike.{u2, u3} R M _inst_2 _inst_3 _inst_4) (Submodule.addSubmonoidClass.{u2, u3} R M _inst_2 _inst_3 _inst_4) ℳ], LinearEquiv.{u2, u2, u3, max u3 u1} R R _inst_2 _inst_2 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2)) (RingHomInvPair.ids.{u2} R _inst_2) (RingHomInvPair.ids.{u2} R _inst_2) M (DirectSum.{u1, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u3} M (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u3, u3} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) M (Submodule.setLike.{u2, u3} R M _inst_2 _inst_3 _inst_4)) x (ℳ i))) (fun (i : ι) => Submodule.addCommMonoid.{u2, u3} R M _inst_2 _inst_3 _inst_4 (ℳ i))) _inst_3 (instAddCommMonoidDirectSum.{u1, u3} ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u3} M (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u3, u3} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) M (Submodule.setLike.{u2, u3} R M _inst_2 _inst_3 _inst_4)) x (ℳ i))) (fun (i : ι) => Submodule.addCommMonoid.{u2, u3} R M _inst_2 _inst_3 _inst_4 (ℳ i))) _inst_4 (DirectSum.instModuleDirectSumInstAddCommMonoidDirectSum.{u2, u1, u3} R _inst_2 ι (fun (i : ι) => Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u3} M (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u3, u3} (Submodule.{u2, u3} R M _inst_2 _inst_3 _inst_4) M (Submodule.setLike.{u2, u3} R M _inst_2 _inst_3 _inst_4)) x (ℳ i))) (fun (i : ι) => Submodule.addCommMonoid.{u2, u3} R M _inst_2 _inst_3 _inst_4 (ℳ i)) (fun (i : ι) => Submodule.module.{u2, u3} R M _inst_2 _inst_3 _inst_4 (ℳ i)))
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_linear_equiv DirectSum.decomposeLinearEquivₓ'. -/
/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
a module to a direct sum of components. -/
@[simps (config := { fullyApplied := false })]
def decomposeLinearEquiv : M ≃ₗ[R] ⨁ i, ℳ i :=
  LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }
#align direct_sum.decompose_linear_equiv DirectSum.decomposeLinearEquiv

/- warning: direct_sum.decompose_smul -> DirectSum.decompose_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.decompose_smul DirectSum.decompose_smulₓ'. -/
@[simp]
theorem decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x :=
  map_smul (decomposeLinearEquiv ℳ) r x
#align direct_sum.decompose_smul DirectSum.decompose_smul

end Module

end DirectSum

