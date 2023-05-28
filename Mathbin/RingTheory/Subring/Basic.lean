/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan

! This file was ported from Lean 3 source module ring_theory.subring.basic
! leanprover-community/mathlib commit 34ee86e6a59d911a8e4f89b68793ee7577ae79c7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.RingTheory.Subsemiring.Basic

/-!
# Subrings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `R` be a ring. This file defines the "bundled" subring type `subring R`, a type
whose terms correspond to subrings of `R`. This is the preferred way to talk
about subrings in mathlib. Unbundled subrings (`s : set R` and `is_subring s`)
are not in this file, and they will ultimately be deprecated.

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `set R` to `subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [ring R] (S : Type u) [ring S] (f g : R →+* S)`
`(A : subring R) (B : subring S) (s : set R)`

* `subring R` : the type of subrings of a ring `R`.

* `instance : complete_lattice (subring R)` : the complete lattice structure on the subrings.

* `subring.center` : the center of a ring `R`.

* `subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `subring.gi` : `closure : set M → subring M` and coercion `coe : subring M → set M`
  form a `galois_insertion`.

* `comap f B : subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : subring (R × S)` : the product of subrings

* `f.range : subring B` : the range of the ring homomorphism `f`.

* `eq_locus f g : subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

A subring is implemented as a subsemiring which is also an additive subgroup.
The initial PR was as a submonoid which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/


open BigOperators

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [Ring R]

section SubringClass

#print SubringClass /-
/-- `subring_class S R` states that `S` is a type of subsets `s ⊆ R` that
are both a multiplicative submonoid and an additive subgroup. -/
class SubringClass (S : Type _) (R : Type u) [Ring R] [SetLike S R] extends SubsemiringClass S R,
  NegMemClass S R : Prop
#align subring_class SubringClass
-/

/- warning: subring_class.add_subgroup_class -> SubringClass.addSubgroupClass is a dubious translation:
lean 3 declaration is
  forall (S : Type.{u2}) (R : Type.{u1}) [_inst_2 : SetLike.{u2, u1} S R] [_inst_3 : Ring.{u1} R] [h : SubringClass.{u1, u2} S R _inst_3 _inst_2], AddSubgroupClass.{u2, u1} S R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_3)))) _inst_2
but is expected to have type
  forall (S : Type.{u2}) (R : Type.{u1}) [_inst_2 : SetLike.{u2, u1} S R] [_inst_3 : Ring.{u1} R] [h : SubringClass.{u1, u2} S R _inst_3 _inst_2], AddSubgroupClass.{u2, u1} S R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_3))) _inst_2
Case conversion may be inaccurate. Consider using '#align subring_class.add_subgroup_class SubringClass.addSubgroupClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) SubringClass.addSubgroupClass (S : Type _) (R : Type u) [SetLike S R]
    [Ring R] [h : SubringClass S R] : AddSubgroupClass S R :=
  { h with }
#align subring_class.add_subgroup_class SubringClass.addSubgroupClass

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

include hSR

/- warning: coe_int_mem -> coe_int_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : SetLike.{u2, u1} S R] [hSR : SubringClass.{u1, u2} S R _inst_1 _inst_2] (s : S) (n : Int), Membership.Mem.{u1, u2} R S (SetLike.hasMem.{u2, u1} S R _inst_2) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) n) s
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : SetLike.{u2, u1} S R] [hSR : SubringClass.{u1, u2} S R _inst_1 _inst_2] (s : S) (n : Int), Membership.mem.{u1, u2} R S (SetLike.instMembership.{u2, u1} S R _inst_2) (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1) n) s
Case conversion may be inaccurate. Consider using '#align coe_int_mem coe_int_memₓ'. -/
theorem coe_int_mem (n : ℤ) : (n : R) ∈ s := by simp only [← zsmul_one, zsmul_mem, one_mem]
#align coe_int_mem coe_int_mem

namespace SubringClass

#print SubringClass.toHasIntCast /-
instance (priority := 75) toHasIntCast : IntCast s :=
  ⟨fun n => ⟨n, coe_int_mem s n⟩⟩
#align subring_class.to_has_int_cast SubringClass.toHasIntCast
-/

#print SubringClass.toRing /-
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
/-- A subring of a ring inherits a ring structure -/
instance (priority := 75) toRing : Ring s :=
  Subtype.coe_injective.Ring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring_class.to_ring SubringClass.toRing
-/

omit hSR

#print SubringClass.toCommRing /-
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
/-- A subring of a `comm_ring` is a `comm_ring`. -/
instance (priority := 75) toCommRing {R} [CommRing R] [SetLike S R] [SubringClass S R] :
    CommRing s :=
  Subtype.coe_injective.CommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring_class.to_comm_ring SubringClass.toCommRing
-/

-- Prefer subclasses of `ring` over subclasses of `subring_class`.
/-- A subring of a domain is a domain. -/
instance (priority := 75) {R} [Ring R] [IsDomain R] [SetLike S R] [SubringClass S R] : IsDomain s :=
  NoZeroDivisors.to_isDomain _

#print SubringClass.toOrderedRing /-
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
/-- A subring of an `ordered_ring` is an `ordered_ring`. -/
instance (priority := 75) toOrderedRing {R} [OrderedRing R] [SetLike S R] [SubringClass S R] :
    OrderedRing s :=
  Subtype.coe_injective.OrderedRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring_class.to_ordered_ring SubringClass.toOrderedRing
-/

#print SubringClass.toOrderedCommRing /-
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
/-- A subring of an `ordered_comm_ring` is an `ordered_comm_ring`. -/
instance (priority := 75) toOrderedCommRing {R} [OrderedCommRing R] [SetLike S R]
    [SubringClass S R] : OrderedCommRing s :=
  Subtype.coe_injective.OrderedCommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring_class.to_ordered_comm_ring SubringClass.toOrderedCommRing
-/

#print SubringClass.toLinearOrderedRing /-
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
/-- A subring of a `linear_ordered_ring` is a `linear_ordered_ring`. -/
instance (priority := 75) toLinearOrderedRing {R} [LinearOrderedRing R] [SetLike S R]
    [SubringClass S R] : LinearOrderedRing s :=
  Subtype.coe_injective.LinearOrderedRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subring_class.to_linear_ordered_ring SubringClass.toLinearOrderedRing
-/

#print SubringClass.toLinearOrderedCommRing /-
-- Prefer subclasses of `ring` over subclasses of `subring_class`.
/-- A subring of a `linear_ordered_comm_ring` is a `linear_ordered_comm_ring`. -/
instance (priority := 75) toLinearOrderedCommRing {R} [LinearOrderedCommRing R] [SetLike S R]
    [SubringClass S R] : LinearOrderedCommRing s :=
  Subtype.coe_injective.LinearOrderedCommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subring_class.to_linear_ordered_comm_ring SubringClass.toLinearOrderedCommRing
-/

include hSR

#print SubringClass.subtype /-
/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : S) : s →+* R :=
  { SubmonoidClass.Subtype s, AddSubgroupClass.subtype s with toFun := coe }
#align subring_class.subtype SubringClass.subtype
-/

/- warning: subring_class.coe_subtype -> SubringClass.coeSubtype is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subring_class.coe_subtype SubringClass.coeSubtypeₓ'. -/
@[simp]
theorem coeSubtype : (subtype s : s → R) = coe :=
  rfl
#align subring_class.coe_subtype SubringClass.coeSubtype

/- warning: subring_class.coe_nat_cast -> SubringClass.coe_natCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : SetLike.{u2, u1} S R] [hSR : SubringClass.{u1, u2} S R _inst_1 _inst_2] (s : S) (n : Nat), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u2} R S (SetLike.hasMem.{u2, u1} S R _inst_2) x s))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (HasLiftT.mk.{1, succ u1} Nat (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (CoeTCₓ.coe.{1, succ u1} Nat (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (Nat.castCoe.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (AddMonoidWithOne.toNatCast.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (AddGroupWithOne.toAddMonoidWithOne.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (Ring.toAddCommGroupWithOne.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (SubringClass.toRing.{u1, u2} R S _inst_1 _inst_2 hSR s)))))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) n)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : SetLike.{u2, u1} S R] [hSR : SubringClass.{u1, u2} S R _inst_1 _inst_2] (s : S) (n : Nat), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u2, u1} S R _inst_2 s)) (Nat.cast.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u2} R S (SetLike.instMembership.{u2, u1} S R _inst_2) x s)) (Semiring.toNatCast.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u2} R S (SetLike.instMembership.{u2, u1} S R _inst_2) x s)) (Ring.toSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u2} R S (SetLike.instMembership.{u2, u1} S R _inst_2) x s)) (SubringClass.toRing.{u1, u2} R S _inst_1 _inst_2 hSR s))) n)) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (Ring.toSemiring.{u1} R _inst_1)) n)
Case conversion may be inaccurate. Consider using '#align subring_class.coe_nat_cast SubringClass.coe_natCastₓ'. -/
@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ((n : s) : R) = n :=
  map_natCast (subtype s) n
#align subring_class.coe_nat_cast SubringClass.coe_natCast

/- warning: subring_class.coe_int_cast -> SubringClass.coe_intCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : SetLike.{u2, u1} S R] [hSR : SubringClass.{u1, u2} S R _inst_1 _inst_2] (s : S) (n : Int), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u2} R S (SetLike.hasMem.{u2, u1} S R _inst_2) x s))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (HasLiftT.mk.{1, succ u1} Int (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (CoeTCₓ.coe.{1, succ u1} Int (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (Int.castCoe.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (AddGroupWithOne.toHasIntCast.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (Ring.toAddCommGroupWithOne.{u1} (coeSort.{succ u2, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u2, u1} S R _inst_2) s) (SubringClass.toRing.{u1, u2} R S _inst_1 _inst_2 hSR s))))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) n)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : SetLike.{u2, u1} S R] [hSR : SubringClass.{u1, u2} S R _inst_1 _inst_2] (s : S) (n : Int), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u2, u1} S R _inst_2 s)) (Int.cast.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u2} R S (SetLike.instMembership.{u2, u1} S R _inst_2) x s)) (Ring.toIntCast.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u2} R S (SetLike.instMembership.{u2, u1} S R _inst_2) x s)) (SubringClass.toRing.{u1, u2} R S _inst_1 _inst_2 hSR s)) n)) (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1) n)
Case conversion may be inaccurate. Consider using '#align subring_class.coe_int_cast SubringClass.coe_intCastₓ'. -/
@[simp, norm_cast]
theorem coe_intCast (n : ℤ) : ((n : s) : R) = n :=
  map_intCast (subtype s) n
#align subring_class.coe_int_cast SubringClass.coe_intCast

end SubringClass

end SubringClass

variable [Ring S] [Ring T]

#print Subring /-
/-- `subring R` is the type of subrings of `R`. A subring of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
structure Subring (R : Type u) [Ring R] extends Subsemiring R, AddSubgroup R
#align subring Subring
-/

/-- Reinterpret a `subring` as a `subsemiring`. -/
add_decl_doc Subring.toSubsemiring

/-- Reinterpret a `subring` as an `add_subgroup`. -/
add_decl_doc Subring.toAddSubgroup

namespace Subring

/- warning: subring.to_submonoid clashes with [anonymous] -> [anonymous]
warning: subring.to_submonoid -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : Ring.{u} R], (Subring.{u} R _inst_1) -> (Submonoid.{u} R (MulZeroOneClass.toMulOneClass.{u} R (NonAssocSemiring.toMulZeroOneClass.{u} R (NonAssocRing.toNonAssocSemiring.{u} R (Ring.toNonAssocRing.{u} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> R -> _inst_1) -> Nat -> (List.{u} R) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align subring.to_submonoid [anonymous]ₓ'. -/
/-- The underlying submonoid of a subring. -/
def [anonymous] (s : Subring R) : Submonoid R :=
  { s.toSubsemiring.toSubmonoid with carrier := s.carrier }
#align subring.to_submonoid [anonymous]

instance : SetLike (Subring R) R where
  coe := Subring.carrier
  coe_injective' p q h := by cases p <;> cases q <;> congr

instance : SubringClass (Subring R) R
    where
  zero_mem := zero_mem'
  add_mem := add_mem'
  one_mem := one_mem'
  mul_mem := mul_mem'
  neg_mem := neg_mem'

/- warning: subring.mem_carrier -> Subring.mem_carrier is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Subring.{u1} R _inst_1} {x : R}, Iff (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x (Subring.carrier.{u1} R _inst_1 s)) (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Subring.{u1} R _inst_1} {x : R}, Iff (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (Subsemigroup.carrier.{u1} R (MulOneClass.toMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (Submonoid.toSubsemigroup.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s))))) (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)
Case conversion may be inaccurate. Consider using '#align subring.mem_carrier Subring.mem_carrierₓ'. -/
@[simp]
theorem mem_carrier {s : Subring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align subring.mem_carrier Subring.mem_carrier

@[simp]
theorem mem_mk {S : Set R} {x : R} (h₁ h₂ h₃ h₄ h₅) :
    x ∈ (⟨S, h₁, h₂, h₃, h₄, h₅⟩ : Subring R) ↔ x ∈ S :=
  Iff.rfl
#align subring.mem_mk Subring.mem_mkₓ

@[simp]
theorem coe_set_mk (S : Set R) (h₁ h₂ h₃ h₄ h₅) :
    ((⟨S, h₁, h₂, h₃, h₄, h₅⟩ : Subring R) : Set R) = S :=
  rfl
#align subring.coe_set_mk Subring.coe_set_mkₓ

@[simp]
theorem mk_le_mk {S S' : Set R} (h₁ h₂ h₃ h₄ h₅ h₁' h₂' h₃' h₄' h₅') :
    (⟨S, h₁, h₂, h₃, h₄, h₅⟩ : Subring R) ≤ (⟨S', h₁', h₂', h₃', h₄', h₅'⟩ : Subring R) ↔ S ⊆ S' :=
  Iff.rfl
#align subring.mk_le_mk Subring.mk_le_mkₓ

/- warning: subring.ext -> Subring.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Subring.{u1} R _inst_1} {T : Subring.{u1} R _inst_1}, (forall (x : R), Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x S) (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x T)) -> (Eq.{succ u1} (Subring.{u1} R _inst_1) S T)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Subring.{u1} R _inst_1} {T : Subring.{u1} R _inst_1}, (forall (x : R), Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x S) (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x T)) -> (Eq.{succ u1} (Subring.{u1} R _inst_1) S T)
Case conversion may be inaccurate. Consider using '#align subring.ext Subring.extₓ'. -/
/-- Two subrings are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align subring.ext Subring.ext

/- warning: subring.copy -> Subring.copy is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (S : Subring.{u1} R _inst_1) (s : Set.{u1} R), (Eq.{succ u1} (Set.{u1} R) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) S)) -> (Subring.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (S : Subring.{u1} R _inst_1) (s : Set.{u1} R), (Eq.{succ u1} (Set.{u1} R) s (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) S)) -> (Subring.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align subring.copy Subring.copyₓ'. -/
/-- Copy of a subring with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subring R) (s : Set R) (hs : s = ↑S) : Subring R :=
  { S.toSubsemiring.copy s hs with
    carrier := s
    neg_mem' := fun _ => hs.symm ▸ S.neg_mem' }
#align subring.copy Subring.copy

/- warning: subring.coe_copy -> Subring.coe_copy is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (S : Subring.{u1} R _inst_1) (s : Set.{u1} R) (hs : Eq.{succ u1} (Set.{u1} R) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) S)), Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.copy.{u1} R _inst_1 S s hs)) s
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (S : Subring.{u1} R _inst_1) (s : Set.{u1} R) (hs : Eq.{succ u1} (Set.{u1} R) s (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) S)), Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Subring.copy.{u1} R _inst_1 S s hs)) s
Case conversion may be inaccurate. Consider using '#align subring.coe_copy Subring.coe_copyₓ'. -/
@[simp]
theorem coe_copy (S : Subring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl
#align subring.coe_copy Subring.coe_copy

/- warning: subring.copy_eq -> Subring.copy_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (S : Subring.{u1} R _inst_1) (s : Set.{u1} R) (hs : Eq.{succ u1} (Set.{u1} R) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) S)), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.copy.{u1} R _inst_1 S s hs) S
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (S : Subring.{u1} R _inst_1) (s : Set.{u1} R) (hs : Eq.{succ u1} (Set.{u1} R) s (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) S)), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.copy.{u1} R _inst_1 S s hs) S
Case conversion may be inaccurate. Consider using '#align subring.copy_eq Subring.copy_eqₓ'. -/
theorem copy_eq (S : Subring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align subring.copy_eq Subring.copy_eq

#print Subring.toSubsemiring_injective /-
theorem toSubsemiring_injective : Function.Injective (toSubsemiring : Subring R → Subsemiring R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)
#align subring.to_subsemiring_injective Subring.toSubsemiring_injective
-/

/- warning: subring.to_subsemiring_strict_mono -> Subring.toSubsemiring_strictMono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], StrictMono.{u1, u1} (Subring.{u1} R _inst_1) (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (SetLike.partialOrder.{u1, u1} (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) R (Subsemiring.setLike.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Subring.toSubsemiring.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], StrictMono.{u1, u1} (Subring.{u1} R _inst_1) (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.instPartialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Subsemiring.instCompleteLatticeSubsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) (Subring.toSubsemiring.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align subring.to_subsemiring_strict_mono Subring.toSubsemiring_strictMonoₓ'. -/
@[mono]
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : Subring R → Subsemiring R) :=
  fun _ _ => id
#align subring.to_subsemiring_strict_mono Subring.toSubsemiring_strictMono

/- warning: subring.to_subsemiring_mono -> Subring.toSubsemiring_mono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Monotone.{u1, u1} (Subring.{u1} R _inst_1) (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (SetLike.partialOrder.{u1, u1} (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) R (Subsemiring.setLike.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Subring.toSubsemiring.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Monotone.{u1, u1} (Subring.{u1} R _inst_1) (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.instPartialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Subsemiring.instCompleteLatticeSubsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) (Subring.toSubsemiring.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align subring.to_subsemiring_mono Subring.toSubsemiring_monoₓ'. -/
@[mono]
theorem toSubsemiring_mono : Monotone (toSubsemiring : Subring R → Subsemiring R) :=
  toSubsemiring_strictMono.Monotone
#align subring.to_subsemiring_mono Subring.toSubsemiring_mono

/- warning: subring.to_add_subgroup_injective -> Subring.toAddSubgroup_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Function.Injective.{succ u1, succ u1} (Subring.{u1} R _inst_1) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Subring.toAddSubgroup.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Function.Injective.{succ u1, succ u1} (Subring.{u1} R _inst_1) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (Subring.toAddSubgroup.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align subring.to_add_subgroup_injective Subring.toAddSubgroup_injectiveₓ'. -/
theorem toAddSubgroup_injective : Function.Injective (toAddSubgroup : Subring R → AddSubgroup R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)
#align subring.to_add_subgroup_injective Subring.toAddSubgroup_injective

/- warning: subring.to_add_subgroup_strict_mono -> Subring.toAddSubgroup_strictMono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], StrictMono.{u1, u1} (Subring.{u1} R _inst_1) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) (Subring.toAddSubgroup.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], StrictMono.{u1, u1} (Subring.{u1} R _inst_1) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.instPartialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (AddSubgroup.instCompleteLatticeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)))))) (Subring.toAddSubgroup.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align subring.to_add_subgroup_strict_mono Subring.toAddSubgroup_strictMonoₓ'. -/
@[mono]
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Subring R → AddSubgroup R) :=
  fun _ _ => id
#align subring.to_add_subgroup_strict_mono Subring.toAddSubgroup_strictMono

/- warning: subring.to_add_subgroup_mono -> Subring.toAddSubgroup_mono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Monotone.{u1, u1} (Subring.{u1} R _inst_1) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) (Subring.toAddSubgroup.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Monotone.{u1, u1} (Subring.{u1} R _inst_1) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.instPartialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (AddSubgroup.instCompleteLatticeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)))))) (Subring.toAddSubgroup.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align subring.to_add_subgroup_mono Subring.toAddSubgroup_monoₓ'. -/
@[mono]
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Subring R → AddSubgroup R) :=
  toAddSubgroup_strictMono.Monotone
#align subring.to_add_subgroup_mono Subring.toAddSubgroup_mono

#print Subring.toSubmonoid_injective /-
theorem toSubmonoid_injective : Function.Injective ([anonymous] : Subring R → Submonoid R)
  | r, s, h => ext (SetLike.ext_iff.mp h : _)
#align subring.to_submonoid_injective Subring.toSubmonoid_injective
-/

#print Subring.toSubmonoid_strictMono /-
@[mono]
theorem toSubmonoid_strictMono : StrictMono ([anonymous] : Subring R → Submonoid R) := fun _ _ => id
#align subring.to_submonoid_strict_mono Subring.toSubmonoid_strictMono
-/

#print Subring.toSubmonoid_mono /-
@[mono]
theorem toSubmonoid_mono : Monotone ([anonymous] : Subring R → Submonoid R) :=
  toSubmonoid_strictMono.Monotone
#align subring.to_submonoid_mono Subring.toSubmonoid_mono
-/

/- warning: subring.mk' -> Subring.mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Set.{u1} R) (sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))), (Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) sm) s) -> (Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) sa) s) -> (Subring.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Set.{u1} R) (sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))), (Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) sm) s) -> (Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) sa) s) -> (Subring.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align subring.mk' Subring.mk'ₓ'. -/
/-- Construct a `subring R` from a set `s`, a submonoid `sm`, and an additive
subgroup `sa` such that `x ∈ s ↔ x ∈ sm ↔ x ∈ sa`. -/
protected def mk' (s : Set R) (sm : Submonoid R) (sa : AddSubgroup R) (hm : ↑sm = s)
    (ha : ↑sa = s) : Subring R where
  carrier := s
  zero_mem' := ha ▸ sa.zero_mem
  one_mem' := hm ▸ sm.one_mem
  add_mem' x y := by simpa only [← ha] using sa.add_mem
  mul_mem' x y := by simpa only [← hm] using sm.mul_mem
  neg_mem' x := by simpa only [← ha] using sa.neg_mem
#align subring.mk' Subring.mk'

/- warning: subring.coe_mk' -> Subring.coe_mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))} (hm : Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) sm) s) {sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))} (ha : Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) sa) s), Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.mk'.{u1} R _inst_1 s sm sa hm ha)) s
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))} (hm : Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) sm) s) {sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))} (ha : Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) sa) s), Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Subring.mk'.{u1} R _inst_1 s sm sa hm ha)) s
Case conversion may be inaccurate. Consider using '#align subring.coe_mk' Subring.coe_mk'ₓ'. -/
@[simp]
theorem coe_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) :
    (Subring.mk' s sm sa hm ha : Set R) = s :=
  rfl
#align subring.coe_mk' Subring.coe_mk'

/- warning: subring.mem_mk' -> Subring.mem_mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))} (hm : Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) sm) s) {sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))} (ha : Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) sa) s) {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Subring.mk'.{u1} R _inst_1 s sm sa hm ha)) (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))} (hm : Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) sm) s) {sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))} (ha : Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) sa) s) {x : R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.mk'.{u1} R _inst_1 s sm sa hm ha)) (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x s)
Case conversion may be inaccurate. Consider using '#align subring.mem_mk' Subring.mem_mk'ₓ'. -/
@[simp]
theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x ∈ Subring.mk' s sm sa hm ha ↔ x ∈ s :=
  Iff.rfl
#align subring.mem_mk' Subring.mem_mk'

/- warning: subring.mk'_to_submonoid -> Subring.mk'_toSubmonoid is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))} (hm : Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) sm) s) {sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))} (ha : Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) sa) s), Eq.{succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) ([anonymous].{u1} R _inst_1 (Subring.mk'.{u1} R _inst_1 s sm sa hm ha)) sm
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))} (hm : Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) sm) s) {sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))} (ha : Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) sa) s), Eq.{succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 (Subring.mk'.{u1} R _inst_1 s sm sa hm ha))) sm
Case conversion may be inaccurate. Consider using '#align subring.mk'_to_submonoid Subring.mk'_toSubmonoidₓ'. -/
@[simp]
theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid = sm :=
  SetLike.coe_injective hm.symm
#align subring.mk'_to_submonoid Subring.mk'_toSubmonoid

/- warning: subring.mk'_to_add_subgroup -> Subring.mk'_toAddSubgroup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))} (hm : Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) sm) s) {sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))} (ha : Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) sa) s), Eq.{succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Subring.toAddSubgroup.{u1} R _inst_1 (Subring.mk'.{u1} R _inst_1 s sm sa hm ha)) sa
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {sm : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))} (hm : Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) sm) s) {sa : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))} (ha : Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) sa) s), Eq.{succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (Subring.toAddSubgroup.{u1} R _inst_1 (Subring.mk'.{u1} R _inst_1 s sm sa hm ha)) sa
Case conversion may be inaccurate. Consider using '#align subring.mk'_to_add_subgroup Subring.mk'_toAddSubgroupₓ'. -/
@[simp]
theorem mk'_toAddSubgroup {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toAddSubgroup = sa :=
  SetLike.coe_injective ha.symm
#align subring.mk'_to_add_subgroup Subring.mk'_toAddSubgroup

end Subring

/- warning: subsemiring.to_subring -> Subsemiring.toSubring is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))), (Membership.Mem.{u1, u1} R (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (SetLike.hasMem.{u1, u1} (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) R (Subsemiring.setLike.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))) s) -> (Subring.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))), (Membership.mem.{u1, u1} R (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) R (Subsemiring.instSetLikeSubsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) s) -> (Subring.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align subsemiring.to_subring Subsemiring.toSubringₓ'. -/
/-- A `subsemiring` containing -1 is a `subring`. -/
def Subsemiring.toSubring (s : Subsemiring R) (hneg : (-1 : R) ∈ s) : Subring R :=
  { s.toSubmonoid, s.toAddSubmonoid with
    neg_mem' := by rintro x; rw [← neg_one_mul]; apply Subsemiring.mul_mem; exact hneg }
#align subsemiring.to_subring Subsemiring.toSubring

namespace Subring

variable (s : Subring R)

/- warning: subring.one_mem -> Subring.one_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) s
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) s
Case conversion may be inaccurate. Consider using '#align subring.one_mem Subring.one_memₓ'. -/
/-- A subring contains the ring's 1. -/
protected theorem one_mem : (1 : R) ∈ s :=
  one_mem _
#align subring.one_mem Subring.one_mem

/- warning: subring.zero_mem -> Subring.zero_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) s
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) s
Case conversion may be inaccurate. Consider using '#align subring.zero_mem Subring.zero_memₓ'. -/
/-- A subring contains the ring's 0. -/
protected theorem zero_mem : (0 : R) ∈ s :=
  zero_mem _
#align subring.zero_mem Subring.zero_mem

/- warning: subring.mul_mem -> Subring.mul_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R} {y : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) y s) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) x y) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R} {y : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) y s) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) x y) s)
Case conversion may be inaccurate. Consider using '#align subring.mul_mem Subring.mul_memₓ'. -/
/-- A subring is closed under multiplication. -/
protected theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem
#align subring.mul_mem Subring.mul_mem

/- warning: subring.add_mem -> Subring.add_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R} {y : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) y s) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1))) x y) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R} {y : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) y s) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x y) s)
Case conversion may be inaccurate. Consider using '#align subring.add_mem Subring.add_memₓ'. -/
/-- A subring is closed under addition. -/
protected theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem
#align subring.add_mem Subring.add_mem

/- warning: subring.neg_mem -> Subring.neg_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) x) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) x) s)
Case conversion may be inaccurate. Consider using '#align subring.neg_mem Subring.neg_memₓ'. -/
/-- A subring is closed under negation. -/
protected theorem neg_mem {x : R} : x ∈ s → -x ∈ s :=
  neg_mem
#align subring.neg_mem Subring.neg_mem

/- warning: subring.sub_mem -> Subring.sub_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R} {y : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) y s) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) x y) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R} {y : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) y s) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R _inst_1)) x y) s)
Case conversion may be inaccurate. Consider using '#align subring.sub_mem Subring.sub_memₓ'. -/
/-- A subring is closed under subtraction -/
protected theorem sub_mem {x y : R} (hx : x ∈ s) (hy : y ∈ s) : x - y ∈ s :=
  sub_mem hx hy
#align subring.sub_mem Subring.sub_mem

/- warning: subring.list_prod_mem -> Subring.list_prod_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {l : List.{u1} R}, (forall (x : R), (Membership.Mem.{u1, u1} R (List.{u1} R) (List.hasMem.{u1} R) x l) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s)) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (List.prod.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) l) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {l : List.{u1} R}, (forall (x : R), (Membership.mem.{u1, u1} R (List.{u1} R) (List.instMembershipList.{u1} R) x l) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (List.prod.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1)) l) s)
Case conversion may be inaccurate. Consider using '#align subring.list_prod_mem Subring.list_prod_memₓ'. -/
/-- Product of a list of elements in a subring is in the subring. -/
protected theorem list_prod_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.Prod ∈ s :=
  list_prod_mem
#align subring.list_prod_mem Subring.list_prod_mem

/- warning: subring.list_sum_mem -> Subring.list_sum_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {l : List.{u1} R}, (forall (x : R), (Membership.Mem.{u1, u1} R (List.{u1} R) (List.hasMem.{u1} R) x l) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s)) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) l) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {l : List.{u1} R}, (forall (x : R), (Membership.mem.{u1, u1} R (List.{u1} R) (List.instMembershipList.{u1} R) x l) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) l) s)
Case conversion may be inaccurate. Consider using '#align subring.list_sum_mem Subring.list_sum_memₓ'. -/
/-- Sum of a list of elements in a subring is in the subring. -/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.Sum ∈ s :=
  list_sum_mem
#align subring.list_sum_mem Subring.list_sum_mem

/- warning: subring.multiset_prod_mem -> Subring.multiset_prod_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : CommRing.{u1} R] (s : Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (m : Multiset.{u1} R), (forall (a : R), (Membership.Mem.{u1, u1} R (Multiset.{u1} R) (Multiset.hasMem.{u1} R) a m) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (SetLike.hasMem.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_4))) a s)) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (SetLike.hasMem.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_4))) (Multiset.prod.{u1} R (CommRing.toCommMonoid.{u1} R _inst_4) m) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : CommRing.{u1} R] (s : Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (m : Multiset.{u1} R), (forall (a : R), (Membership.mem.{u1, u1} R (Multiset.{u1} R) (Multiset.instMembershipMultiset.{u1} R) a m) -> (Membership.mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) R (Subring.instSetLikeSubring.{u1} R (CommRing.toRing.{u1} R _inst_4))) a s)) -> (Membership.mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) R (Subring.instSetLikeSubring.{u1} R (CommRing.toRing.{u1} R _inst_4))) (Multiset.prod.{u1} R (CommRing.toCommMonoid.{u1} R _inst_4) m) s)
Case conversion may be inaccurate. Consider using '#align subring.multiset_prod_mem Subring.multiset_prod_memₓ'. -/
/-- Product of a multiset of elements in a subring of a `comm_ring` is in the subring. -/
protected theorem multiset_prod_mem {R} [CommRing R] (s : Subring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.Prod ∈ s :=
  multiset_prod_mem _
#align subring.multiset_prod_mem Subring.multiset_prod_mem

/- warning: subring.multiset_sum_mem -> Subring.multiset_sum_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : Ring.{u1} R] (s : Subring.{u1} R _inst_4) (m : Multiset.{u1} R), (forall (a : R), (Membership.Mem.{u1, u1} R (Multiset.{u1} R) (Multiset.hasMem.{u1} R) a m) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_4) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_4) R (Subring.setLike.{u1} R _inst_4)) a s)) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_4) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_4) R (Subring.setLike.{u1} R _inst_4)) (Multiset.sum.{u1} R (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_4)))) m) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : Ring.{u1} R] (s : Subring.{u1} R _inst_4) (m : Multiset.{u1} R), (forall (a : R), (Membership.mem.{u1, u1} R (Multiset.{u1} R) (Multiset.instMembershipMultiset.{u1} R) a m) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_4) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_4) R (Subring.instSetLikeSubring.{u1} R _inst_4)) a s)) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_4) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_4) R (Subring.instSetLikeSubring.{u1} R _inst_4)) (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_4)))) m) s)
Case conversion may be inaccurate. Consider using '#align subring.multiset_sum_mem Subring.multiset_sum_memₓ'. -/
/-- Sum of a multiset of elements in an `subring` of a `ring` is
in the `subring`. -/
protected theorem multiset_sum_mem {R} [Ring R] (s : Subring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.Sum ∈ s :=
  multiset_sum_mem _
#align subring.multiset_sum_mem Subring.multiset_sum_mem

/- warning: subring.prod_mem -> Subring.prod_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : CommRing.{u1} R] (s : Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) {ι : Type.{u2}} {t : Finset.{u2} ι} {f : ι -> R}, (forall (c : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) c t) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (SetLike.hasMem.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_4))) (f c) s)) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (SetLike.hasMem.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_4))) (Finset.prod.{u1, u2} R ι (CommRing.toCommMonoid.{u1} R _inst_4) t (fun (i : ι) => f i)) s)
but is expected to have type
  forall {R : Type.{u2}} [_inst_4 : CommRing.{u2} R] (s : Subring.{u2} R (CommRing.toRing.{u2} R _inst_4)) {ι : Type.{u1}} {t : Finset.{u1} ι} {f : ι -> R}, (forall (c : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) c t) -> (Membership.mem.{u2, u2} R (Subring.{u2} R (CommRing.toRing.{u2} R _inst_4)) (SetLike.instMembership.{u2, u2} (Subring.{u2} R (CommRing.toRing.{u2} R _inst_4)) R (Subring.instSetLikeSubring.{u2} R (CommRing.toRing.{u2} R _inst_4))) (f c) s)) -> (Membership.mem.{u2, u2} R (Subring.{u2} R (CommRing.toRing.{u2} R _inst_4)) (SetLike.instMembership.{u2, u2} (Subring.{u2} R (CommRing.toRing.{u2} R _inst_4)) R (Subring.instSetLikeSubring.{u2} R (CommRing.toRing.{u2} R _inst_4))) (Finset.prod.{u2, u1} R ι (CommRing.toCommMonoid.{u2} R _inst_4) t (fun (i : ι) => f i)) s)
Case conversion may be inaccurate. Consider using '#align subring.prod_mem Subring.prod_memₓ'. -/
/-- Product of elements of a subring of a `comm_ring` indexed by a `finset` is in the
    subring. -/
protected theorem prod_mem {R : Type _} [CommRing R] (s : Subring R) {ι : Type _} {t : Finset ι}
    {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∏ i in t, f i) ∈ s :=
  prod_mem h
#align subring.prod_mem Subring.prod_mem

/- warning: subring.sum_mem -> Subring.sum_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : Ring.{u1} R] (s : Subring.{u1} R _inst_4) {ι : Type.{u2}} {t : Finset.{u2} ι} {f : ι -> R}, (forall (c : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) c t) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_4) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_4) R (Subring.setLike.{u1} R _inst_4)) (f c) s)) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_4) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_4) R (Subring.setLike.{u1} R _inst_4)) (Finset.sum.{u1, u2} R ι (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_4)))) t (fun (i : ι) => f i)) s)
but is expected to have type
  forall {R : Type.{u2}} [_inst_4 : Ring.{u2} R] (s : Subring.{u2} R _inst_4) {ι : Type.{u1}} {t : Finset.{u1} ι} {f : ι -> R}, (forall (c : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) c t) -> (Membership.mem.{u2, u2} R (Subring.{u2} R _inst_4) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_4) R (Subring.instSetLikeSubring.{u2} R _inst_4)) (f c) s)) -> (Membership.mem.{u2, u2} R (Subring.{u2} R _inst_4) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_4) R (Subring.instSetLikeSubring.{u2} R _inst_4)) (Finset.sum.{u2, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_4)))) t (fun (i : ι) => f i)) s)
Case conversion may be inaccurate. Consider using '#align subring.sum_mem Subring.sum_memₓ'. -/
/-- Sum of elements in a `subring` of a `ring` indexed by a `finset`
is in the `subring`. -/
protected theorem sum_mem {R : Type _} [Ring R] (s : Subring R) {ι : Type _} {t : Finset ι}
    {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i in t, f i) ∈ s :=
  sum_mem h
#align subring.sum_mem Subring.sum_mem

/- warning: subring.to_ring -> Subring.toRing is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Ring.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Ring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s))
Case conversion may be inaccurate. Consider using '#align subring.to_ring Subring.toRingₓ'. -/
/-- A subring of a ring inherits a ring structure -/
instance toRing : Ring s :=
  Subtype.coe_injective.Ring coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring.to_ring Subring.toRing

/- warning: subring.zsmul_mem -> Subring.zsmul_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s) -> (forall (n : Int), Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (SMul.smul.{0, u1} Int R (SubNegMonoid.SMulInt.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) n x) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s) -> (forall (n : Int), Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (HSMul.hSMul.{0, u1, u1} Int R R (instHSMul.{0, u1} Int R (SubNegMonoid.SMulInt.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))))) n x) s)
Case conversion may be inaccurate. Consider using '#align subring.zsmul_mem Subring.zsmul_memₓ'. -/
protected theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n
#align subring.zsmul_mem Subring.zsmul_mem

/- warning: subring.pow_mem -> Subring.pow_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s) -> (forall (n : Nat), Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1))) x n) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s) -> (forall (n : Nat), Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) x n) s)
Case conversion may be inaccurate. Consider using '#align subring.pow_mem Subring.pow_memₓ'. -/
protected theorem pow_mem {x : R} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n
#align subring.pow_mem Subring.pow_mem

/- warning: subring.coe_add -> Subring.coe_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (x : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (y : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) (HAdd.hAdd.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (instHAdd.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (AddMemClass.add.{u1, u1} R (Subring.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.setLike.{u1} R _inst_1) (AddSubmonoidClass.to_addMemClass.{u1, u1} (Subring.{u1} R _inst_1) R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (Subring.setLike.{u1} R _inst_1) (SubsemiringClass.to_addSubmonoidClass.{u1, u1} (Subring.{u1} R _inst_1) R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (Subring.setLike.{u1} R _inst_1) (SubringClass.to_subsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.setLike.{u1} R _inst_1) (Subring.subringClass.{u1} R _inst_1)))) s)) x y)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (x : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (y : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) (HAdd.hAdd.{u1, u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (instHAdd.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Distrib.toAdd.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonUnitalNonAssocSemiring.toDistrib.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Ring.toNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subring.toRing.{u1} R _inst_1 s))))))) x y)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) x) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) y))
Case conversion may be inaccurate. Consider using '#align subring.coe_add Subring.coe_addₓ'. -/
@[simp, norm_cast]
theorem coe_add (x y : s) : (↑(x + y) : R) = ↑x + ↑y :=
  rfl
#align subring.coe_add Subring.coe_add

/- warning: subring.coe_neg -> Subring.coe_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (x : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) (Neg.neg.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (AddSubgroupClass.neg.{u1, u1} R (Subring.{u1} R _inst_1) (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Subring.setLike.{u1} R _inst_1) (SubringClass.addSubgroupClass.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1) _inst_1 (Subring.subringClass.{u1} R _inst_1)) s) x)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (x : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) (Neg.neg.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (AddSubgroupClass.neg.{u1, u1} R (Subring.{u1} R _inst_1) (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (Subring.instSetLikeSubring.{u1} R _inst_1) (SubringClass.addSubgroupClass.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) _inst_1 (Subring.instSubringClassSubringInstSetLikeSubring.{u1} R _inst_1)) s) x)) (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) x))
Case conversion may be inaccurate. Consider using '#align subring.coe_neg Subring.coe_negₓ'. -/
@[simp, norm_cast]
theorem coe_neg (x : s) : (↑(-x) : R) = -↑x :=
  rfl
#align subring.coe_neg Subring.coe_neg

/- warning: subring.coe_mul -> Subring.coe_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (x : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (y : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (MulMemClass.mul.{u1, u1} R (Subring.{u1} R _inst_1) (MulOneClass.toHasMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Subring.setLike.{u1} R _inst_1) (SubmonoidClass.to_mulMemClass.{u1, u1} (Subring.{u1} R _inst_1) R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Subring.setLike.{u1} R _inst_1) (SubsemiringClass.to_submonoidClass.{u1, u1} (Subring.{u1} R _inst_1) R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (Subring.setLike.{u1} R _inst_1) (SubringClass.to_subsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.setLike.{u1} R _inst_1) (Subring.subringClass.{u1} R _inst_1)))) s)) x y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (x : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (y : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (instHMul.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Submonoid.mul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)))) x y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) x) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) y))
Case conversion may be inaccurate. Consider using '#align subring.coe_mul Subring.coe_mulₓ'. -/
@[simp, norm_cast]
theorem coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y :=
  rfl
#align subring.coe_mul Subring.coe_mul

/- warning: subring.coe_zero -> Subring.coe_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) (OfNat.ofNat.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) 0 (OfNat.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) 0 (Zero.zero.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (ZeroMemClass.zero.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1) (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (AddSubmonoidClass.to_zeroMemClass.{u1, u1} (Subring.{u1} R _inst_1) R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (Subring.setLike.{u1} R _inst_1) (SubsemiringClass.to_addSubmonoidClass.{u1, u1} (Subring.{u1} R _inst_1) R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (Subring.setLike.{u1} R _inst_1) (SubringClass.to_subsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.setLike.{u1} R _inst_1) (Subring.subringClass.{u1} R _inst_1)))) s))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) 0 (Zero.toOfNat0.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (ZeroMemClass.zero.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (AddSubmonoidClass.toZeroMemClass.{u1, u1} (Subring.{u1} R _inst_1) R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)))) (Subring.instSetLikeSubring.{u1} R _inst_1) (SubsemiringClass.toAddSubmonoidClass.{u1, u1} (Subring.{u1} R _inst_1) R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.instSetLikeSubring.{u1} R _inst_1) (SubringClass.toSubsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.instSetLikeSubring.{u1} R _inst_1) (Subring.instSubringClassSubringInstSetLikeSubring.{u1} R _inst_1)))) s)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align subring.coe_zero Subring.coe_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_zero : ((0 : s) : R) = 0 :=
  rfl
#align subring.coe_zero Subring.coe_zero

/- warning: subring.coe_one -> Subring.coe_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) (OfNat.ofNat.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) 1 (OfNat.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) 1 (One.one.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (OneMemClass.one.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (AddSubmonoidWithOneClass.to_oneMemClass.{u1, u1} (Subring.{u1} R _inst_1) R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Subring.setLike.{u1} R _inst_1) (SubsemiringClass.addSubmonoidWithOneClass.{u1, u1} (Subring.{u1} R _inst_1) R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (Subring.setLike.{u1} R _inst_1) (SubringClass.to_subsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.setLike.{u1} R _inst_1) (Subring.subringClass.{u1} R _inst_1)))) s))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Submonoid.one.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)))))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align subring.coe_one Subring.coe_oneₓ'. -/
@[simp, norm_cast]
theorem coe_one : ((1 : s) : R) = 1 :=
  rfl
#align subring.coe_one Subring.coe_one

/- warning: subring.coe_pow -> Subring.coe_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (x : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (n : Nat), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) (HPow.hPow.{u1, 0, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) Nat (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (instHPow.{u1, 0} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) Nat (SubmonoidClass.nPow.{u1, u1} R (Ring.toMonoid.{u1} R _inst_1) (Subring.{u1} R _inst_1) (Subring.setLike.{u1} R _inst_1) (SubsemiringClass.to_submonoidClass.{u1, u1} (Subring.{u1} R _inst_1) R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (Subring.setLike.{u1} R _inst_1) (SubringClass.to_subsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.setLike.{u1} R _inst_1) (Subring.subringClass.{u1} R _inst_1))) s)) x n)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) x) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (x : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (n : Nat), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) (HPow.hPow.{u1, 0, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) Nat (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (instHPow.{u1, 0} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) Nat (SubmonoidClass.nPow.{u1, u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Subring.{u1} R _inst_1) (Subring.instSetLikeSubring.{u1} R _inst_1) (SubsemiringClass.toSubmonoidClass.{u1, u1} (Subring.{u1} R _inst_1) R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.instSetLikeSubring.{u1} R _inst_1) (SubringClass.toSubsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.instSetLikeSubring.{u1} R _inst_1) (Subring.instSubringClassSubringInstSetLikeSubring.{u1} R _inst_1))) s)) x n)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) x) n)
Case conversion may be inaccurate. Consider using '#align subring.coe_pow Subring.coe_powₓ'. -/
@[simp, norm_cast]
theorem coe_pow (x : s) (n : ℕ) : (↑(x ^ n) : R) = x ^ n :=
  SubmonoidClass.coe_pow x n
#align subring.coe_pow Subring.coe_pow

/- warning: subring.coe_eq_zero_iff -> Subring.coe_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s}, Iff (Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) x) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))) (Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) x (OfNat.ofNat.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) 0 (OfNat.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) 0 (Zero.zero.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (ZeroMemClass.zero.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1) (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (AddSubmonoidClass.to_zeroMemClass.{u1, u1} (Subring.{u1} R _inst_1) R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) (Subring.setLike.{u1} R _inst_1) (SubsemiringClass.to_addSubmonoidClass.{u1, u1} (Subring.{u1} R _inst_1) R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (Subring.setLike.{u1} R _inst_1) (SubringClass.to_subsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.setLike.{u1} R _inst_1) (Subring.subringClass.{u1} R _inst_1)))) s)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) {x : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)}, Iff (Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) x) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) (Eq.{succ u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) x (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) 0 (Zero.toOfNat0.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (ZeroMemClass.zero.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (AddSubmonoidClass.toZeroMemClass.{u1, u1} (Subring.{u1} R _inst_1) R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)))) (Subring.instSetLikeSubring.{u1} R _inst_1) (SubsemiringClass.toAddSubmonoidClass.{u1, u1} (Subring.{u1} R _inst_1) R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.instSetLikeSubring.{u1} R _inst_1) (SubringClass.toSubsemiringClass.{u1, u1} (Subring.{u1} R _inst_1) R _inst_1 (Subring.instSetLikeSubring.{u1} R _inst_1) (Subring.instSubringClassSubringInstSetLikeSubring.{u1} R _inst_1)))) s))))
Case conversion may be inaccurate. Consider using '#align subring.coe_eq_zero_iff Subring.coe_eq_zero_iffₓ'. -/
-- TODO: can be generalized to `add_submonoid_class`
@[simp]
theorem coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0 :=
  ⟨fun h => Subtype.ext (trans h s.val_zero.symm), fun h => h.symm ▸ s.val_zero⟩
#align subring.coe_eq_zero_iff Subring.coe_eq_zero_iff

/- warning: subring.to_comm_ring -> Subring.toCommRing is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : CommRing.{u1} R] (s : Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)), CommRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) R (Subring.setLike.{u1} R (CommRing.toRing.{u1} R _inst_4))) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : CommRing.{u1} R] (s : Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)), CommRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) R (Subring.instSetLikeSubring.{u1} R (CommRing.toRing.{u1} R _inst_4))) x s))
Case conversion may be inaccurate. Consider using '#align subring.to_comm_ring Subring.toCommRingₓ'. -/
/-- A subring of a `comm_ring` is a `comm_ring`. -/
instance toCommRing {R} [CommRing R] (s : Subring R) : CommRing s :=
  Subtype.coe_injective.CommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring.to_comm_ring Subring.toCommRing

/-- A subring of a non-trivial ring is non-trivial. -/
instance {R} [Ring R] [Nontrivial R] (s : Subring R) : Nontrivial s :=
  s.toSubsemiring.Nontrivial

/-- A subring of a ring with no zero divisors has no zero divisors. -/
instance {R} [Ring R] [NoZeroDivisors R] (s : Subring R) : NoZeroDivisors s :=
  s.toSubsemiring.NoZeroDivisors

/-- A subring of a domain is a domain. -/
instance {R} [Ring R] [IsDomain R] (s : Subring R) : IsDomain s :=
  NoZeroDivisors.to_isDomain _

/- warning: subring.to_ordered_ring -> Subring.toOrderedRing is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : OrderedRing.{u1} R] (s : Subring.{u1} R (OrderedRing.toRing.{u1} R _inst_4)), OrderedRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (OrderedRing.toRing.{u1} R _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (OrderedRing.toRing.{u1} R _inst_4)) R (Subring.setLike.{u1} R (OrderedRing.toRing.{u1} R _inst_4))) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : OrderedRing.{u1} R] (s : Subring.{u1} R (OrderedRing.toRing.{u1} R _inst_4)), OrderedRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R (OrderedRing.toRing.{u1} R _inst_4)) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (OrderedRing.toRing.{u1} R _inst_4)) R (Subring.instSetLikeSubring.{u1} R (OrderedRing.toRing.{u1} R _inst_4))) x s))
Case conversion may be inaccurate. Consider using '#align subring.to_ordered_ring Subring.toOrderedRingₓ'. -/
/-- A subring of an `ordered_ring` is an `ordered_ring`. -/
instance toOrderedRing {R} [OrderedRing R] (s : Subring R) : OrderedRing s :=
  Subtype.coe_injective.OrderedRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring.to_ordered_ring Subring.toOrderedRing

/- warning: subring.to_ordered_comm_ring -> Subring.toOrderedCommRing is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : OrderedCommRing.{u1} R] (s : Subring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_4))), OrderedCommRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_4))) R (Subring.setLike.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_4)))) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : OrderedCommRing.{u1} R] (s : Subring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_4))), OrderedCommRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_4))) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_4))) R (Subring.instSetLikeSubring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_4)))) x s))
Case conversion may be inaccurate. Consider using '#align subring.to_ordered_comm_ring Subring.toOrderedCommRingₓ'. -/
/-- A subring of an `ordered_comm_ring` is an `ordered_comm_ring`. -/
instance toOrderedCommRing {R} [OrderedCommRing R] (s : Subring R) : OrderedCommRing s :=
  Subtype.coe_injective.OrderedCommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
#align subring.to_ordered_comm_ring Subring.toOrderedCommRing

/- warning: subring.to_linear_ordered_ring -> Subring.toLinearOrderedRing is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : LinearOrderedRing.{u1} R] (s : Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_4))), LinearOrderedRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_4))) R (Subring.setLike.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_4)))) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : LinearOrderedRing.{u1} R] (s : Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_4))), LinearOrderedRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_4))) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_4))) R (Subring.instSetLikeSubring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R _inst_4)))) x s))
Case conversion may be inaccurate. Consider using '#align subring.to_linear_ordered_ring Subring.toLinearOrderedRingₓ'. -/
/-- A subring of a `linear_ordered_ring` is a `linear_ordered_ring`. -/
instance toLinearOrderedRing {R} [LinearOrderedRing R] (s : Subring R) : LinearOrderedRing s :=
  Subtype.coe_injective.LinearOrderedRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subring.to_linear_ordered_ring Subring.toLinearOrderedRing

/- warning: subring.to_linear_ordered_comm_ring -> Subring.toLinearOrderedCommRing is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : LinearOrderedCommRing.{u1} R] (s : Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_4)))), LinearOrderedCommRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_4)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_4)))) R (Subring.setLike.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_4))))) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : LinearOrderedCommRing.{u1} R] (s : Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_4)))), LinearOrderedCommRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_4)))) (SetLike.instMembership.{u1, u1} (Subring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_4)))) R (Subring.instSetLikeSubring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_4))))) x s))
Case conversion may be inaccurate. Consider using '#align subring.to_linear_ordered_comm_ring Subring.toLinearOrderedCommRingₓ'. -/
/-- A subring of a `linear_ordered_comm_ring` is a `linear_ordered_comm_ring`. -/
instance toLinearOrderedCommRing {R} [LinearOrderedCommRing R] (s : Subring R) :
    LinearOrderedCommRing s :=
  Subtype.coe_injective.LinearOrderedCommRing coe rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subring.to_linear_ordered_comm_ring Subring.toLinearOrderedCommRing

/- warning: subring.subtype -> Subring.subtype is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), RingHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (NonAssocRing.toNonAssocSemiring.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Ring.toNonAssocRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Subring.toRing.{u1} R _inst_1 s))) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), RingHom.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align subring.subtype Subring.subtypeₓ'. -/
/-- The natural ring hom from a subring of ring `R` to `R`. -/
def subtype (s : Subring R) : s →+* R :=
  { s.toSubmonoid.Subtype, s.toAddSubgroup.Subtype with toFun := coe }
#align subring.subtype Subring.subtype

/- warning: subring.coe_subtype -> Subring.coeSubtype is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} ((coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) -> R) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (NonAssocRing.toNonAssocSemiring.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Ring.toNonAssocRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Subring.toRing.{u1} R _inst_1 s))) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (NonAssocRing.toNonAssocSemiring.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Ring.toNonAssocRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Subring.toRing.{u1} R _inst_1 s))) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) => (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) -> R) (RingHom.hasCoeToFun.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (NonAssocRing.toNonAssocSemiring.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Ring.toNonAssocRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Subring.toRing.{u1} R _inst_1 s))) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (Subring.subtype.{u1} R _inst_1 s)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} (forall (ᾰ : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) => R) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (fun (_x : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) => R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (NonUnitalNonAssocSemiring.toMul.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) (Subring.subtype.{u1} R _inst_1 s)) (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align subring.coe_subtype Subring.coeSubtypeₓ'. -/
@[simp]
theorem coeSubtype : ⇑s.Subtype = coe :=
  rfl
#align subring.coe_subtype Subring.coeSubtype

/- warning: subring.coe_nat_cast -> Subring.coe_natCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (n : Nat), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (HasLiftT.mk.{1, succ u1} Nat (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (CoeTCₓ.coe.{1, succ u1} Nat (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Nat.castCoe.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (AddMonoidWithOne.toNatCast.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (AddGroupWithOne.toAddMonoidWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Ring.toAddCommGroupWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Subring.toRing.{u1} R _inst_1 s)))))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (n : Nat), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) (Nat.cast.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Semiring.toNatCast.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subsemiring.toSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1) (Subring.toSubsemiring.{u1} R _inst_1 s))) n)) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (Ring.toSemiring.{u1} R _inst_1)) n)
Case conversion may be inaccurate. Consider using '#align subring.coe_nat_cast Subring.coe_natCastₓ'. -/
@[simp, norm_cast]
theorem coe_natCast : ∀ n : ℕ, ((n : s) : R) = n :=
  map_natCast s.Subtype
#align subring.coe_nat_cast Subring.coe_natCast

/- warning: subring.coe_int_cast -> Subring.coe_intCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (n : Int), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (HasLiftT.mk.{1, succ u1} Int (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (CoeTCₓ.coe.{1, succ u1} Int (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Int.castCoe.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (AddGroupWithOne.toHasIntCast.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Ring.toAddCommGroupWithOne.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (Subring.toRing.{u1} R _inst_1 s))))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1) (n : Int), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)) (Int.cast.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Ring.toIntCast.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subring.toRing.{u1} R _inst_1 s)) n)) (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1) n)
Case conversion may be inaccurate. Consider using '#align subring.coe_int_cast Subring.coe_intCastₓ'. -/
@[simp, norm_cast]
theorem coe_intCast : ∀ n : ℤ, ((n : s) : R) = n :=
  map_intCast s.Subtype
#align subring.coe_int_cast Subring.coe_intCast

/-! ## Partial order -/


/- warning: subring.mem_to_submonoid -> Subring.mem_toSubmonoid is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Subring.{u1} R _inst_1} {x : R}, Iff (Membership.Mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x ([anonymous].{u1} R _inst_1 s)) (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Subring.{u1} R _inst_1} {x : R}, Iff (Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) x (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s))) (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)
Case conversion may be inaccurate. Consider using '#align subring.mem_to_submonoid Subring.mem_toSubmonoidₓ'. -/
@[simp]
theorem mem_toSubmonoid {s : Subring R} {x : R} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl
#align subring.mem_to_submonoid Subring.mem_toSubmonoid

/- warning: subring.coe_to_submonoid -> Subring.coe_toSubmonoid is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) ([anonymous].{u1} R _inst_1 s)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s))) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)
Case conversion may be inaccurate. Consider using '#align subring.coe_to_submonoid Subring.coe_toSubmonoidₓ'. -/
@[simp]
theorem coe_toSubmonoid (s : Subring R) : (s.toSubmonoid : Set R) = s :=
  rfl
#align subring.coe_to_submonoid Subring.coe_toSubmonoid

/- warning: subring.mem_to_add_subgroup -> Subring.mem_toAddSubgroup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Subring.{u1} R _inst_1} {x : R}, Iff (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) x (Subring.toAddSubgroup.{u1} R _inst_1 s)) (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Subring.{u1} R _inst_1} {x : R}, Iff (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)))) x (Subring.toAddSubgroup.{u1} R _inst_1 s)) (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)
Case conversion may be inaccurate. Consider using '#align subring.mem_to_add_subgroup Subring.mem_toAddSubgroupₓ'. -/
@[simp]
theorem mem_toAddSubgroup {s : Subring R} {x : R} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl
#align subring.mem_to_add_subgroup Subring.mem_toAddSubgroup

/- warning: subring.coe_to_add_subgroup -> Subring.coe_toAddSubgroup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))) (Subring.toAddSubgroup.{u1} R _inst_1 s)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) s)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (Subring.toAddSubgroup.{u1} R _inst_1 s)) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)
Case conversion may be inaccurate. Consider using '#align subring.coe_to_add_subgroup Subring.coe_toAddSubgroupₓ'. -/
@[simp]
theorem coe_toAddSubgroup (s : Subring R) : (s.toAddSubgroup : Set R) = s :=
  rfl
#align subring.coe_to_add_subgroup Subring.coe_toAddSubgroup

/-! ## top -/


/-- The subring `R` of the ring `R`. -/
instance : Top (Subring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubgroup R) with }⟩

/- warning: subring.mem_top -> Subring.mem_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (x : R), Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (x : R), Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align subring.mem_top Subring.mem_topₓ'. -/
@[simp]
theorem mem_top (x : R) : x ∈ (⊤ : Subring R) :=
  Set.mem_univ x
#align subring.mem_top Subring.mem_top

/- warning: subring.coe_top -> Subring.coe_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))) (Set.univ.{u1} R)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1))) (Set.univ.{u1} R)
Case conversion may be inaccurate. Consider using '#align subring.coe_top Subring.coe_topₓ'. -/
@[simp]
theorem coe_top : ((⊤ : Subring R) : Set R) = Set.univ :=
  rfl
#align subring.coe_top Subring.coe_top

/- warning: subring.top_equiv -> Subring.topEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], RingEquiv.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))) R (MulMemClass.mul.{u1, u1} R (Subring.{u1} R _inst_1) (MulOneClass.toHasMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Subring.setLike.{u1} R _inst_1) (Subring.topEquiv._proof_1.{u1} R _inst_1) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))) (AddMemClass.add.{u1, u1} R (Subring.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.setLike.{u1} R _inst_1) (Subring.topEquiv._proof_2.{u1} R _inst_1) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], RingEquiv.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))) R (Submonoid.mul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1))))) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (Distrib.toAdd.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toDistrib.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))) (Ring.toNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))) (Subring.toRing.{u1} R _inst_1 (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))))))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align subring.top_equiv Subring.topEquivₓ'. -/
/-- The ring equiv between the top element of `subring R` and `R`. -/
@[simps]
def topEquiv : (⊤ : Subring R) ≃+* R :=
  Subsemiring.topEquiv
#align subring.top_equiv Subring.topEquiv

/-! ## comap -/


#print Subring.comap /-
/-- The preimage of a subring along a ring homomorphism is a subring. -/
def comap {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (s : Subring S) : Subring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubgroup.comap (f : R →+ S) with
    carrier := f ⁻¹' s.carrier }
#align subring.comap Subring.comap
-/

/- warning: subring.coe_comap -> Subring.coe_comap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u2} S _inst_2) (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f s)) (Set.preimage.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subring.{u2} S _inst_2) (Set.{u2} S) (HasLiftT.mk.{succ u2, succ u2} (Subring.{u2} S _inst_2) (Set.{u2} S) (CoeTCₓ.coe.{succ u2, succ u2} (Subring.{u2} S _inst_2) (Set.{u2} S) (SetLike.Set.hasCoeT.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)))) s))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u2} S _inst_2) (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f s)) (Set.preimage.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f) (SetLike.coe.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2) s))
Case conversion may be inaccurate. Consider using '#align subring.coe_comap Subring.coe_comapₓ'. -/
@[simp]
theorem coe_comap (s : Subring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl
#align subring.coe_comap Subring.coe_comap

/- warning: subring.mem_comap -> Subring.mem_comap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {s : Subring.{u2} S _inst_2} {f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))} {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f s)) (Membership.Mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.hasMem.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f x) s)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {s : Subring.{u2} S _inst_2} {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))} {x : R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f s)) (Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f x) s)
Case conversion may be inaccurate. Consider using '#align subring.mem_comap Subring.mem_comapₓ'. -/
@[simp]
theorem mem_comap {s : Subring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl
#align subring.mem_comap Subring.mem_comap

#print Subring.comap_comap /-
theorem comap_comap (s : Subring T) (g : S →+* T) (f : R →+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl
#align subring.comap_comap Subring.comap_comap
-/

/-! ## map -/


#print Subring.map /-
/-- The image of a subring along a ring homomorphism is a subring. -/
def map {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) (s : Subring R) : Subring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubgroup.map (f : R →+ S) with
    carrier := f '' s.carrier }
#align subring.map Subring.map
-/

/- warning: subring.coe_map -> Subring.coe_map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (s : Subring.{u1} R _inst_1), Eq.{succ u2} (Set.{u2} S) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subring.{u2} S _inst_2) (Set.{u2} S) (HasLiftT.mk.{succ u2, succ u2} (Subring.{u2} S _inst_2) (Set.{u2} S) (CoeTCₓ.coe.{succ u2, succ u2} (Subring.{u2} S _inst_2) (Set.{u2} S) (SetLike.Set.hasCoeT.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)))) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s)) (Set.image.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) s))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (s : Subring.{u1} R _inst_1), Eq.{succ u2} (Set.{u2} S) (SetLike.coe.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s)) (Set.image.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s))
Case conversion may be inaccurate. Consider using '#align subring.coe_map Subring.coe_mapₓ'. -/
@[simp]
theorem coe_map (f : R →+* S) (s : Subring R) : (s.map f : Set S) = f '' s :=
  rfl
#align subring.coe_map Subring.coe_map

/- warning: subring.mem_map -> Subring.mem_map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))} {s : Subring.{u1} R _inst_1} {y : S}, Iff (Membership.Mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.hasMem.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) y (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s)) (Exists.{succ u1} R (fun (x : R) => Exists.{0} (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s) (fun (H : Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s) => Eq.{succ u2} S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f x) y)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))} {s : Subring.{u1} R _inst_1} {y : S}, Iff (Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) y (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s)) (Exists.{succ u1} R (fun (x : R) => And (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s) (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (a : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) a) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f x) y)))
Case conversion may be inaccurate. Consider using '#align subring.mem_map Subring.mem_mapₓ'. -/
@[simp]
theorem mem_map {f : R →+* S} {s : Subring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
  Set.mem_image_iff_bex
#align subring.mem_map Subring.mem_map

#print Subring.map_id /-
@[simp]
theorem map_id : s.map (RingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _
#align subring.map_id Subring.map_id
-/

#print Subring.map_map /-
theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
#align subring.map_map Subring.map_map
-/

/- warning: subring.map_le_iff_le_comap -> Subring.map_le_iff_le_comap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))} {s : Subring.{u1} R _inst_1} {t : Subring.{u2} S _inst_2}, Iff (LE.le.{u2} (Subring.{u2} S _inst_2) (Preorder.toHasLe.{u2} (Subring.{u2} S _inst_2) (PartialOrder.toPreorder.{u2} (Subring.{u2} S _inst_2) (SetLike.partialOrder.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)))) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s) t) (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) s (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f t))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))} {s : Subring.{u1} R _inst_1} {t : Subring.{u2} S _inst_2}, Iff (LE.le.{u2} (Subring.{u2} S _inst_2) (Preorder.toLE.{u2} (Subring.{u2} S _inst_2) (PartialOrder.toPreorder.{u2} (Subring.{u2} S _inst_2) (SetLike.instPartialOrder.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)))) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s) t) (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.instPartialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)))) s (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f t))
Case conversion may be inaccurate. Consider using '#align subring.map_le_iff_le_comap Subring.map_le_iff_le_comapₓ'. -/
theorem map_le_iff_le_comap {f : R →+* S} {s : Subring R} {t : Subring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
#align subring.map_le_iff_le_comap Subring.map_le_iff_le_comap

/- warning: subring.gc_map_comap -> Subring.gc_map_comap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), GaloisConnection.{u1, u2} (Subring.{u1} R _inst_1) (Subring.{u2} S _inst_2) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))) (PartialOrder.toPreorder.{u2} (Subring.{u2} S _inst_2) (SetLike.partialOrder.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2))) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), GaloisConnection.{u1, u2} (Subring.{u1} R _inst_1) (Subring.{u2} S _inst_2) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.instPartialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u2} (Subring.{u2} S _inst_2) (SetLike.instPartialOrder.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2))) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align subring.gc_map_comap Subring.gc_map_comapₓ'. -/
theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun S T =>
  map_le_iff_le_comap
#align subring.gc_map_comap Subring.gc_map_comap

/- warning: subring.equiv_map_of_injective -> Subring.equivMapOfInjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1) (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f)) -> (RingEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s)) (MulMemClass.mul.{u1, u1} R (Subring.{u1} R _inst_1) (MulOneClass.toHasMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Subring.setLike.{u1} R _inst_1) (Subring.equivMapOfInjective._proof_1.{u1} R _inst_1) s) (AddMemClass.add.{u1, u1} R (Subring.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.setLike.{u1} R _inst_1) (Subring.equivMapOfInjective._proof_2.{u1} R _inst_1) s) (MulMemClass.mul.{u2, u2} S (Subring.{u2} S _inst_2) (MulOneClass.toHasMul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))))) (Subring.setLike.{u2} S _inst_2) (Subring.equivMapOfInjective._proof_3.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s)) (AddMemClass.add.{u2, u2} S (Subring.{u2} S _inst_2) (AddZeroClass.toHasAdd.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddMonoidWithOne.toAddMonoid.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))))))) (Subring.setLike.{u2} S _inst_2) (Subring.equivMapOfInjective._proof_4.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1) (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f)) -> (RingEquiv.{u1, u2} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s))) (Submonoid.mul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s))) (Submonoid.mul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (Subsemiring.toSubmonoid.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s)))) (Distrib.toAdd.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonUnitalNonAssocSemiring.toDistrib.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Ring.toNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subring.toRing.{u1} R _inst_1 s)))))) (Distrib.toAdd.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s))) (NonUnitalNonAssocSemiring.toDistrib.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s))) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s))) (NonAssocRing.toNonUnitalNonAssocRing.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s))) (Ring.toNonAssocRing.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s))) (Subring.toRing.{u2} S _inst_2 (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s))))))))
Case conversion may be inaccurate. Consider using '#align subring.equiv_map_of_injective Subring.equivMapOfInjectiveₓ'. -/
/-- A subring is isomorphic to its image under an injective function -/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  {
    Equiv.Set.image f s
      hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }
#align subring.equiv_map_of_injective Subring.equivMapOfInjective

/- warning: subring.coe_equiv_map_of_injective_apply -> Subring.coe_equivMapOfInjective_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subring.coe_equiv_map_of_injective_apply Subring.coe_equivMapOfInjective_applyₓ'. -/
@[simp]
theorem coe_equivMapOfInjective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl
#align subring.coe_equiv_map_of_injective_apply Subring.coe_equivMapOfInjective_apply

end Subring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-! ## range -/


#print RingHom.range /-
/-- The range of a ring homomorphism, as a subring of the target. See Note [range copy pattern]. -/
def range {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) : Subring S :=
  ((⊤ : Subring R).map f).copy (Set.range f) Set.image_univ.symm
#align ring_hom.range RingHom.range
-/

/- warning: ring_hom.coe_range -> RingHom.coe_range is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Eq.{succ u2} (Set.{u2} S) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subring.{u2} S _inst_2) (Set.{u2} S) (HasLiftT.mk.{succ u2, succ u2} (Subring.{u2} S _inst_2) (Set.{u2} S) (CoeTCₓ.coe.{succ u2, succ u2} (Subring.{u2} S _inst_2) (Set.{u2} S) (SetLike.Set.hasCoeT.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)))) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Set.range.{u2, succ u1} S R (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Eq.{succ u2} (Set.{u2} S) (SetLike.coe.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Set.range.{u2, succ u1} S R (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f))
Case conversion may be inaccurate. Consider using '#align ring_hom.coe_range RingHom.coe_rangeₓ'. -/
@[simp]
theorem coe_range : (f.range : Set S) = Set.range f :=
  rfl
#align ring_hom.coe_range RingHom.coe_range

/- warning: ring_hom.mem_range -> RingHom.mem_range is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))} {y : S}, Iff (Membership.Mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.hasMem.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) y (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Exists.{succ u1} R (fun (x : R) => Eq.{succ u2} S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f x) y))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))} {y : S}, Iff (Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) y (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Exists.{succ u1} R (fun (x : R) => Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f x) y))
Case conversion may be inaccurate. Consider using '#align ring_hom.mem_range RingHom.mem_rangeₓ'. -/
@[simp]
theorem mem_range {f : R →+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl
#align ring_hom.mem_range RingHom.mem_range

/- warning: ring_hom.range_eq_map -> RingHom.range_eq_map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Eq.{succ u2} (Subring.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Eq.{succ u2} (Subring.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align ring_hom.range_eq_map RingHom.range_eq_mapₓ'. -/
theorem range_eq_map (f : R →+* S) : f.range = Subring.map f ⊤ := by ext; simp
#align ring_hom.range_eq_map RingHom.range_eq_map

/- warning: ring_hom.mem_range_self -> RingHom.mem_range_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (x : R), Membership.Mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.hasMem.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f x) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (x : R), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f x) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align ring_hom.mem_range_self RingHom.mem_range_selfₓ'. -/
theorem mem_range_self (f : R →+* S) (x : R) : f x ∈ f.range :=
  mem_range.mpr ⟨x, rfl⟩
#align ring_hom.mem_range_self RingHom.mem_range_self

#print RingHom.map_range /-
theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : Subring R).map_map g f
#align ring_hom.map_range RingHom.map_range
-/

/- warning: ring_hom.fintype_range -> RingHom.fintypeRange is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] [_inst_4 : Fintype.{u1} R] [_inst_5 : DecidableEq.{succ u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] [_inst_4 : Fintype.{u1} R] [_inst_5 : DecidableEq.{succ u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Fintype.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))
Case conversion may be inaccurate. Consider using '#align ring_hom.fintype_range RingHom.fintypeRangeₓ'. -/
/-- The range of a ring homomorphism is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype S`. -/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (range f) :=
  Set.fintypeRange f
#align ring_hom.fintype_range RingHom.fintypeRange

end RingHom

namespace Subring

/-! ## bot -/


instance : Bot (Subring R) :=
  ⟨(Int.castRingHom R).range⟩

instance : Inhabited (Subring R) :=
  ⟨⊥⟩

/- warning: subring.coe_bot -> Subring.coe_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.hasBot.{u1} R _inst_1))) (Set.range.{u1, 1} R Int ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.instBotSubring.{u1} R _inst_1))) (Set.range.{u1, 1} R Int (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align subring.coe_bot Subring.coe_botₓ'. -/
theorem coe_bot : ((⊥ : Subring R) : Set R) = Set.range (coe : ℤ → R) :=
  RingHom.coe_range (Int.castRingHom R)
#align subring.coe_bot Subring.coe_bot

/- warning: subring.mem_bot -> Subring.mem_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.hasBot.{u1} R _inst_1))) (Exists.{1} Int (fun (n : Int) => Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) n) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {x : R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.instBotSubring.{u1} R _inst_1))) (Exists.{1} Int (fun (n : Int) => Eq.{succ u1} R (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1) n) x))
Case conversion may be inaccurate. Consider using '#align subring.mem_bot Subring.mem_botₓ'. -/
theorem mem_bot {x : R} : x ∈ (⊥ : Subring R) ↔ ∃ n : ℤ, ↑n = x :=
  RingHom.mem_range
#align subring.mem_bot Subring.mem_bot

/-! ## inf -/


/-- The inf of two subrings is their intersection. -/
instance : Inf (Subring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubgroup ⊓ t.toAddSubgroup with carrier := s ∩ t }⟩

/- warning: subring.coe_inf -> Subring.coe_inf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (p : Subring.{u1} R _inst_1) (p' : Subring.{u1} R _inst_1), Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Inf.inf.{u1} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) p p')) (Inter.inter.{u1} (Set.{u1} R) (Set.hasInter.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) p) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) p'))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (p : Subring.{u1} R _inst_1) (p' : Subring.{u1} R _inst_1), Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Inf.inf.{u1} (Subring.{u1} R _inst_1) (Subring.instInfSubring.{u1} R _inst_1) p p')) (Inter.inter.{u1} (Set.{u1} R) (Set.instInterSet.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) p) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) p'))
Case conversion may be inaccurate. Consider using '#align subring.coe_inf Subring.coe_infₓ'. -/
@[simp]
theorem coe_inf (p p' : Subring R) : ((p ⊓ p' : Subring R) : Set R) = p ∩ p' :=
  rfl
#align subring.coe_inf Subring.coe_inf

/- warning: subring.mem_inf -> Subring.mem_inf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {p : Subring.{u1} R _inst_1} {p' : Subring.{u1} R _inst_1} {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Inf.inf.{u1} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) p p')) (And (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x p) (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x p'))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {p : Subring.{u1} R _inst_1} {p' : Subring.{u1} R _inst_1} {x : R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Inf.inf.{u1} (Subring.{u1} R _inst_1) (Subring.instInfSubring.{u1} R _inst_1) p p')) (And (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x p) (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x p'))
Case conversion may be inaccurate. Consider using '#align subring.mem_inf Subring.mem_infₓ'. -/
@[simp]
theorem mem_inf {p p' : Subring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align subring.mem_inf Subring.mem_inf

instance : InfSet (Subring R) :=
  ⟨fun s =>
    Subring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, [anonymous] t) (⨅ t ∈ s, Subring.toAddSubgroup t) (by simp)
      (by simp)⟩

/- warning: subring.coe_Inf -> Subring.coe_sInf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (S : Set.{u1} (Subring.{u1} R _inst_1)), Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (InfSet.sInf.{u1} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) S)) (Set.iInter.{u1, succ u1} R (Subring.{u1} R _inst_1) (fun (s : Subring.{u1} R _inst_1) => Set.iInter.{u1, 0} R (Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) s S) (fun (H : Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) s S) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) s)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (S : Set.{u1} (Subring.{u1} R _inst_1)), Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (InfSet.sInf.{u1} (Subring.{u1} R _inst_1) (Subring.instInfSetSubring.{u1} R _inst_1) S)) (Set.iInter.{u1, succ u1} R (Subring.{u1} R _inst_1) (fun (s : Subring.{u1} R _inst_1) => Set.iInter.{u1, 0} R (Membership.mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.instMembershipSet.{u1} (Subring.{u1} R _inst_1)) s S) (fun (H : Membership.mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.instMembershipSet.{u1} (Subring.{u1} R _inst_1)) s S) => SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align subring.coe_Inf Subring.coe_sInfₓ'. -/
@[simp, norm_cast]
theorem coe_sInf (S : Set (Subring R)) : ((sInf S : Subring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl
#align subring.coe_Inf Subring.coe_sInf

/- warning: subring.mem_Inf -> Subring.mem_sInf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Set.{u1} (Subring.{u1} R _inst_1)} {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (InfSet.sInf.{u1} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) S)) (forall (p : Subring.{u1} R _inst_1), (Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) p S) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Set.{u1} (Subring.{u1} R _inst_1)} {x : R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (InfSet.sInf.{u1} (Subring.{u1} R _inst_1) (Subring.instInfSetSubring.{u1} R _inst_1) S)) (forall (p : Subring.{u1} R _inst_1), (Membership.mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.instMembershipSet.{u1} (Subring.{u1} R _inst_1)) p S) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x p))
Case conversion may be inaccurate. Consider using '#align subring.mem_Inf Subring.mem_sInfₓ'. -/
theorem mem_sInf {S : Set (Subring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
#align subring.mem_Inf Subring.mem_sInf

/- warning: subring.coe_infi -> Subring.coe_iInf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {ι : Sort.{u2}} {S : ι -> (Subring.{u1} R _inst_1)}, Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (iInf.{u1, u2} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) ι (fun (i : ι) => S i))) (Set.iInter.{u1, u2} R ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (S i)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Sort.{u1}} {S : ι -> (Subring.{u2} R _inst_1)}, Eq.{succ u2} (Set.{u2} R) (SetLike.coe.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1) (iInf.{u2, u1} (Subring.{u2} R _inst_1) (Subring.instInfSetSubring.{u2} R _inst_1) ι (fun (i : ι) => S i))) (Set.iInter.{u2, u1} R ι (fun (i : ι) => SetLike.coe.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1) (S i)))
Case conversion may be inaccurate. Consider using '#align subring.coe_infi Subring.coe_iInfₓ'. -/
@[simp, norm_cast]
theorem coe_iInf {ι : Sort _} {S : ι → Subring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_Inf, Set.biInter_range]
#align subring.coe_infi Subring.coe_iInf

/- warning: subring.mem_infi -> Subring.mem_iInf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {ι : Sort.{u2}} {S : ι -> (Subring.{u1} R _inst_1)} {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (iInf.{u1, u2} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) ι (fun (i : ι) => S i))) (forall (i : ι), Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (S i))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Sort.{u1}} {S : ι -> (Subring.{u2} R _inst_1)} {x : R}, Iff (Membership.mem.{u2, u2} R (Subring.{u2} R _inst_1) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1)) x (iInf.{u2, u1} (Subring.{u2} R _inst_1) (Subring.instInfSetSubring.{u2} R _inst_1) ι (fun (i : ι) => S i))) (forall (i : ι), Membership.mem.{u2, u2} R (Subring.{u2} R _inst_1) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1)) x (S i))
Case conversion may be inaccurate. Consider using '#align subring.mem_infi Subring.mem_iInfₓ'. -/
theorem mem_iInf {ι : Sort _} {S : ι → Subring R} {x : R} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_Inf, Set.forall_range_iff]
#align subring.mem_infi Subring.mem_iInf

#print Subring.sInf_toSubmonoid /-
@[simp]
theorem sInf_toSubmonoid (s : Set (Subring R)) : (sInf s).toSubmonoid = ⨅ t ∈ s, [anonymous] t :=
  mk'_toSubmonoid _ _
#align subring.Inf_to_submonoid Subring.sInf_toSubmonoid
-/

/- warning: subring.Inf_to_add_subgroup -> Subring.sInf_toAddSubgroup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Set.{u1} (Subring.{u1} R _inst_1)), Eq.{succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Subring.toAddSubgroup.{u1} R _inst_1 (InfSet.sInf.{u1} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) s)) (iInf.{u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (AddSubgroup.hasInf.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Subring.{u1} R _inst_1) (fun (t : Subring.{u1} R _inst_1) => iInf.{u1, 0} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (AddSubgroup.hasInf.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) t s) (fun (H : Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) t s) => Subring.toAddSubgroup.{u1} R _inst_1 t)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Set.{u1} (Subring.{u1} R _inst_1)), Eq.{succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (Subring.toAddSubgroup.{u1} R _inst_1 (InfSet.sInf.{u1} (Subring.{u1} R _inst_1) (Subring.instInfSetSubring.{u1} R _inst_1) s)) (iInf.{u1, succ u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (AddSubgroup.instInfSetAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (Subring.{u1} R _inst_1) (fun (t : Subring.{u1} R _inst_1) => iInf.{u1, 0} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (AddSubgroup.instInfSetAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (Membership.mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.instMembershipSet.{u1} (Subring.{u1} R _inst_1)) t s) (fun (H : Membership.mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.instMembershipSet.{u1} (Subring.{u1} R _inst_1)) t s) => Subring.toAddSubgroup.{u1} R _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align subring.Inf_to_add_subgroup Subring.sInf_toAddSubgroupₓ'. -/
@[simp]
theorem sInf_toAddSubgroup (s : Set (Subring R)) :
    (sInf s).toAddSubgroup = ⨅ t ∈ s, Subring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _
#align subring.Inf_to_add_subgroup Subring.sInf_toAddSubgroup

/-- Subrings of a ring form a complete lattice. -/
instance : CompleteLattice (Subring R) :=
  {
    completeLatticeOfInf (Subring R) fun s =>
      IsGLB.of_image (fun s t => show (s : Set R) ≤ t ↔ s ≤ t from SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ coe_int_mem s n
    top := ⊤
    le_top := fun s x hx => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun s t x => And.left
    inf_le_right := fun s t x => And.right
    le_inf := fun s t₁ t₂ h₁ h₂ x hx => ⟨h₁ hx, h₂ hx⟩ }

/- warning: subring.eq_top_iff' -> Subring.eq_top_iff' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (A : Subring.{u1} R _inst_1), Iff (Eq.{succ u1} (Subring.{u1} R _inst_1) A (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))) (forall (x : R), Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x A)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (A : Subring.{u1} R _inst_1), Iff (Eq.{succ u1} (Subring.{u1} R _inst_1) A (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1))) (forall (x : R), Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x A)
Case conversion may be inaccurate. Consider using '#align subring.eq_top_iff' Subring.eq_top_iff'ₓ'. -/
theorem eq_top_iff' (A : Subring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
#align subring.eq_top_iff' Subring.eq_top_iff'

/-! ## Center of a ring -/


section

variable (R)

#print Subring.center /-
/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
def center : Subring R :=
  { Subsemiring.center R with
    carrier := Set.center R
    neg_mem' := fun a => Set.neg_mem_center }
#align subring.center Subring.center
-/

/- warning: subring.coe_center -> Subring.coe_center is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.center.{u1} R _inst_1)) (Set.center.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Subring.center.{u1} R _inst_1)) (Set.center.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align subring.coe_center Subring.coe_centerₓ'. -/
theorem coe_center : ↑(center R) = Set.center R :=
  rfl
#align subring.coe_center Subring.coe_center

#print Subring.center_toSubsemiring /-
@[simp]
theorem center_toSubsemiring : (center R).toSubsemiring = Subsemiring.center R :=
  rfl
#align subring.center_to_subsemiring Subring.center_toSubsemiring
-/

variable {R}

/- warning: subring.mem_center_iff -> Subring.mem_center_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {z : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) z (Subring.center.{u1} R _inst_1)) (forall (g : R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) g z) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) z g))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {z : R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) z (Subring.center.{u1} R _inst_1)) (forall (g : R), Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) g z) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) z g))
Case conversion may be inaccurate. Consider using '#align subring.mem_center_iff Subring.mem_center_iffₓ'. -/
theorem mem_center_iff {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align subring.mem_center_iff Subring.mem_center_iff

/- warning: subring.decidable_mem_center -> Subring.decidableMemCenter is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_4 : DecidableEq.{succ u1} R] [_inst_5 : Fintype.{u1} R], DecidablePred.{succ u1} R (fun (_x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) _x (Subring.center.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_4 : DecidableEq.{succ u1} R] [_inst_5 : Fintype.{u1} R], DecidablePred.{succ u1} R (fun (_x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) _x (Subring.center.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align subring.decidable_mem_center Subring.decidableMemCenterₓ'. -/
instance decidableMemCenter [DecidableEq R] [Fintype R] : DecidablePred (· ∈ center R) := fun _ =>
  decidable_of_iff' _ mem_center_iff
#align subring.decidable_mem_center Subring.decidableMemCenter

/- warning: subring.center_eq_top -> Subring.center_eq_top is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_4 : CommRing.{u1} R], Eq.{succ u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (Subring.center.{u1} R (CommRing.toRing.{u1} R _inst_4)) (Top.top.{u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (Subring.hasTop.{u1} R (CommRing.toRing.{u1} R _inst_4)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_4 : CommRing.{u1} R], Eq.{succ u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (Subring.center.{u1} R (CommRing.toRing.{u1} R _inst_4)) (Top.top.{u1} (Subring.{u1} R (CommRing.toRing.{u1} R _inst_4)) (Subring.instTopSubring.{u1} R (CommRing.toRing.{u1} R _inst_4)))
Case conversion may be inaccurate. Consider using '#align subring.center_eq_top Subring.center_eq_topₓ'. -/
@[simp]
theorem center_eq_top (R) [CommRing R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)
#align subring.center_eq_top Subring.center_eq_top

/-- The center is commutative. -/
instance : CommRing (center R) :=
  { Subsemiring.center.commSemiring, (center R).toRing with }

end

section DivisionRing

variable {K : Type u} [DivisionRing K]

instance : Field (center K) :=
  { (center K).Nontrivial,
    center.commRing with
    inv := fun a => ⟨a⁻¹, Set.inv_mem_center₀ a.Prop⟩
    mul_inv_cancel := fun ⟨a, ha⟩ h => Subtype.ext <| mul_inv_cancel <| Subtype.coe_injective.Ne h
    div := fun a b => ⟨a / b, Set.div_mem_center₀ a.Prop b.Prop⟩
    div_eq_mul_inv := fun a b => Subtype.ext <| div_eq_mul_inv _ _
    inv_zero := Subtype.ext inv_zero }

/- warning: subring.center.coe_inv -> Subring.center.coe_inv is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_4 : DivisionRing.{u1} K] (a : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))), Eq.{succ u1} K ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) K (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) K (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) K (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) K (coeSubtype.{succ u1} K (fun (x : K) => Membership.Mem.{u1, u1} K (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) (SetLike.hasMem.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) x (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))))))) (Inv.inv.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (DivInvMonoid.toHasInv.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (DivisionRing.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Field.toDivisionRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.field.{u1} K _inst_4)))) a)) (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K _inst_4)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) K (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) K (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) K (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) K (coeSubtype.{succ u1} K (fun (x : K) => Membership.Mem.{u1, u1} K (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) (SetLike.hasMem.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.setLike.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) x (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4))))))) a))
but is expected to have type
  forall {K : Type.{u1}} [_inst_4 : DivisionRing.{u1} K] (a : Subtype.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) (SetLike.instMembership.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.instSetLikeSubring.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) x (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4)))), Eq.{succ u1} K (Subtype.val.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Set.{u1} K) (Set.instMembershipSet.{u1} K) x (SetLike.coe.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.instSetLikeSubring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4)))) (Inv.inv.{u1} (Subtype.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) (SetLike.instMembership.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.instSetLikeSubring.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) x (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4)))) (Field.toInv.{u1} (Subtype.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) (SetLike.instMembership.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.instSetLikeSubring.{u1} K (DivisionRing.toRing.{u1} K _inst_4))) x (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4)))) (Subring.instFieldSubtypeMemSubringToRingInstMembershipInstSetLikeSubringCenter.{u1} K _inst_4)) a)) (Inv.inv.{u1} K (DivisionRing.toInv.{u1} K _inst_4) (Subtype.val.{succ u1} K (fun (x : K) => Membership.mem.{u1, u1} K (Set.{u1} K) (Set.instMembershipSet.{u1} K) x (SetLike.coe.{u1, u1} (Subring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) K (Subring.instSetLikeSubring.{u1} K (DivisionRing.toRing.{u1} K _inst_4)) (Subring.center.{u1} K (DivisionRing.toRing.{u1} K _inst_4)))) a))
Case conversion may be inaccurate. Consider using '#align subring.center.coe_inv Subring.center.coe_invₓ'. -/
@[simp]
theorem center.coe_inv (a : center K) : ((a⁻¹ : center K) : K) = (a : K)⁻¹ :=
  rfl
#align subring.center.coe_inv Subring.center.coe_inv

/- warning: subring.center.coe_div -> Subring.center.coe_div is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subring.center.coe_div Subring.center.coe_divₓ'. -/
@[simp]
theorem center.coe_div (a b : center K) : ((a / b : center K) : K) = (a : K) / (b : K) :=
  rfl
#align subring.center.coe_div Subring.center.coe_div

end DivisionRing

/-! ## subring closure of a subset -/


#print Subring.closure /-
/-- The `subring` generated by a set. -/
def closure (s : Set R) : Subring R :=
  sInf { S | s ⊆ S }
#align subring.closure Subring.closure
-/

/- warning: subring.mem_closure -> Subring.mem_closure is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {x : R} {s : Set.{u1} R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) (forall (S : Subring.{u1} R _inst_1), (HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) S)) -> (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x S))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {x : R} {s : Set.{u1} R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) (forall (S : Subring.{u1} R _inst_1), (HasSubset.Subset.{u1} (Set.{u1} R) (Set.instHasSubsetSet.{u1} R) s (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) S)) -> (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x S))
Case conversion may be inaccurate. Consider using '#align subring.mem_closure Subring.mem_closureₓ'. -/
theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subring R, s ⊆ S → x ∈ S :=
  mem_sInf
#align subring.mem_closure Subring.mem_closure

/- warning: subring.subset_closure -> Subring.subset_closure is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R}, HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.closure.{u1} R _inst_1 s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R}, HasSubset.Subset.{u1} (Set.{u1} R) (Set.instHasSubsetSet.{u1} R) s (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 s))
Case conversion may be inaccurate. Consider using '#align subring.subset_closure Subring.subset_closureₓ'. -/
/-- The subring generated by a set includes the set. -/
@[simp]
theorem subset_closure {s : Set R} : s ⊆ closure s := fun x hx => mem_closure.2 fun S hS => hS hx
#align subring.subset_closure Subring.subset_closure

/- warning: subring.not_mem_of_not_mem_closure -> Subring.not_mem_of_not_mem_closure is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {P : R}, (Not (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) P (Subring.closure.{u1} R _inst_1 s))) -> (Not (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) P s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {P : R}, (Not (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) P (Subring.closure.{u1} R _inst_1 s))) -> (Not (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) P s))
Case conversion may be inaccurate. Consider using '#align subring.not_mem_of_not_mem_closure Subring.not_mem_of_not_mem_closureₓ'. -/
theorem not_mem_of_not_mem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align subring.not_mem_of_not_mem_closure Subring.not_mem_of_not_mem_closure

/- warning: subring.closure_le -> Subring.closure_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {t : Subring.{u1} R _inst_1}, Iff (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.closure.{u1} R _inst_1 s) t) (HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) t))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {t : Subring.{u1} R _inst_1}, Iff (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) (Subring.closure.{u1} R _inst_1 s) t) (HasSubset.Subset.{u1} (Set.{u1} R) (Set.instHasSubsetSet.{u1} R) s (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) t))
Case conversion may be inaccurate. Consider using '#align subring.closure_le Subring.closure_leₓ'. -/
/-- A subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
theorem closure_le {s : Set R} {t : Subring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩
#align subring.closure_le Subring.closure_le

/- warning: subring.closure_mono -> Subring.closure_mono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {{s : Set.{u1} R}} {{t : Set.{u1} R}}, (HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) s t) -> (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.closure.{u1} R _inst_1 s) (Subring.closure.{u1} R _inst_1 t))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {{s : Set.{u1} R}} {{t : Set.{u1} R}}, (HasSubset.Subset.{u1} (Set.{u1} R) (Set.instHasSubsetSet.{u1} R) s t) -> (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) (Subring.closure.{u1} R _inst_1 s) (Subring.closure.{u1} R _inst_1 t))
Case conversion may be inaccurate. Consider using '#align subring.closure_mono Subring.closure_monoₓ'. -/
/-- Subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
#align subring.closure_mono Subring.closure_mono

/- warning: subring.closure_eq_of_le -> Subring.closure_eq_of_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {t : Subring.{u1} R _inst_1}, (HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) t)) -> (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) t (Subring.closure.{u1} R _inst_1 s)) -> (Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 s) t)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {t : Subring.{u1} R _inst_1}, (HasSubset.Subset.{u1} (Set.{u1} R) (Set.instHasSubsetSet.{u1} R) s (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) t)) -> (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) t (Subring.closure.{u1} R _inst_1 s)) -> (Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 s) t)
Case conversion may be inaccurate. Consider using '#align subring.closure_eq_of_le Subring.closure_eq_of_leₓ'. -/
theorem closure_eq_of_le {s : Set R} {t : Subring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂
#align subring.closure_eq_of_le Subring.closure_eq_of_le

/- warning: subring.closure_induction -> Subring.closure_induction is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {p : R -> Prop} {x : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) -> (forall (x : R), (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x s) -> (p x)) -> (p (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))) -> (p (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))) -> (forall (x : R) (y : R), (p x) -> (p y) -> (p (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1))) x y))) -> (forall (x : R), (p x) -> (p (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) x))) -> (forall (x : R) (y : R), (p x) -> (p y) -> (p (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) x y))) -> (p x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {p : R -> Prop} {x : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) -> (forall (x : R), (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x s) -> (p x)) -> (p (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) -> (p (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) -> (forall (x : R) (y : R), (p x) -> (p y) -> (p (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x y))) -> (forall (x : R), (p x) -> (p (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) x))) -> (forall (x : R) (y : R), (p x) -> (p y) -> (p (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) x y))) -> (p x)
Case conversion may be inaccurate. Consider using '#align subring.closure_induction Subring.closure_inductionₓ'. -/
/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
theorem closure_induction {s : Set R} {p : R → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (H0 : p 0) (H1 : p 1) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x : R, p x → p (-x))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, Hmul, H1, Hadd, H0, Hneg⟩).2 Hs h
#align subring.closure_induction Subring.closure_induction

/- warning: subring.closure_induction₂ -> Subring.closure_induction₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subring.closure_induction₂ Subring.closure_induction₂ₓ'. -/
/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_elim]
theorem closure_induction₂ {s : Set R} {p : R → R → Prop} {a b : R} (ha : a ∈ closure s)
    (hb : b ∈ closure s) (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H0_left : ∀ x, p 0 x)
    (H0_right : ∀ x, p x 0) (H1_left : ∀ x, p 1 x) (H1_right : ∀ x, p x 1)
    (Hneg_left : ∀ x y, p x y → p (-x) y) (Hneg_right : ∀ x y, p x y → p x (-y))
    (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p a b :=
  by
  refine'
    closure_induction hb _ (H0_right _) (H1_right _) (Hadd_right a) (Hneg_right a) (Hmul_right a)
  refine' closure_induction ha Hs (fun x _ => H0_left x) (fun x _ => H1_left x) _ _ _
  · exact fun x y H₁ H₂ z zs => Hadd_left x y z (H₁ z zs) (H₂ z zs)
  · exact fun x hx z zs => Hneg_left x z (hx z zs)
  · exact fun x y H₁ H₂ z zs => Hmul_left x y z (H₁ z zs) (H₂ z zs)
#align subring.closure_induction₂ Subring.closure_induction₂

/- warning: subring.mem_closure_iff -> Subring.mem_closure_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) x (AddSubgroup.closure.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) (Submonoid.closure.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) s))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {x : R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)))) x (AddSubgroup.closure.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) (SetLike.coe.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (Submonoid.closure.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) s))))
Case conversion may be inaccurate. Consider using '#align subring.mem_closure_iff Subring.mem_closure_iffₓ'. -/
theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubgroup.closure (Submonoid.closure s : Set R) :=
  ⟨fun h =>
    closure_induction h (fun x hx => AddSubgroup.subset_closure <| Submonoid.subset_closure hx)
      (AddSubgroup.zero_mem _)
      (AddSubgroup.subset_closure (Submonoid.one_mem (Submonoid.closure s)))
      (fun x y hx hy => AddSubgroup.add_mem _ hx hy) (fun x hx => AddSubgroup.neg_mem _ hx)
      fun x y hx hy =>
      AddSubgroup.closure_induction hy
        (fun q hq =>
          AddSubgroup.closure_induction hx
            (fun p hp => AddSubgroup.subset_closure ((Submonoid.closure s).mul_mem hp hq))
            (by rw [MulZeroClass.zero_mul q]; apply AddSubgroup.zero_mem _)
            (fun p₁ p₂ ihp₁ ihp₂ => by rw [add_mul p₁ p₂ q]; apply AddSubgroup.add_mem _ ihp₁ ihp₂)
            fun x hx => by
            have f : -x * q = -(x * q) := by simp
            rw [f]; apply AddSubgroup.neg_mem _ hx)
        (by rw [MulZeroClass.mul_zero x]; apply AddSubgroup.zero_mem _)
        (fun q₁ q₂ ihq₁ ihq₂ => by rw [mul_add x q₁ q₂]; apply AddSubgroup.add_mem _ ihq₁ ihq₂)
        fun z hz => by
        have f : x * -z = -(x * z) := by simp
        rw [f]; apply AddSubgroup.neg_mem _ hz,
    fun h =>
    AddSubgroup.closure_induction h
      (fun x hx =>
        Submonoid.closure_induction hx (fun x hx => subset_closure hx) (one_mem _) fun x y hx hy =>
          mul_mem hx hy)
      (zero_mem _) (fun x y hx hy => add_mem hx hy) fun x hx => neg_mem hx⟩
#align subring.mem_closure_iff Subring.mem_closure_iff

/- warning: subring.closure_comm_ring_of_comm -> Subring.closureCommRingOfComm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R}, (forall (a : R), (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) a s) -> (forall (b : R), (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) b s) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) b a)))) -> (CommRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (Subring.closure.{u1} R _inst_1 s)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R}, (forall (a : R), (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) a s) -> (forall (b : R), (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) b s) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) b a)))) -> (CommRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s))))
Case conversion may be inaccurate. Consider using '#align subring.closure_comm_ring_of_comm Subring.closureCommRingOfCommₓ'. -/
/-- If all elements of `s : set A` commute pairwise, then `closure s` is a commutative ring.  -/
def closureCommRingOfComm {s : Set R} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommRing (closure s) :=
  { (closure s).toRing with
    mul_comm := fun x y => by
      ext
      simp only [Subring.coe_mul]
      refine'
        closure_induction₂ x.prop y.prop hcomm
          (fun x => by simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul])
          (fun x => by simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul])
          (fun x => by simp only [mul_one, one_mul]) (fun x => by simp only [mul_one, one_mul])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x y hxy => by simp only [mul_neg, neg_mul, hxy])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, ← h₁, mul_assoc x₁ y x₂, ← h₂, mul_assoc])
          fun x₁ x₂ y h₁ h₂ => by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc] }
#align subring.closure_comm_ring_of_comm Subring.closureCommRingOfComm

/- warning: subring.exists_list_of_mem_closure -> Subring.exists_list_of_mem_closure is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {x : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) -> (Exists.{succ u1} (List.{u1} (List.{u1} R)) (fun (L : List.{u1} (List.{u1} R)) => And (forall (t : List.{u1} R), (Membership.Mem.{u1, u1} (List.{u1} R) (List.{u1} (List.{u1} R)) (List.hasMem.{u1} (List.{u1} R)) t L) -> (forall (y : R), (Membership.Mem.{u1, u1} R (List.{u1} R) (List.hasMem.{u1} R) y t) -> (Or (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) y s) (Eq.{succ u1} R y (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))))))) (Eq.{succ u1} R (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (List.map.{u1, u1} (List.{u1} R) R (List.prod.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) L)) x)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {x : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) -> (Exists.{succ u1} (List.{u1} (List.{u1} R)) (fun (L : List.{u1} (List.{u1} R)) => And (forall (t : List.{u1} R), (Membership.mem.{u1, u1} (List.{u1} R) (List.{u1} (List.{u1} R)) (List.instMembershipList.{u1} (List.{u1} R)) t L) -> (forall (y : R), (Membership.mem.{u1, u1} R (List.{u1} R) (List.instMembershipList.{u1} R) y t) -> (Or (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) y s) (Eq.{succ u1} R y (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))))))) (Eq.{succ u1} R (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (List.map.{u1, u1} (List.{u1} R) R (List.prod.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))) L)) x)))
Case conversion may be inaccurate. Consider using '#align subring.exists_list_of_mem_closure Subring.exists_list_of_mem_closureₓ'. -/
theorem exists_list_of_mem_closure {s : Set R} {x : R} (h : x ∈ closure s) :
    ∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s ∨ y = (-1 : R)) ∧ (L.map List.prod).Sum = x :=
  AddSubgroup.closure_induction (mem_closure_iff.1 h)
    (fun x hx =>
      let ⟨l, hl, h⟩ := Submonoid.exists_list_of_mem_closure hx
      ⟨[l], by simp [h] <;> clear_aux_decl <;> tauto⟩)
    ⟨[], by simp⟩
    (fun x y ⟨l, hl1, hl2⟩ ⟨m, hm1, hm2⟩ =>
      ⟨l ++ m, fun t ht => (List.mem_append.1 ht).elim (hl1 t) (hm1 t), by simp [hl2, hm2]⟩)
    fun x ⟨L, hL⟩ =>
    ⟨L.map (List.cons (-1)),
      List.forall_mem_map_iff.2 fun j hj => List.forall_mem_cons.2 ⟨Or.inr rfl, hL.1 j hj⟩,
      hL.2 ▸
        List.recOn L (by simp)
          (by simp (config := { contextual := true }) [List.map_cons, add_comm])⟩
#align subring.exists_list_of_mem_closure Subring.exists_list_of_mem_closure

variable (R)

/- warning: subring.gi -> Subring.gi is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R], GaloisInsertion.{u1, u1} (Set.{u1} R) (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} R) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} R) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} R) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} R) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} R) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} R) (Set.completeBooleanAlgebra.{u1} R))))))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))) (Subring.closure.{u1} R _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Ring.{u1} R], GaloisInsertion.{u1, u1} (Set.{u1} R) (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} R) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} R) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} R) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} R) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} R) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} R) (Set.instCompleteBooleanAlgebraSet.{u1} R))))))) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1)))) (Subring.closure.{u1} R _inst_1) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align subring.gi Subring.giₓ'. -/
/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure R _) coe
    where
  choice s _ := closure s
  gc s t := closure_le
  le_l_u s := subset_closure
  choice_eq s h := rfl
#align subring.gi Subring.gi

variable {R}

#print Subring.closure_eq /-
/-- Closure of a subring `S` equals `S`. -/
theorem closure_eq (s : Subring R) : closure (s : Set R) = s :=
  (Subring.gi R).l_u_eq s
#align subring.closure_eq Subring.closure_eq
-/

/- warning: subring.closure_empty -> Subring.closure_empty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} R) (Set.hasEmptyc.{u1} R))) (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.hasBot.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} R) (Set.instEmptyCollectionSet.{u1} R))) (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.instBotSubring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align subring.closure_empty Subring.closure_emptyₓ'. -/
@[simp]
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subring.gi R).gc.l_bot
#align subring.closure_empty Subring.closure_empty

/- warning: subring.closure_univ -> Subring.closure_univ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 (Set.univ.{u1} R)) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 (Set.univ.{u1} R)) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align subring.closure_univ Subring.closure_univₓ'. -/
@[simp]
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤
#align subring.closure_univ Subring.closure_univ

#print Subring.closure_union /-
theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subring.gi R).gc.l_sup
#align subring.closure_union Subring.closure_union
-/

/- warning: subring.closure_Union -> Subring.closure_iUnion is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {ι : Sort.{u2}} (s : ι -> (Set.{u1} R)), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 (Set.iUnion.{u1, u2} R ι (fun (i : ι) => s i))) (iSup.{u1, u2} (Subring.{u1} R _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1))) ι (fun (i : ι) => Subring.closure.{u1} R _inst_1 (s i)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Sort.{u1}} (s : ι -> (Set.{u2} R)), Eq.{succ u2} (Subring.{u2} R _inst_1) (Subring.closure.{u2} R _inst_1 (Set.iUnion.{u2, u1} R ι (fun (i : ι) => s i))) (iSup.{u2, u1} (Subring.{u2} R _inst_1) (CompleteLattice.toSupSet.{u2} (Subring.{u2} R _inst_1) (Subring.instCompleteLatticeSubring.{u2} R _inst_1)) ι (fun (i : ι) => Subring.closure.{u2} R _inst_1 (s i)))
Case conversion may be inaccurate. Consider using '#align subring.closure_Union Subring.closure_iUnionₓ'. -/
theorem closure_iUnion {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subring.gi R).gc.l_iSup
#align subring.closure_Union Subring.closure_iUnion

/- warning: subring.closure_sUnion -> Subring.closure_sUnion is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Set.{u1} (Set.{u1} R)), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 (Set.sUnion.{u1} R s)) (iSup.{u1, succ u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1))) (Set.{u1} R) (fun (t : Set.{u1} R) => iSup.{u1, 0} (Subring.{u1} R _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1))) (Membership.Mem.{u1, u1} (Set.{u1} R) (Set.{u1} (Set.{u1} R)) (Set.hasMem.{u1} (Set.{u1} R)) t s) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} R) (Set.{u1} (Set.{u1} R)) (Set.hasMem.{u1} (Set.{u1} R)) t s) => Subring.closure.{u1} R _inst_1 t)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Set.{u1} (Set.{u1} R)), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 (Set.sUnion.{u1} R s)) (iSup.{u1, succ u1} (Subring.{u1} R _inst_1) (CompleteLattice.toSupSet.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1)) (Set.{u1} R) (fun (t : Set.{u1} R) => iSup.{u1, 0} (Subring.{u1} R _inst_1) (CompleteLattice.toSupSet.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1)) (Membership.mem.{u1, u1} (Set.{u1} R) (Set.{u1} (Set.{u1} R)) (Set.instMembershipSet.{u1} (Set.{u1} R)) t s) (fun (H : Membership.mem.{u1, u1} (Set.{u1} R) (Set.{u1} (Set.{u1} R)) (Set.instMembershipSet.{u1} (Set.{u1} R)) t s) => Subring.closure.{u1} R _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align subring.closure_sUnion Subring.closure_sUnionₓ'. -/
theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subring.gi R).gc.l_sSup
#align subring.closure_sUnion Subring.closure_sUnion

/- warning: subring.map_sup -> Subring.map_sup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1) (t : Subring.{u1} R _inst_1) (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Eq.{succ u2} (Subring.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f (Sup.sup.{u1} (Subring.{u1} R _inst_1) (SemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (Lattice.toSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toLattice.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1)))) s t)) (Sup.sup.{u2} (Subring.{u2} S _inst_2) (SemilatticeSup.toHasSup.{u2} (Subring.{u2} S _inst_2) (Lattice.toSemilatticeSup.{u2} (Subring.{u2} S _inst_2) (CompleteLattice.toLattice.{u2} (Subring.{u2} S _inst_2) (Subring.completeLattice.{u2} S _inst_2)))) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f t))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1) (t : Subring.{u1} R _inst_1) (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Eq.{succ u2} (Subring.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f (Sup.sup.{u1} (Subring.{u1} R _inst_1) (SemilatticeSup.toSup.{u1} (Subring.{u1} R _inst_1) (Lattice.toSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toLattice.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1)))) s t)) (Sup.sup.{u2} (Subring.{u2} S _inst_2) (SemilatticeSup.toSup.{u2} (Subring.{u2} S _inst_2) (Lattice.toSemilatticeSup.{u2} (Subring.{u2} S _inst_2) (CompleteLattice.toLattice.{u2} (Subring.{u2} S _inst_2) (Subring.instCompleteLatticeSubring.{u2} S _inst_2)))) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f s) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f t))
Case conversion may be inaccurate. Consider using '#align subring.map_sup Subring.map_supₓ'. -/
theorem map_sup (s t : Subring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
#align subring.map_sup Subring.map_sup

/- warning: subring.map_supr -> Subring.map_iSup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {ι : Sort.{u3}} (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (s : ι -> (Subring.{u1} R _inst_1)), Eq.{succ u2} (Subring.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f (iSup.{u1, u3} (Subring.{u1} R _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1))) ι s)) (iSup.{u2, u3} (Subring.{u2} S _inst_2) (CompleteSemilatticeSup.toHasSup.{u2} (Subring.{u2} S _inst_2) (CompleteLattice.toCompleteSemilatticeSup.{u2} (Subring.{u2} S _inst_2) (Subring.completeLattice.{u2} S _inst_2))) ι (fun (i : ι) => Subring.map.{u1, u2} R S _inst_1 _inst_2 f (s i)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_2 : Ring.{u3} S] {ι : Sort.{u1}} (f : RingHom.{u2, u3} R S (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (Ring.toSemiring.{u3} S _inst_2))) (s : ι -> (Subring.{u2} R _inst_1)), Eq.{succ u3} (Subring.{u3} S _inst_2) (Subring.map.{u2, u3} R S _inst_1 _inst_2 f (iSup.{u2, u1} (Subring.{u2} R _inst_1) (CompleteLattice.toSupSet.{u2} (Subring.{u2} R _inst_1) (Subring.instCompleteLatticeSubring.{u2} R _inst_1)) ι s)) (iSup.{u3, u1} (Subring.{u3} S _inst_2) (CompleteLattice.toSupSet.{u3} (Subring.{u3} S _inst_2) (Subring.instCompleteLatticeSubring.{u3} S _inst_2)) ι (fun (i : ι) => Subring.map.{u2, u3} R S _inst_1 _inst_2 f (s i)))
Case conversion may be inaccurate. Consider using '#align subring.map_supr Subring.map_iSupₓ'. -/
theorem map_iSup {ι : Sort _} (f : R →+* S) (s : ι → Subring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
#align subring.map_supr Subring.map_iSup

/- warning: subring.comap_inf -> Subring.comap_inf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u2} S _inst_2) (t : Subring.{u2} S _inst_2) (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (Inf.inf.{u2} (Subring.{u2} S _inst_2) (Subring.hasInf.{u2} S _inst_2) s t)) (Inf.inf.{u1} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f s) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f t))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u2} S _inst_2) (t : Subring.{u2} S _inst_2) (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (Inf.inf.{u2} (Subring.{u2} S _inst_2) (Subring.instInfSubring.{u2} S _inst_2) s t)) (Inf.inf.{u1} (Subring.{u1} R _inst_1) (Subring.instInfSubring.{u1} R _inst_1) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f s) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f t))
Case conversion may be inaccurate. Consider using '#align subring.comap_inf Subring.comap_infₓ'. -/
theorem comap_inf (s t : Subring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf
#align subring.comap_inf Subring.comap_inf

/- warning: subring.comap_infi -> Subring.comap_iInf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {ι : Sort.{u3}} (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (s : ι -> (Subring.{u2} S _inst_2)), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (iInf.{u2, u3} (Subring.{u2} S _inst_2) (Subring.hasInf.{u2} S _inst_2) ι s)) (iInf.{u1, u3} (Subring.{u1} R _inst_1) (Subring.hasInf.{u1} R _inst_1) ι (fun (i : ι) => Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (s i)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_2 : Ring.{u3} S] {ι : Sort.{u1}} (f : RingHom.{u2, u3} R S (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (Ring.toSemiring.{u3} S _inst_2))) (s : ι -> (Subring.{u3} S _inst_2)), Eq.{succ u2} (Subring.{u2} R _inst_1) (Subring.comap.{u2, u3} R S _inst_1 _inst_2 f (iInf.{u3, u1} (Subring.{u3} S _inst_2) (Subring.instInfSetSubring.{u3} S _inst_2) ι s)) (iInf.{u2, u1} (Subring.{u2} R _inst_1) (Subring.instInfSetSubring.{u2} R _inst_1) ι (fun (i : ι) => Subring.comap.{u2, u3} R S _inst_1 _inst_2 f (s i)))
Case conversion may be inaccurate. Consider using '#align subring.comap_infi Subring.comap_iInfₓ'. -/
theorem comap_iInf {ι : Sort _} (f : R →+* S) (s : ι → Subring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf
#align subring.comap_infi Subring.comap_iInf

/- warning: subring.map_bot -> Subring.map_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Eq.{succ u2} (Subring.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.hasBot.{u1} R _inst_1))) (Bot.bot.{u2} (Subring.{u2} S _inst_2) (Subring.hasBot.{u2} S _inst_2))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Eq.{succ u2} (Subring.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 f (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.instBotSubring.{u1} R _inst_1))) (Bot.bot.{u2} (Subring.{u2} S _inst_2) (Subring.instBotSubring.{u2} S _inst_2))
Case conversion may be inaccurate. Consider using '#align subring.map_bot Subring.map_botₓ'. -/
@[simp]
theorem map_bot (f : R →+* S) : (⊥ : Subring R).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align subring.map_bot Subring.map_bot

/- warning: subring.comap_top -> Subring.comap_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.hasTop.{u2} S _inst_2))) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.instTopSubring.{u2} S _inst_2))) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align subring.comap_top Subring.comap_topₓ'. -/
@[simp]
theorem comap_top (f : R →+* S) : (⊤ : Subring S).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align subring.comap_top Subring.comap_top

/- warning: subring.prod -> Subring.prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S], (Subring.{u1} R _inst_1) -> (Subring.{u2} S _inst_2) -> (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S], (Subring.{u1} R _inst_1) -> (Subring.{u2} S _inst_2) -> (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align subring.prod Subring.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given `subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×̂ t`
as a subring of `R × S`. -/
def prod (s : Subring R) (t : Subring S) : Subring (R × S) :=
  { s.toSubmonoid.Prod t.toSubmonoid, s.toAddSubgroup.Prod t.toAddSubgroup with carrier := s ×ˢ t }
#align subring.prod Subring.prod

/- warning: subring.coe_prod -> Subring.coe_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1) (t : Subring.{u2} S _inst_2), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} R S)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} R S)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} R S)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} R S)) (SetLike.Set.hasCoeT.{max u1 u2, max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Prod.{u1, u2} R S) (Subring.setLike.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2))))) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)) (Set.prod.{u1, u2} R S ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subring.{u2} S _inst_2) (Set.{u2} S) (HasLiftT.mk.{succ u2, succ u2} (Subring.{u2} S _inst_2) (Set.{u2} S) (CoeTCₓ.coe.{succ u2, succ u2} (Subring.{u2} S _inst_2) (Set.{u2} S) (SetLike.Set.hasCoeT.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)))) t))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1) (t : Subring.{u2} S _inst_2), Eq.{max (succ u1) (succ u2)} (Set.{max u1 u2} (Prod.{u1, u2} R S)) (SetLike.coe.{max u1 u2, max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Prod.{u1, u2} R S) (Subring.instSetLikeSubring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)) (Set.prod.{u1, u2} R S (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s) (SetLike.coe.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2) t))
Case conversion may be inaccurate. Consider using '#align subring.coe_prod Subring.coe_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[norm_cast]
theorem coe_prod (s : Subring R) (t : Subring S) : (s.Prod t : Set (R × S)) = s ×ˢ t :=
  rfl
#align subring.coe_prod Subring.coe_prod

/- warning: subring.mem_prod -> Subring.mem_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {s : Subring.{u1} R _inst_1} {t : Subring.{u2} S _inst_2} {p : Prod.{u1, u2} R S}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} R S) (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (SetLike.hasMem.{max u1 u2, max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Prod.{u1, u2} R S) (Subring.setLike.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2))) p (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)) (And (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (Prod.fst.{u1, u2} R S p) s) (Membership.Mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.hasMem.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (Prod.snd.{u1, u2} R S p) t))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {s : Subring.{u1} R _inst_1} {t : Subring.{u2} S _inst_2} {p : Prod.{u1, u2} R S}, Iff (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} R S) (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (SetLike.instMembership.{max u1 u2, max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Prod.{u1, u2} R S) (Subring.instSetLikeSubring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2))) p (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)) (And (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) (Prod.fst.{u1, u2} R S p) s) (Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) (Prod.snd.{u1, u2} R S p) t))
Case conversion may be inaccurate. Consider using '#align subring.mem_prod Subring.mem_prodₓ'. -/
theorem mem_prod {s : Subring R} {t : Subring S} {p : R × S} : p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align subring.mem_prod Subring.mem_prod

/- warning: subring.prod_mono -> Subring.prod_mono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {{s₁ : Subring.{u1} R _inst_1}} {{s₂ : Subring.{u1} R _inst_1}}, (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) s₁ s₂) -> (forall {{t₁ : Subring.{u2} S _inst_2}} {{t₂ : Subring.{u2} S _inst_2}}, (LE.le.{u2} (Subring.{u2} S _inst_2) (Preorder.toHasLe.{u2} (Subring.{u2} S _inst_2) (PartialOrder.toPreorder.{u2} (Subring.{u2} S _inst_2) (SetLike.partialOrder.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)))) t₁ t₂) -> (LE.le.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Preorder.toHasLe.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Prod.{u1, u2} R S) (Subring.setLike.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2))))) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s₁ t₁) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s₂ t₂)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {{s₁ : Subring.{u1} R _inst_1}} {{s₂ : Subring.{u1} R _inst_1}}, (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) s₁ s₂) -> (forall {{t₁ : Subring.{u2} S _inst_2}} {{t₂ : Subring.{u2} S _inst_2}}, (LE.le.{u2} (Subring.{u2} S _inst_2) (Preorder.toLE.{u2} (Subring.{u2} S _inst_2) (PartialOrder.toPreorder.{u2} (Subring.{u2} S _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subring.{u2} S _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subring.{u2} S _inst_2) (Subring.instCompleteLatticeSubring.{u2} S _inst_2))))) t₁ t₂) -> (LE.le.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.instCompleteLatticeSubring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)))))) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s₁ t₁) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s₂ t₂)))
Case conversion may be inaccurate. Consider using '#align subring.prod_mono Subring.prod_monoₓ'. -/
@[mono]
theorem prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subring S⦄ (ht : t₁ ≤ t₂) :
    s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht
#align subring.prod_mono Subring.prod_mono

/- warning: subring.prod_mono_right -> Subring.prod_mono_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1), Monotone.{u2, max u1 u2} (Subring.{u2} S _inst_2) (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (PartialOrder.toPreorder.{u2} (Subring.{u2} S _inst_2) (SetLike.partialOrder.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2))) (PartialOrder.toPreorder.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Prod.{u1, u2} R S) (Subring.setLike.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)))) (fun (t : Subring.{u2} S _inst_2) => Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1), Monotone.{u2, max u1 u2} (Subring.{u2} S _inst_2) (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (PartialOrder.toPreorder.{u2} (Subring.{u2} S _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subring.{u2} S _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subring.{u2} S _inst_2) (Subring.instCompleteLatticeSubring.{u2} S _inst_2)))) (PartialOrder.toPreorder.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.instCompleteLatticeSubring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2))))) (fun (t : Subring.{u2} S _inst_2) => Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)
Case conversion may be inaccurate. Consider using '#align subring.prod_mono_right Subring.prod_mono_rightₓ'. -/
theorem prod_mono_right (s : Subring R) : Monotone fun t : Subring S => s.Prod t :=
  prod_mono (le_refl s)
#align subring.prod_mono_right Subring.prod_mono_right

/- warning: subring.prod_mono_left -> Subring.prod_mono_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (t : Subring.{u2} S _inst_2), Monotone.{u1, max u1 u2} (Subring.{u1} R _inst_1) (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))) (PartialOrder.toPreorder.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Prod.{u1, u2} R S) (Subring.setLike.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)))) (fun (s : Subring.{u1} R _inst_1) => Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (t : Subring.{u2} S _inst_2), Monotone.{u1, max u1 u2} (Subring.{u1} R _inst_1) (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1)))) (PartialOrder.toPreorder.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.instCompleteLatticeSubring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2))))) (fun (s : Subring.{u1} R _inst_1) => Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)
Case conversion may be inaccurate. Consider using '#align subring.prod_mono_left Subring.prod_mono_leftₓ'. -/
theorem prod_mono_left (t : Subring S) : Monotone fun s : Subring R => s.Prod t := fun s₁ s₂ hs =>
  prod_mono hs (le_refl t)
#align subring.prod_mono_left Subring.prod_mono_left

/- warning: subring.prod_top -> Subring.prod_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1), Eq.{succ (max u1 u2)} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.hasTop.{u2} S _inst_2))) (Subring.comap.{max u1 u2, u1} (Prod.{u1, u2} R S) R (Prod.ring.{u1, u2} R S _inst_1 _inst_2) _inst_1 (RingHom.fst.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) s)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1), Eq.{max (succ u1) (succ u2)} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.instTopSubring.{u2} S _inst_2))) (Subring.comap.{max u1 u2, u1} (Prod.{u1, u2} R S) R (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2) _inst_1 (RingHom.fst.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) s)
Case conversion may be inaccurate. Consider using '#align subring.prod_top Subring.prod_topₓ'. -/
theorem prod_top (s : Subring R) : s.Prod (⊤ : Subring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]
#align subring.prod_top Subring.prod_top

/- warning: subring.top_prod -> Subring.top_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u2} S _inst_2), Eq.{succ (max u1 u2)} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1)) s) (Subring.comap.{max u1 u2, u2} (Prod.{u1, u2} R S) S (Prod.ring.{u1, u2} R S _inst_1 _inst_2) _inst_2 (RingHom.snd.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) s)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u2} S _inst_2), Eq.{max (succ u1) (succ u2)} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)) s) (Subring.comap.{max u1 u2, u2} (Prod.{u1, u2} R S) S (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2) _inst_2 (RingHom.snd.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) s)
Case conversion may be inaccurate. Consider using '#align subring.top_prod Subring.top_prodₓ'. -/
theorem top_prod (s : Subring S) : (⊤ : Subring R).Prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]
#align subring.top_prod Subring.top_prod

/- warning: subring.top_prod_top -> Subring.top_prod_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S], Eq.{succ (max u1 u2)} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1)) (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.hasTop.{u2} S _inst_2))) (Top.top.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Subring.hasTop.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S], Eq.{max (succ u1) (succ u2)} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)) (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.instTopSubring.{u2} S _inst_2))) (Top.top.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.instTopSubring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align subring.top_prod_top Subring.top_prod_topₓ'. -/
@[simp]
theorem top_prod_top : (⊤ : Subring R).Prod (⊤ : Subring S) = ⊤ :=
  (top_prod _).trans <| comap_top _
#align subring.top_prod_top Subring.top_prod_top

/- warning: subring.prod_equiv -> Subring.prodEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subring.prod_equiv Subring.prodEquivₓ'. -/
/-- Product of subrings is isomorphic to their product as rings. -/
def prodEquiv (s : Subring R) (t : Subring S) : s.Prod t ≃+* s × t :=
  { Equiv.Set.prod ↑s ↑t with
    map_mul' := fun x y => rfl
    map_add' := fun x y => rfl }
#align subring.prod_equiv Subring.prodEquiv

/- warning: subring.mem_supr_of_directed -> Subring.mem_iSup_of_directed is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {ι : Sort.{u2}} [hι : Nonempty.{u2} ι] {S : ι -> (Subring.{u1} R _inst_1)}, (Directed.{u1, u2} (Subring.{u1} R _inst_1) ι (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))))) S) -> (forall {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (iSup.{u1, u2} (Subring.{u1} R _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1))) ι (fun (i : ι) => S i))) (Exists.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (S i))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Sort.{u1}} [hι : Nonempty.{u1} ι] {S : ι -> (Subring.{u2} R _inst_1)}, (Directed.{u2, u1} (Subring.{u2} R _inst_1) ι (fun (x._@.Mathlib.RingTheory.Subring.Basic._hyg.10386 : Subring.{u2} R _inst_1) (x._@.Mathlib.RingTheory.Subring.Basic._hyg.10388 : Subring.{u2} R _inst_1) => LE.le.{u2} (Subring.{u2} R _inst_1) (Preorder.toLE.{u2} (Subring.{u2} R _inst_1) (PartialOrder.toPreorder.{u2} (Subring.{u2} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subring.{u2} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subring.{u2} R _inst_1) (Subring.instCompleteLatticeSubring.{u2} R _inst_1))))) x._@.Mathlib.RingTheory.Subring.Basic._hyg.10386 x._@.Mathlib.RingTheory.Subring.Basic._hyg.10388) S) -> (forall {x : R}, Iff (Membership.mem.{u2, u2} R (Subring.{u2} R _inst_1) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1)) x (iSup.{u2, u1} (Subring.{u2} R _inst_1) (CompleteLattice.toSupSet.{u2} (Subring.{u2} R _inst_1) (Subring.instCompleteLatticeSubring.{u2} R _inst_1)) ι (fun (i : ι) => S i))) (Exists.{u1} ι (fun (i : ι) => Membership.mem.{u2, u2} R (Subring.{u2} R _inst_1) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1)) x (S i))))
Case conversion may be inaccurate. Consider using '#align subring.mem_supr_of_directed Subring.mem_iSup_of_directedₓ'. -/
/-- The underlying set of a non-empty directed Sup of subrings is just a union of the subrings.
  Note that this fails without the directedness assumption (the union of two subrings is
  typically not a subring) -/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subring R} (hS : Directed (· ≤ ·) S)
    {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i :=
  by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_iSup S i) hi⟩
  let U : Subring R :=
    Subring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid) (⨆ i, (S i).toAddSubgroup)
      (Submonoid.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
      (AddSubgroup.coe_iSup_of_directed <| hS.mono_comp _ fun _ _ => id)
  suffices (⨆ i, S i) ≤ U by simpa using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩
#align subring.mem_supr_of_directed Subring.mem_iSup_of_directed

/- warning: subring.coe_supr_of_directed -> Subring.coe_iSup_of_directed is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {ι : Sort.{u2}} [hι : Nonempty.{u2} ι] {S : ι -> (Subring.{u1} R _inst_1)}, (Directed.{u1, u2} (Subring.{u1} R _inst_1) ι (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))))) S) -> (Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (iSup.{u1, u2} (Subring.{u1} R _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1))) ι (fun (i : ι) => S i))) (Set.iUnion.{u1, u2} R ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (S i))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Sort.{u1}} [hι : Nonempty.{u1} ι] {S : ι -> (Subring.{u2} R _inst_1)}, (Directed.{u2, u1} (Subring.{u2} R _inst_1) ι (fun (x._@.Mathlib.RingTheory.Subring.Basic._hyg.10680 : Subring.{u2} R _inst_1) (x._@.Mathlib.RingTheory.Subring.Basic._hyg.10682 : Subring.{u2} R _inst_1) => LE.le.{u2} (Subring.{u2} R _inst_1) (Preorder.toLE.{u2} (Subring.{u2} R _inst_1) (PartialOrder.toPreorder.{u2} (Subring.{u2} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subring.{u2} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subring.{u2} R _inst_1) (Subring.instCompleteLatticeSubring.{u2} R _inst_1))))) x._@.Mathlib.RingTheory.Subring.Basic._hyg.10680 x._@.Mathlib.RingTheory.Subring.Basic._hyg.10682) S) -> (Eq.{succ u2} (Set.{u2} R) (SetLike.coe.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1) (iSup.{u2, u1} (Subring.{u2} R _inst_1) (CompleteLattice.toSupSet.{u2} (Subring.{u2} R _inst_1) (Subring.instCompleteLatticeSubring.{u2} R _inst_1)) ι (fun (i : ι) => S i))) (Set.iUnion.{u2, u1} R ι (fun (i : ι) => SetLike.coe.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1) (S i))))
Case conversion may be inaccurate. Consider using '#align subring.coe_supr_of_directed Subring.coe_iSup_of_directedₓ'. -/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subring R} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subring R) : Set R) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_supr_of_directed hS]
#align subring.coe_supr_of_directed Subring.coe_iSup_of_directed

/- warning: subring.mem_Sup_of_directed_on -> Subring.mem_sSup_of_directedOn is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Set.{u1} (Subring.{u1} R _inst_1)}, (Set.Nonempty.{u1} (Subring.{u1} R _inst_1) S) -> (DirectedOn.{u1} (Subring.{u1} R _inst_1) (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))))) S) -> (forall {x : R}, Iff (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (SupSet.sSup.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1))) S)) (Exists.{succ u1} (Subring.{u1} R _inst_1) (fun (s : Subring.{u1} R _inst_1) => Exists.{0} (Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) s S) (fun (H : Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) s S) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x s))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Set.{u1} (Subring.{u1} R _inst_1)}, (Set.Nonempty.{u1} (Subring.{u1} R _inst_1) S) -> (DirectedOn.{u1} (Subring.{u1} R _inst_1) (fun (x._@.Mathlib.RingTheory.Subring.Basic._hyg.10775 : Subring.{u1} R _inst_1) (x._@.Mathlib.RingTheory.Subring.Basic._hyg.10777 : Subring.{u1} R _inst_1) => LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) x._@.Mathlib.RingTheory.Subring.Basic._hyg.10775 x._@.Mathlib.RingTheory.Subring.Basic._hyg.10777) S) -> (forall {x : R}, Iff (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (SupSet.sSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toSupSet.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1)) S)) (Exists.{succ u1} (Subring.{u1} R _inst_1) (fun (s : Subring.{u1} R _inst_1) => And (Membership.mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.instMembershipSet.{u1} (Subring.{u1} R _inst_1)) s S) (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s))))
Case conversion may be inaccurate. Consider using '#align subring.mem_Sup_of_directed_on Subring.mem_sSup_of_directedOnₓ'. -/
theorem mem_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s :=
  by
  haveI : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_supr_of_directed hS.directed_coe, SetCoe.exists, Subtype.coe_mk]
#align subring.mem_Sup_of_directed_on Subring.mem_sSup_of_directedOn

/- warning: subring.coe_Sup_of_directed_on -> Subring.coe_sSup_of_directedOn is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Set.{u1} (Subring.{u1} R _inst_1)}, (Set.Nonempty.{u1} (Subring.{u1} R _inst_1) S) -> (DirectedOn.{u1} (Subring.{u1} R _inst_1) (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1))))) S) -> (Eq.{succ u1} (Set.{u1} R) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (SupSet.sSup.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subring.{u1} R _inst_1) (Subring.completeLattice.{u1} R _inst_1))) S)) (Set.iUnion.{u1, succ u1} R (Subring.{u1} R _inst_1) (fun (s : Subring.{u1} R _inst_1) => Set.iUnion.{u1, 0} R (Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) s S) (fun (H : Membership.Mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.hasMem.{u1} (Subring.{u1} R _inst_1)) s S) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) s))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Set.{u1} (Subring.{u1} R _inst_1)}, (Set.Nonempty.{u1} (Subring.{u1} R _inst_1) S) -> (DirectedOn.{u1} (Subring.{u1} R _inst_1) (fun (x._@.Mathlib.RingTheory.Subring.Basic._hyg.10870 : Subring.{u1} R _inst_1) (x._@.Mathlib.RingTheory.Subring.Basic._hyg.10872 : Subring.{u1} R _inst_1) => LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) x._@.Mathlib.RingTheory.Subring.Basic._hyg.10870 x._@.Mathlib.RingTheory.Subring.Basic._hyg.10872) S) -> (Eq.{succ u1} (Set.{u1} R) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (SupSet.sSup.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toSupSet.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1)) S)) (Set.iUnion.{u1, succ u1} R (Subring.{u1} R _inst_1) (fun (s : Subring.{u1} R _inst_1) => Set.iUnion.{u1, 0} R (Membership.mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.instMembershipSet.{u1} (Subring.{u1} R _inst_1)) s S) (fun (H : Membership.mem.{u1, u1} (Subring.{u1} R _inst_1) (Set.{u1} (Subring.{u1} R _inst_1)) (Set.instMembershipSet.{u1} (Subring.{u1} R _inst_1)) s S) => SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) s))))
Case conversion may be inaccurate. Consider using '#align subring.coe_Sup_of_directed_on Subring.coe_sSup_of_directedOnₓ'. -/
theorem coe_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_Sup_of_directed_on Sne hS]
#align subring.coe_Sup_of_directed_on Subring.coe_sSup_of_directedOn

/- warning: subring.mem_map_equiv -> Subring.mem_map_equiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subring.mem_map_equiv Subring.mem_map_equivₓ'. -/
theorem mem_map_equiv {f : R ≃+* S} {K : Subring R} {x : S} :
    x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x
#align subring.mem_map_equiv Subring.mem_map_equiv

/- warning: subring.map_equiv_eq_comap_symm -> Subring.map_equiv_eq_comap_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subring.map_equiv_eq_comap_symm Subring.map_equiv_eq_comap_symmₓ'. -/
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subring R) :
    K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)
#align subring.map_equiv_eq_comap_symm Subring.map_equiv_eq_comap_symm

/- warning: subring.comap_equiv_eq_map_symm -> Subring.comap_equiv_eq_map_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subring.comap_equiv_eq_map_symm Subring.comap_equiv_eq_map_symmₓ'. -/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subring S) :
    K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm
#align subring.comap_equiv_eq_map_symm Subring.comap_equiv_eq_map_symm

end Subring

namespace RingHom

variable {s : Subring R}

open Subring

/- warning: ring_hom.range_restrict -> RingHom.rangeRestrict is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), RingHom.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Ring.toNonAssocRing.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Subring.toRing.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), RingHom.{u1, u2} R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))
Case conversion may be inaccurate. Consider using '#align ring_hom.range_restrict RingHom.rangeRestrictₓ'. -/
/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `set.range_factorization`. -/
def rangeRestrict (f : R →+* S) : R →+* f.range :=
  f.codRestrict f.range fun x => ⟨x, rfl⟩
#align ring_hom.range_restrict RingHom.rangeRestrict

/- warning: ring_hom.coe_range_restrict -> RingHom.coe_rangeRestrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.coe_range_restrict RingHom.coe_rangeRestrictₓ'. -/
@[simp]
theorem coe_rangeRestrict (f : R →+* S) (x : R) : (f.range_restrict x : S) = f x :=
  rfl
#align ring_hom.coe_range_restrict RingHom.coe_rangeRestrict

/- warning: ring_hom.range_restrict_surjective -> RingHom.rangeRestrict_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Function.Surjective.{succ u1, succ u2} R (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Ring.toNonAssocRing.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Subring.toRing.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))))) (fun (_x : RingHom.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Ring.toNonAssocRing.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Subring.toRing.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))))) => R -> (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (RingHom.hasCoeToFun.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Ring.toNonAssocRing.{u2} (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Subring.toRing.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))))) (RingHom.rangeRestrict.{u1, u2} R S _inst_1 _inst_2 f))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Function.Surjective.{succ u1, succ u2} R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))) R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))) R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))) R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (RingHom.instRingHomClassRingHom.{u1, u2} R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subsemiring.toNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))))))) (RingHom.rangeRestrict.{u1, u2} R S _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align ring_hom.range_restrict_surjective RingHom.rangeRestrict_surjectiveₓ'. -/
theorem rangeRestrict_surjective (f : R →+* S) : Function.Surjective f.range_restrict :=
  fun ⟨y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩
#align ring_hom.range_restrict_surjective RingHom.rangeRestrict_surjective

/- warning: ring_hom.range_top_iff_surjective -> RingHom.range_top_iff_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))}, Iff (Eq.{succ u2} (Subring.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f) (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.hasTop.{u2} S _inst_2))) (Function.Surjective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))}, Iff (Eq.{succ u2} (Subring.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f) (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.instTopSubring.{u2} S _inst_2))) (Function.Surjective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f))
Case conversion may be inaccurate. Consider using '#align ring_hom.range_top_iff_surjective RingHom.range_top_iff_surjectiveₓ'. -/
theorem range_top_iff_surjective {f : R →+* S} :
    f.range = (⊤ : Subring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, coe_top]) Set.range_iff_surjective
#align ring_hom.range_top_iff_surjective RingHom.range_top_iff_surjective

/- warning: ring_hom.range_top_of_surjective -> RingHom.range_top_of_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), (Function.Surjective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f)) -> (Eq.{succ u2} (Subring.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f) (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.hasTop.{u2} S _inst_2)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), (Function.Surjective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f)) -> (Eq.{succ u2} (Subring.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f) (Top.top.{u2} (Subring.{u2} S _inst_2) (Subring.instTopSubring.{u2} S _inst_2)))
Case conversion may be inaccurate. Consider using '#align ring_hom.range_top_of_surjective RingHom.range_top_of_surjectiveₓ'. -/
/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
theorem range_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : Subring S) :=
  range_top_iff_surjective.2 hf
#align ring_hom.range_top_of_surjective RingHom.range_top_of_surjective

#print RingHom.eqLocus /-
/-- The subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a subring of R -/
def eqLocus (f g : R →+* S) : Subring R :=
  { (f : R →* S).eqLocus g, (f : R →+ S).eqLocus g with carrier := { x | f x = g x } }
#align ring_hom.eq_locus RingHom.eqLocus
-/

/- warning: ring_hom.eq_locus_same -> RingHom.eqLocus_same is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), Eq.{succ u1} (Subring.{u1} R _inst_1) (RingHom.eqLocus.{u1, u2} R S _inst_1 _inst_2 f f) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))), Eq.{succ u1} (Subring.{u1} R _inst_1) (RingHom.eqLocus.{u1, u2} R S _inst_1 _inst_2 f f) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align ring_hom.eq_locus_same RingHom.eqLocus_sameₓ'. -/
@[simp]
theorem eqLocus_same (f : R →+* S) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _
#align ring_hom.eq_locus_same RingHom.eqLocus_same

/- warning: ring_hom.eq_on_set_closure -> RingHom.eqOn_set_closure is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.eq_on_set_closure RingHom.eqOn_set_closureₓ'. -/
/-- If two ring homomorphisms are equal on a set, then they are equal on its subring closure. -/
theorem eqOn_set_closure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h
#align ring_hom.eq_on_set_closure RingHom.eqOn_set_closure

/- warning: ring_hom.eq_of_eq_on_set_top -> RingHom.eq_of_eqOn_set_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))} {g : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))}, (Set.EqOn.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) g) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} R _inst_1) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} R _inst_1) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1)))) -> (Eq.{max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f g)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))} {g : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))}, (Set.EqOn.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) g) (SetLike.coe.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1)))) -> (Eq.{max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) f g)
Case conversion may be inaccurate. Consider using '#align ring_hom.eq_of_eq_on_set_top RingHom.eq_of_eqOn_set_topₓ'. -/
theorem eq_of_eqOn_set_top {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subring R)) : f = g :=
  ext fun x => h trivial
#align ring_hom.eq_of_eq_on_set_top RingHom.eq_of_eqOn_set_top

/- warning: ring_hom.eq_of_eq_on_set_dense -> RingHom.eq_of_eqOn_set_dense is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {s : Set.{u1} R}, (Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 s) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.hasTop.{u1} R _inst_1))) -> (forall {f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))} {g : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))}, (Set.EqOn.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) g) s) -> (Eq.{max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f g))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {s : Set.{u1} R}, (Eq.{succ u1} (Subring.{u1} R _inst_1) (Subring.closure.{u1} R _inst_1 s) (Top.top.{u1} (Subring.{u1} R _inst_1) (Subring.instTopSubring.{u1} R _inst_1))) -> (forall {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))} {g : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))}, (Set.EqOn.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) g) s) -> (Eq.{max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) f g))
Case conversion may be inaccurate. Consider using '#align ring_hom.eq_of_eq_on_set_dense RingHom.eq_of_eqOn_set_denseₓ'. -/
theorem eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_set_top <| hs ▸ eqOn_set_closure h
#align ring_hom.eq_of_eq_on_set_dense RingHom.eq_of_eqOn_set_dense

/- warning: ring_hom.closure_preimage_le -> RingHom.closure_preimage_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (s : Set.{u2} S), LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.closure.{u1} R _inst_1 (Set.preimage.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f) s)) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (Subring.closure.{u2} S _inst_2 s))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (s : Set.{u2} S), LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) (Subring.closure.{u1} R _inst_1 (Set.preimage.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f) s)) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (Subring.closure.{u2} S _inst_2 s))
Case conversion may be inaccurate. Consider using '#align ring_hom.closure_preimage_le RingHom.closure_preimage_leₓ'. -/
theorem closure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align ring_hom.closure_preimage_le RingHom.closure_preimage_le

#print RingHom.map_closure /-
/-- The image under a ring homomorphism of the subring generated by a set equals
the subring generated by the image of the set. -/
theorem map_closure (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (closure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)
#align ring_hom.map_closure RingHom.map_closure
-/

end RingHom

namespace Subring

open RingHom

/- warning: subring.inclusion -> Subring.inclusion is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Subring.{u1} R _inst_1} {T : Subring.{u1} R _inst_1}, (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) S T) -> (RingHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) T) (NonAssocRing.toNonAssocSemiring.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) (Ring.toNonAssocRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) (Subring.toRing.{u1} R _inst_1 S))) (NonAssocRing.toNonAssocSemiring.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) T) (Ring.toNonAssocRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) T) (Subring.toRing.{u1} R _inst_1 T))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Subring.{u1} R _inst_1} {T : Subring.{u1} R _inst_1}, (LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) S T) -> (RingHom.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x S)) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x T)) (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 S)) (Subsemiring.toNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 T)))
Case conversion may be inaccurate. Consider using '#align subring.inclusion Subring.inclusionₓ'. -/
/-- The ring homomorphism associated to an inclusion of subrings. -/
def inclusion {S T : Subring R} (h : S ≤ T) : S →+* T :=
  S.Subtype.codRestrict _ fun x => h x.2
#align subring.inclusion Subring.inclusion

/- warning: subring.range_subtype -> Subring.range_subtype is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} (Subring.{u1} R _inst_1) (RingHom.range.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) R (Subring.toRing.{u1} R _inst_1 s) _inst_1 (Subring.subtype.{u1} R _inst_1 s)) s
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (s : Subring.{u1} R _inst_1), Eq.{succ u1} (Subring.{u1} R _inst_1) (RingHom.range.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) R (Subring.toRing.{u1} R _inst_1 s) _inst_1 (Subring.subtype.{u1} R _inst_1 s)) s
Case conversion may be inaccurate. Consider using '#align subring.range_subtype Subring.range_subtypeₓ'. -/
@[simp]
theorem range_subtype (s : Subring R) : s.Subtype.range = s :=
  SetLike.coe_injective <| (coe_rangeS _).trans Subtype.range_coe
#align subring.range_subtype Subring.range_subtype

/- warning: subring.range_fst -> Subring.range_fst is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S], Eq.{succ u1} (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (RingHom.rangeS.{max u1 u2, u1} (Prod.{u1, u2} R S) R (Prod.nonAssocSemiring.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (RingHom.fst.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)))) (Top.top.{u1} (Subsemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (Subsemiring.hasTop.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S], Eq.{succ u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHom.rangeS.{max u1 u2, u1} (Prod.{u1, u2} R S) R (Prod.instNonAssocSemiringProd.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (RingHom.fst.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (Top.top.{u1} (Subsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Subsemiring.instTopSubsemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align subring.range_fst Subring.range_fstₓ'. -/
@[simp]
theorem range_fst : (fst R S).srange = ⊤ :=
  (fst R S).srange_top_of_surjective <| Prod.fst_surjective
#align subring.range_fst Subring.range_fst

/- warning: subring.range_snd -> Subring.range_snd is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S], Eq.{succ u2} (Subsemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (RingHom.rangeS.{max u1 u2, u2} (Prod.{u1, u2} R S) S (Prod.nonAssocSemiring.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)) (RingHom.snd.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)))) (Top.top.{u2} (Subsemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (Subsemiring.hasTop.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S], Eq.{succ u2} (Subsemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHom.rangeS.{max u1 u2, u2} (Prod.{u1, u2} R S) S (Prod.instNonAssocSemiringProd.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.snd.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (Top.top.{u2} (Subsemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (Subsemiring.instTopSubsemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))))
Case conversion may be inaccurate. Consider using '#align subring.range_snd Subring.range_sndₓ'. -/
@[simp]
theorem range_snd : (snd R S).srange = ⊤ :=
  (snd R S).srange_top_of_surjective <| Prod.snd_surjective
#align subring.range_snd Subring.range_snd

/- warning: subring.prod_bot_sup_bot_prod -> Subring.prod_bot_sup_bot_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1) (t : Subring.{u2} S _inst_2), Eq.{succ (max u1 u2)} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Sup.sup.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (SemilatticeSup.toHasSup.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Lattice.toSemilatticeSup.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (CompleteLattice.toLattice.{max u1 u2} (Subring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2)) (Subring.completeLattice.{max u1 u2} (Prod.{u1, u2} R S) (Prod.ring.{u1, u2} R S _inst_1 _inst_2))))) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s (Bot.bot.{u2} (Subring.{u2} S _inst_2) (Subring.hasBot.{u2} S _inst_2))) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.hasBot.{u1} R _inst_1)) t)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (s : Subring.{u1} R _inst_1) (t : Subring.{u2} S _inst_2), Eq.{max (succ u1) (succ u2)} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Sup.sup.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (SemilatticeSup.toSup.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Lattice.toSemilatticeSup.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (CompleteLattice.toLattice.{max u1 u2} (Subring.{max u2 u1} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2)) (Subring.instCompleteLatticeSubring.{max u1 u2} (Prod.{u1, u2} R S) (Prod.instRingProd.{u1, u2} R S _inst_1 _inst_2))))) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s (Bot.bot.{u2} (Subring.{u2} S _inst_2) (Subring.instBotSubring.{u2} S _inst_2))) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 (Bot.bot.{u1} (Subring.{u1} R _inst_1) (Subring.instBotSubring.{u1} R _inst_1)) t)) (Subring.prod.{u1, u2} R S _inst_1 _inst_2 s t)
Case conversion may be inaccurate. Consider using '#align subring.prod_bot_sup_bot_prod Subring.prod_bot_sup_bot_prodₓ'. -/
@[simp]
theorem prod_bot_sup_bot_prod (s : Subring R) (t : Subring S) : s.Prod ⊥ ⊔ prod ⊥ t = s.Prod t :=
  le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.Prod ⊥ ≤ s.Prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.Prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)
#align subring.prod_bot_sup_bot_prod Subring.prod_bot_sup_bot_prod

end Subring

namespace RingEquiv

variable {s t : Subring R}

/- warning: ring_equiv.subring_congr -> RingEquiv.subringCongr is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Subring.{u1} R _inst_1} {t : Subring.{u1} R _inst_1}, (Eq.{succ u1} (Subring.{u1} R _inst_1) s t) -> (RingEquiv.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) t) (MulMemClass.mul.{u1, u1} R (Subring.{u1} R _inst_1) (MulOneClass.toHasMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Subring.setLike.{u1} R _inst_1) (RingEquiv.subringCongr._proof_1.{u1} R _inst_1) s) (AddMemClass.add.{u1, u1} R (Subring.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.setLike.{u1} R _inst_1) (RingEquiv.subringCongr._proof_2.{u1} R _inst_1) s) (MulMemClass.mul.{u1, u1} R (Subring.{u1} R _inst_1) (MulOneClass.toHasMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Subring.setLike.{u1} R _inst_1) (RingEquiv.subringCongr._proof_3.{u1} R _inst_1) t) (AddMemClass.add.{u1, u1} R (Subring.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.setLike.{u1} R _inst_1) (RingEquiv.subringCongr._proof_4.{u1} R _inst_1) t))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Subring.{u1} R _inst_1} {t : Subring.{u1} R _inst_1}, (Eq.{succ u1} (Subring.{u1} R _inst_1) s t) -> (RingEquiv.{u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x t)) (Submonoid.mul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s))) (Submonoid.mul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 t))) (Distrib.toAdd.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonUnitalNonAssocSemiring.toDistrib.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Ring.toNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subring.toRing.{u1} R _inst_1 s)))))) (Distrib.toAdd.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x t)) (NonUnitalNonAssocSemiring.toDistrib.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x t)) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x t)) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x t)) (Ring.toNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x t)) (Subring.toRing.{u1} R _inst_1 t)))))))
Case conversion may be inaccurate. Consider using '#align ring_equiv.subring_congr RingEquiv.subringCongrₓ'. -/
/-- Makes the identity isomorphism from a proof two subrings of a multiplicative
    monoid are equal. -/
def subringCongr (h : s = t) : s ≃+* t :=
  {
    Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align ring_equiv.subring_congr RingEquiv.subringCongr

/- warning: ring_equiv.of_left_inverse -> RingEquiv.ofLeftInverse is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {g : S -> R} {f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))}, (Function.LeftInverse.{succ u1, succ u2} R S g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f)) -> (RingEquiv.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (MulMemClass.mul.{u2, u2} S (Subring.{u2} S _inst_2) (MulOneClass.toHasMul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))))) (Subring.setLike.{u2} S _inst_2) (RingEquiv.ofLeftInverse._proof_1.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)) (AddMemClass.add.{u2, u2} S (Subring.{u2} S _inst_2) (AddZeroClass.toHasAdd.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddMonoidWithOne.toAddMonoid.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))))))) (Subring.setLike.{u2} S _inst_2) (RingEquiv.ofLeftInverse._proof_2.{u2} S _inst_2) (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {g : S -> R} {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))}, (Function.LeftInverse.{succ u1, succ u2} R S g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f)) -> (RingEquiv.{u1, u2} R (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (Submonoid.mul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (Subsemiring.toSubmonoid.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f)))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Distrib.toAdd.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (NonUnitalNonAssocSemiring.toDistrib.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (NonAssocRing.toNonUnitalNonAssocRing.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Ring.toNonAssocRing.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))) (Subring.toRing.{u2} S _inst_2 (RingHom.range.{u1, u2} R S _inst_1 _inst_2 f))))))))
Case conversion may be inaccurate. Consider using '#align ring_equiv.of_left_inverse RingEquiv.ofLeftInverseₓ'. -/
/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`ring_hom.range`. -/
def ofLeftInverse {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.range_restrict with
    toFun := fun x => f.range_restrict x
    invFun := fun x => (g ∘ f.range.Subtype) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_range.mp x.Prop
        show f (g x) = x by rw [← hx', h x'] }
#align ring_equiv.of_left_inverse RingEquiv.ofLeftInverse

/- warning: ring_equiv.of_left_inverse_apply -> RingEquiv.ofLeftInverse_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_equiv.of_left_inverse_apply RingEquiv.ofLeftInverse_applyₓ'. -/
@[simp]
theorem ofLeftInverse_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse h x) = f x :=
  rfl
#align ring_equiv.of_left_inverse_apply RingEquiv.ofLeftInverse_apply

/- warning: ring_equiv.of_left_inverse_symm_apply -> RingEquiv.ofLeftInverse_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_equiv.of_left_inverse_symm_apply RingEquiv.ofLeftInverse_symm_applyₓ'. -/
@[simp]
theorem ofLeftInverse_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl
#align ring_equiv.of_left_inverse_symm_apply RingEquiv.ofLeftInverse_symm_apply

/- warning: ring_equiv.subring_map -> RingEquiv.subringMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {s : Subring.{u1} R _inst_1} (e : RingEquiv.{u1, u2} R S (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (Distrib.toHasMul.{u2} S (Ring.toDistrib.{u2} S _inst_2)) (Distrib.toHasAdd.{u2} S (Ring.toDistrib.{u2} S _inst_2))), RingEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) s) (coeSort.{succ u2, succ (succ u2)} (Subring.{u2} S _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.setLike.{u2} S _inst_2)) (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)) e) s)) (MulMemClass.mul.{u1, u1} R (Subring.{u1} R _inst_1) (MulOneClass.toHasMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Subring.setLike.{u1} R _inst_1) (RingEquiv.subringMap._proof_1.{u1} R _inst_1) s) (AddMemClass.add.{u1, u1} R (Subring.{u1} R _inst_1) (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.setLike.{u1} R _inst_1) (RingEquiv.subringMap._proof_2.{u1} R _inst_1) s) (MulMemClass.mul.{u2, u2} S (Subring.{u2} S _inst_2) (MulOneClass.toHasMul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))))) (Subring.setLike.{u2} S _inst_2) (RingEquiv.subringMap._proof_3.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)) e) s)) (AddMemClass.add.{u2, u2} S (Subring.{u2} S _inst_2) (AddZeroClass.toHasAdd.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddMonoidWithOne.toAddMonoid.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))))))) (Subring.setLike.{u2} S _inst_2) (RingEquiv.subringMap._proof_4.{u2} S _inst_2) (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)) e) s))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] {s : Subring.{u1} R _inst_1} (e : RingEquiv.{u1, u2} R S (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (NonUnitalNonAssocRing.toMul.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Distrib.toAdd.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2)))))), RingEquiv.{u1, u2} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) e) s))) (Submonoid.mul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Subsemiring.toSubmonoid.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Subring.toSubsemiring.{u1} R _inst_1 s))) (Submonoid.mul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (Subsemiring.toSubmonoid.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (Subring.toSubsemiring.{u2} S _inst_2 (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) e) s)))) (Distrib.toAdd.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonUnitalNonAssocSemiring.toDistrib.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Ring.toNonAssocRing.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x s)) (Subring.toRing.{u1} R _inst_1 s)))))) (Distrib.toAdd.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) e) s))) (NonUnitalNonAssocSemiring.toDistrib.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) e) s))) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) e) s))) (NonAssocRing.toNonUnitalNonAssocRing.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) e) s))) (Ring.toNonAssocRing.{u2} (Subtype.{succ u2} S (fun (x : S) => Membership.mem.{u2, u2} S (Subring.{u2} S _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} S _inst_2) S (Subring.instSetLikeSubring.{u2} S _inst_2)) x (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) e) s))) (Subring.toRing.{u2} S _inst_2 (Subring.map.{u1, u2} R S _inst_1 _inst_2 (RingEquiv.toRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) e) s)))))))
Case conversion may be inaccurate. Consider using '#align ring_equiv.subring_map RingEquiv.subringMapₓ'. -/
/-- Given an equivalence `e : R ≃+* S` of rings and a subring `s` of `R`,
`subring_equiv_map e s` is the induced equivalence between `s` and `s.map e` -/
@[simps]
def subringMap (e : R ≃+* S) : s ≃+* s.map e.toRingHom :=
  e.subsemiringMap s.toSubsemiring
#align ring_equiv.subring_map RingEquiv.subringMap

end RingEquiv

namespace Subring

variable {s : Set R}

attribute [local reducible] closure

/- warning: subring.in_closure.rec_on -> Subring.InClosure.recOn is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {C : R -> Prop} {x : R}, (Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) -> (C (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))) -> (C (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))))))) -> (forall (z : R), (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) z s) -> (forall (n : R), (C n) -> (C (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) z n)))) -> (forall {x : R} {y : R}, (C x) -> (C y) -> (C (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1))) x y))) -> (C x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {C : R -> Prop} {x : R}, (Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.closure.{u1} R _inst_1 s)) -> (C (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) -> (C (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) -> (forall (z : R), (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) z s) -> (forall (n : R), (C n) -> (C (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) z n)))) -> (forall {x : R} {y : R}, (C x) -> (C y) -> (C (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x y))) -> (C x)
Case conversion may be inaccurate. Consider using '#align subring.in_closure.rec_on Subring.InClosure.recOnₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[elab_as_elim]
protected theorem InClosure.recOn {C : R → Prop} {x : R} (hx : x ∈ closure s) (h1 : C 1)
    (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) :
    C x := by
  have h0 : C 0 := add_neg_self (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩; clear hx
  induction' L with hd tl ih; · exact h0
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons, List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1; clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    ∃ L : List R, (∀ x ∈ L, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]; clear HP HL hd; induction' L with hd tl ih; · exact h1
    rw [List.forall_mem_cons] at HL'
    rw [List.prod_cons]
    exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]; clear HP HL hd; induction' L with hd tl ih; · exact hneg1
    rw [List.prod_cons, neg_mul_eq_mul_neg]
    rw [List.forall_mem_cons] at HL'
    exact hs _ HL'.1 _ (ih HL'.2)
  induction' hd with hd tl ih
  · exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> cases' HL.1 with hhd hhd
  ·
    exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inl <| by rw [List.prod_cons, List.prod_cons, HP]⟩
  · exact ⟨L, HL', Or.inr <| by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  ·
    exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inr <| by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
  · exact ⟨L, HL', Or.inl <| by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩
#align subring.in_closure.rec_on Subring.InClosure.recOn

/- warning: subring.closure_preimage_le -> Subring.closure_preimage_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (s : Set.{u2} S), LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toHasLe.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (SetLike.partialOrder.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)))) (Subring.closure.{u1} R _inst_1 (Set.preimage.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f) s)) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (Subring.closure.{u2} S _inst_2 s))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (s : Set.{u2} S), LE.le.{u1} (Subring.{u1} R _inst_1) (Preorder.toLE.{u1} (Subring.{u1} R _inst_1) (PartialOrder.toPreorder.{u1} (Subring.{u1} R _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} R _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} R _inst_1) (Subring.instCompleteLatticeSubring.{u1} R _inst_1))))) (Subring.closure.{u1} R _inst_1 (Set.preimage.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S _inst_2)))))) f) s)) (Subring.comap.{u1, u2} R S _inst_1 _inst_2 f (Subring.closure.{u2} S _inst_2 s))
Case conversion may be inaccurate. Consider using '#align subring.closure_preimage_le Subring.closure_preimage_leₓ'. -/
theorem closure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align subring.closure_preimage_le Subring.closure_preimage_le

end Subring

/- warning: add_subgroup.int_mul_mem -> AddSubgroup.int_mul_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {G : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))} (k : Int) {g : R}, (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) g G) -> (Membership.Mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))) R (AddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) k) g) G)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {G : AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))} (k : Int) {g : R}, (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)))) g G) -> (Membership.mem.{u1, u1} R (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1))) R (AddSubgroup.instSetLikeAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (Int.cast.{u1} R (Ring.toIntCast.{u1} R _inst_1) k) g) G)
Case conversion may be inaccurate. Consider using '#align add_subgroup.int_mul_mem AddSubgroup.int_mul_memₓ'. -/
theorem AddSubgroup.int_mul_mem {G : AddSubgroup R} (k : ℤ) {g : R} (h : g ∈ G) : (k : R) * g ∈ G :=
  by convert AddSubgroup.zsmul_mem G h k; simp
#align add_subgroup.int_mul_mem AddSubgroup.int_mul_mem

/-! ## Actions by `subring`s

These are just copies of the definitions about `subsemiring` starting from
`subsemiring.mul_action`.

When `R` is commutative, `algebra.of_subring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subring

variable {α β : Type _}

/-- The action by a subring is the action by the underlying ring. -/
instance [SMul R α] (S : Subring R) : SMul S α :=
  S.toSubsemiring.SMul

/- warning: subring.smul_def -> Subring.smul_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {α : Type.{u2}} [_inst_4 : SMul.{u1, u2} R α] {S : Subring.{u1} R _inst_1} (g : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) (m : α), Eq.{succ u2} α (SMul.smul.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) α (Subring.hasSmul.{u1, u2} R _inst_1 α _inst_4 S) g m) (SMul.smul.{u1, u2} R α _inst_4 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) R (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) R (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) R (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) R (coeSubtype.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.hasMem.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) x S))))) g) m)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {α : Type.{u1}} [_inst_4 : SMul.{u2, u1} R α] {S : Subring.{u2} R _inst_1} (g : Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Subring.{u2} R _inst_1) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1)) x S)) (m : α), Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} (Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Subring.{u2} R _inst_1) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1)) x S)) α α (instHSMul.{u2, u1} (Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Subring.{u2} R _inst_1) (SetLike.instMembership.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1)) x S)) α (Subring.instSMulSubtypeMemSubringInstMembershipInstSetLikeSubring.{u2, u1} R _inst_1 α _inst_4 S)) g m) (HSMul.hSMul.{u2, u1, u1} R α α (instHSMul.{u2, u1} R α _inst_4) (Subtype.val.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Set.{u2} R) (Set.instMembershipSet.{u2} R) x (SetLike.coe.{u2, u2} (Subring.{u2} R _inst_1) R (Subring.instSetLikeSubring.{u2} R _inst_1) S)) g) m)
Case conversion may be inaccurate. Consider using '#align subring.smul_def Subring.smul_defₓ'. -/
theorem smul_def [SMul R α] {S : Subring R} (g : S) (m : α) : g • m = (g : R) • m :=
  rfl
#align subring.smul_def Subring.smul_def

/- warning: subring.smul_comm_class_left -> Subring.smulCommClass_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : SMul.{u1, u3} R β] [_inst_5 : SMul.{u2, u3} α β] [_inst_6 : SMulCommClass.{u1, u2, u3} R α β _inst_4 _inst_5] (S : Subring.{u1} R _inst_1), SMulCommClass.{u1, u2, u3} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) α β (Subring.hasSmul.{u1, u3} R _inst_1 β _inst_4 S) _inst_5
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : SMul.{u1, u3} R β] [_inst_5 : SMul.{u2, u3} α β] [_inst_6 : SMulCommClass.{u1, u2, u3} R α β _inst_4 _inst_5] (S : Subring.{u1} R _inst_1), SMulCommClass.{u1, u2, u3} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x S)) α β (Subring.instSMulSubtypeMemSubringInstMembershipInstSetLikeSubring.{u1, u3} R _inst_1 β _inst_4 S) _inst_5
Case conversion may be inaccurate. Consider using '#align subring.smul_comm_class_left Subring.smulCommClass_leftₓ'. -/
instance smulCommClass_left [SMul R β] [SMul α β] [SMulCommClass R α β] (S : Subring R) :
    SMulCommClass S α β :=
  S.toSubsemiring.smulCommClass_left
#align subring.smul_comm_class_left Subring.smulCommClass_left

/- warning: subring.smul_comm_class_right -> Subring.smulCommClass_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : SMul.{u2, u3} α β] [_inst_5 : SMul.{u1, u3} R β] [_inst_6 : SMulCommClass.{u2, u1, u3} α R β _inst_4 _inst_5] (S : Subring.{u1} R _inst_1), SMulCommClass.{u2, u1, u3} α (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) S) β _inst_4 (Subring.hasSmul.{u1, u3} R _inst_1 β _inst_5 S)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : SMul.{u2, u3} α β] [_inst_5 : SMul.{u1, u3} R β] [_inst_6 : SMulCommClass.{u2, u1, u3} α R β _inst_4 _inst_5] (S : Subring.{u1} R _inst_1), SMulCommClass.{u2, u1, u3} α (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x S)) β _inst_4 (Subring.instSMulSubtypeMemSubringInstMembershipInstSetLikeSubring.{u1, u3} R _inst_1 β _inst_5 S)
Case conversion may be inaccurate. Consider using '#align subring.smul_comm_class_right Subring.smulCommClass_rightₓ'. -/
instance smulCommClass_right [SMul α β] [SMul R β] [SMulCommClass α R β] (S : Subring R) :
    SMulCommClass α S β :=
  S.toSubsemiring.smulCommClass_right
#align subring.smul_comm_class_right Subring.smulCommClass_right

/-- Note that this provides `is_scalar_tower S R R` which is needed by `smul_mul_assoc`. -/
instance [SMul α β] [SMul R α] [SMul R β] [IsScalarTower R α β] (S : Subring R) :
    IsScalarTower S α β :=
  S.toSubsemiring.IsScalarTower

instance [SMul R α] [FaithfulSMul R α] (S : Subring R) : FaithfulSMul S α :=
  S.toSubsemiring.FaithfulSMul

/-- The action by a subring is the action by the underlying ring. -/
instance [MulAction R α] (S : Subring R) : MulAction S α :=
  S.toSubsemiring.MulAction

/-- The action by a subring is the action by the underlying ring. -/
instance [AddMonoid α] [DistribMulAction R α] (S : Subring R) : DistribMulAction S α :=
  S.toSubsemiring.DistribMulAction

/-- The action by a subring is the action by the underlying ring. -/
instance [Monoid α] [MulDistribMulAction R α] (S : Subring R) : MulDistribMulAction S α :=
  S.toSubsemiring.MulDistribMulAction

/-- The action by a subring is the action by the underlying ring. -/
instance [Zero α] [SMulWithZero R α] (S : Subring R) : SMulWithZero S α :=
  S.toSubsemiring.SMulWithZero

/-- The action by a subring is the action by the underlying ring. -/
instance [Zero α] [MulActionWithZero R α] (S : Subring R) : MulActionWithZero S α :=
  S.toSubsemiring.MulActionWithZero

/-- The action by a subring is the action by the underlying ring. -/
instance [AddCommMonoid α] [Module R α] (S : Subring R) : Module S α :=
  S.toSubsemiring.Module

/-- The action by a subsemiring is the action by the underlying ring. -/
instance [Semiring α] [MulSemiringAction R α] (S : Subring R) : MulSemiringAction S α :=
  S.toSubmonoid.MulSemiringAction

/- warning: subring.center.smul_comm_class_left -> Subring.center.smulCommClass_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], SMulCommClass.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (Subring.center.{u1} R _inst_1)) R R (Subring.hasSmul.{u1, u1} R _inst_1 R (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) (Subring.center.{u1} R _inst_1)) (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], SMulCommClass.{u1, u1, u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.center.{u1} R _inst_1))) R R (Subring.instSMulSubtypeMemSubringInstMembershipInstSetLikeSubring.{u1, u1} R _inst_1 R (SMulZeroClass.toSMul.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (SMulWithZero.toSMulZeroClass.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MulZeroClass.toSMulWithZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.center.{u1} R _inst_1)) (SMulZeroClass.toSMul.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (SMulWithZero.toSMulZeroClass.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MulZeroClass.toSMulWithZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align subring.center.smul_comm_class_left Subring.center.smulCommClass_leftₓ'. -/
/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smulCommClass_left : SMulCommClass (center R) R R :=
  Subsemiring.center.smulCommClass_left
#align subring.center.smul_comm_class_left Subring.center.smulCommClass_left

/- warning: subring.center.smul_comm_class_right -> Subring.center.smulCommClass_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], SMulCommClass.{u1, u1, u1} R (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} R _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.setLike.{u1} R _inst_1)) (Subring.center.{u1} R _inst_1)) R (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) (Subring.hasSmul.{u1, u1} R _inst_1 R (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) (Subring.center.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R], SMulCommClass.{u1, u1, u1} R (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Subring.{u1} R _inst_1) (SetLike.instMembership.{u1, u1} (Subring.{u1} R _inst_1) R (Subring.instSetLikeSubring.{u1} R _inst_1)) x (Subring.center.{u1} R _inst_1))) R (SMulZeroClass.toSMul.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (SMulWithZero.toSMulZeroClass.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MulZeroClass.toSMulWithZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.instSMulSubtypeMemSubringInstMembershipInstSetLikeSubring.{u1, u1} R _inst_1 R (SMulZeroClass.toSMul.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (SMulWithZero.toSMulZeroClass.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MulZeroClass.toSMulWithZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))) (Subring.center.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align subring.center.smul_comm_class_right Subring.center.smulCommClass_rightₓ'. -/
/-- The center of a semiring acts commutatively on that semiring. -/
instance center.smulCommClass_right : SMulCommClass R (center R) R :=
  Subsemiring.center.smulCommClass_right
#align subring.center.smul_comm_class_right Subring.center.smulCommClass_right

end Subring

end Actions

/- warning: units.pos_subgroup -> Units.posSubgroup is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_4 : LinearOrderedSemiring.{u1} R], Subgroup.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Units.group.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_4 : LinearOrderedSemiring.{u1} R], Subgroup.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Units.instGroupUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))))
Case conversion may be inaccurate. Consider using '#align units.pos_subgroup Units.posSubgroupₓ'. -/
-- while this definition is not about subrings, this is the earliest we have
-- both ordered ring structures and submonoids available
/-- The subgroup of positive units of a linear ordered semiring. -/
def Units.posSubgroup (R : Type _) [LinearOrderedSemiring R] : Subgroup Rˣ :=
  {
    (posSubmonoid R).comap
      (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := fun x => Units.inv_pos.mpr }
#align units.pos_subgroup Units.posSubgroup

/- warning: units.mem_pos_subgroup -> Units.mem_posSubgroup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_4 : LinearOrderedSemiring.{u1} R] (u : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))), Iff (Membership.Mem.{u1, u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Subgroup.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Units.group.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))))) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Units.group.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))))) (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Subgroup.setLike.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Units.group.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))))) u (Units.posSubgroup.{u1} R _inst_4)) (LT.lt.{u1} R (Preorder.toHasLt.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedCancelAddCommMonoid.toPartialOrder.{u1} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) R (Units.hasCoe.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))))))) u))
but is expected to have type
  forall {R : Type.{u1}} [_inst_4 : LinearOrderedSemiring.{u1} R] (u : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))), Iff (Membership.mem.{u1, u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Subgroup.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Units.instGroupUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))))) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Units.instGroupUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))))) (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Subgroup.instSetLikeSubgroup.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))) (Units.instGroupUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4))))))) u (Units.posSubgroup.{u1} R _inst_4)) (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R _inst_4)))) u))
Case conversion may be inaccurate. Consider using '#align units.mem_pos_subgroup Units.mem_posSubgroupₓ'. -/
@[simp]
theorem Units.mem_posSubgroup {R : Type _} [LinearOrderedSemiring R] (u : Rˣ) :
    u ∈ Units.posSubgroup R ↔ (0 : R) < u :=
  Iff.rfl
#align units.mem_pos_subgroup Units.mem_posSubgroup

