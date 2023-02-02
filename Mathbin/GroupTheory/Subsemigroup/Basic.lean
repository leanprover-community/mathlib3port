/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky

! This file was ported from Lean 3 source module group_theory.subsemigroup.basic
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Data.Set.Lattice
import Mathbin.Data.SetLike.Basic

/-!
# Subsemigroups: definition and `complete_lattice` structure

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled multiplicative and additive subsemigroups. We also define
a `complete_lattice` structure on `subsemigroup`s,
and define the closure of a set as the minimal subsemigroup that includes this set.

## Main definitions

* `subsemigroup M`: the type of bundled subsemigroup of a magma `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : set M)`.
* `add_subsemigroup M` : the type of bundled subsemigroups of an additive magma `M`.

For each of the following definitions in the `subsemigroup` namespace, there is a corresponding
definition in the `add_subsemigroup` namespace.

* `subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `subsemigroup`.
* `subsemigroup.closure` :  semigroup closure of a set, i.e.,
  the least subsemigroup that includes the set.
* `subsemigroup.gi` : `closure : set M → subsemigroup M` and coercion `coe : subsemigroup M → set M`
  form a `galois_insertion`;

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `subsemigroup M` does not actually require `semigroup M`,
instead requiring only the weaker `has_mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/


-- Only needed for notation
-- Only needed for notation
variable {M : Type _} {N : Type _}

variable {A : Type _}

section NonAssoc

variable [Mul M] {s : Set M}

variable [Add A] {t : Set A}

#print MulMemClass /-
/-- `mul_mem_class S M` says `S` is a type of subsets `s ≤ M` that are closed under `(*)` -/
class MulMemClass (S M : Type _) [Mul M] [SetLike S M] : Prop where
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
#align mul_mem_class MulMemClass
-/

export MulMemClass (mul_mem)

#print AddMemClass /-
/-- `add_mem_class S M` says `S` is a type of subsets `s ≤ M` that are closed under `(+)` -/
class AddMemClass (S M : Type _) [Add M] [SetLike S M] : Prop where
  add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s
#align add_mem_class AddMemClass
-/

export AddMemClass (add_mem)

attribute [to_additive] MulMemClass

#print Subsemigroup /-
/-- A subsemigroup of a magma `M` is a subset closed under multiplication. -/
structure Subsemigroup (M : Type _) [Mul M] where
  carrier : Set M
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
#align subsemigroup Subsemigroup
-/

#print AddSubsemigroup /-
/-- An additive subsemigroup of an additive magma `M` is a subset closed under addition. -/
structure AddSubsemigroup (M : Type _) [Add M] where
  carrier : Set M
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
#align add_subsemigroup AddSubsemigroup
-/

attribute [to_additive AddSubsemigroup] Subsemigroup

namespace Subsemigroup

@[to_additive]
instance : SetLike (Subsemigroup M) M :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p <;> cases q <;> congr ⟩

@[to_additive]
instance : MulMemClass (Subsemigroup M) M where mul_mem := Subsemigroup.mul_mem'

#print Subsemigroup.Simps.coe /-
/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection]"]
def Simps.coe (S : Subsemigroup M) : Set M :=
  S
#align subsemigroup.simps.coe Subsemigroup.Simps.coe
#align add_subsemigroup.simps.coe AddSubsemigroup.Simps.coe
-/

initialize_simps_projections Subsemigroup (carrier → coe)

initialize_simps_projections AddSubsemigroup (carrier → coe)

#print Subsemigroup.mem_carrier /-
@[simp, to_additive]
theorem mem_carrier {s : Subsemigroup M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align subsemigroup.mem_carrier Subsemigroup.mem_carrier
#align add_subsemigroup.mem_carrier AddSubsemigroup.mem_carrier
-/

#print Subsemigroup.mem_mk /-
@[simp, to_additive]
theorem mem_mk {s : Set M} {x : M} (h_mul) : x ∈ mk s h_mul ↔ x ∈ s :=
  Iff.rfl
#align subsemigroup.mem_mk Subsemigroup.mem_mk
#align add_subsemigroup.mem_mk AddSubsemigroup.mem_mk
-/

#print Subsemigroup.coe_set_mk /-
@[simp, to_additive]
theorem coe_set_mk {s : Set M} (h_mul) : (mk s h_mul : Set M) = s :=
  rfl
#align subsemigroup.coe_set_mk Subsemigroup.coe_set_mk
#align add_subsemigroup.coe_set_mk AddSubsemigroup.coe_set_mk
-/

/- warning: subsemigroup.mk_le_mk -> Subsemigroup.mk_le_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {s : Set.{u1} M} {t : Set.{u1} M} (h_mul : forall {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a s) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b s) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) a b) s)) (h_mul' : forall {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a t) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b t) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) a b) t)), Iff (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Subsemigroup.mk.{u1} M _inst_1 s h_mul) (Subsemigroup.mk.{u1} M _inst_1 t h_mul')) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s t)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {s : Set.{u1} M} {t : Set.{u1} M} (h_mul : forall {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a s) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b s) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) a b) s)) (h_mul' : forall {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a t) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b t) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) a b) t)), Iff (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.instPartialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)))) (Subsemigroup.mk.{u1} M _inst_1 s h_mul) (Subsemigroup.mk.{u1} M _inst_1 t h_mul')) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s t)
Case conversion may be inaccurate. Consider using '#align subsemigroup.mk_le_mk Subsemigroup.mk_le_mkₓ'. -/
@[simp, to_additive]
theorem mk_le_mk {s t : Set M} (h_mul) (h_mul') : mk s h_mul ≤ mk t h_mul' ↔ s ⊆ t :=
  Iff.rfl
#align subsemigroup.mk_le_mk Subsemigroup.mk_le_mk
#align add_subsemigroup.mk_le_mk AddSubsemigroup.mk_le_mk

#print Subsemigroup.ext /-
/-- Two subsemigroups are equal if they have the same elements. -/
@[ext, to_additive "Two `add_subsemigroup`s are equal if they have the same elements."]
theorem ext {S T : Subsemigroup M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align subsemigroup.ext Subsemigroup.ext
#align add_subsemigroup.ext AddSubsemigroup.ext
-/

#print Subsemigroup.copy /-
/-- Copy a subsemigroup replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive subsemigroup replacing `carrier` with a set that is equal to\nit."]
protected def copy (S : Subsemigroup M) (s : Set M) (hs : s = S) : Subsemigroup M
    where
  carrier := s
  mul_mem' _ _ := hs.symm ▸ S.mul_mem'
#align subsemigroup.copy Subsemigroup.copy
#align add_subsemigroup.copy AddSubsemigroup.copy
-/

variable {S : Subsemigroup M}

#print Subsemigroup.coe_copy /-
@[simp, to_additive]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
#align subsemigroup.coe_copy Subsemigroup.coe_copy
#align add_subsemigroup.coe_copy AddSubsemigroup.coe_copy
-/

#print Subsemigroup.copy_eq /-
@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align subsemigroup.copy_eq Subsemigroup.copy_eq
#align add_subsemigroup.copy_eq AddSubsemigroup.copy_eq
-/

variable (S)

#print Subsemigroup.mul_mem /-
/-- A subsemigroup is closed under multiplication. -/
@[to_additive "An `add_subsemigroup` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  Subsemigroup.mul_mem' S
#align subsemigroup.mul_mem Subsemigroup.mul_mem
#align add_subsemigroup.add_mem AddSubsemigroup.add_mem
-/

/-- The subsemigroup `M` of the magma `M`. -/
@[to_additive "The additive subsemigroup `M` of the magma `M`."]
instance : Top (Subsemigroup M) :=
  ⟨{  carrier := Set.univ
      mul_mem' := fun _ _ _ _ => Set.mem_univ _ }⟩

/-- The trivial subsemigroup `∅` of a magma `M`. -/
@[to_additive "The trivial `add_subsemigroup` `∅` of an additive magma `M`."]
instance : Bot (Subsemigroup M) :=
  ⟨{  carrier := ∅
      mul_mem' := fun a b => by simp }⟩

@[to_additive]
instance : Inhabited (Subsemigroup M) :=
  ⟨⊥⟩

#print Subsemigroup.not_mem_bot /-
@[to_additive]
theorem not_mem_bot {x : M} : x ∉ (⊥ : Subsemigroup M) :=
  Set.not_mem_empty x
#align subsemigroup.not_mem_bot Subsemigroup.not_mem_bot
#align add_subsemigroup.not_mem_bot AddSubsemigroup.not_mem_bot
-/

#print Subsemigroup.mem_top /-
@[simp, to_additive]
theorem mem_top (x : M) : x ∈ (⊤ : Subsemigroup M) :=
  Set.mem_univ x
#align subsemigroup.mem_top Subsemigroup.mem_top
#align add_subsemigroup.mem_top AddSubsemigroup.mem_top
-/

#print Subsemigroup.coe_top /-
@[simp, to_additive]
theorem coe_top : ((⊤ : Subsemigroup M) : Set M) = Set.univ :=
  rfl
#align subsemigroup.coe_top Subsemigroup.coe_top
#align add_subsemigroup.coe_top AddSubsemigroup.coe_top
-/

#print Subsemigroup.coe_bot /-
@[simp, to_additive]
theorem coe_bot : ((⊥ : Subsemigroup M) : Set M) = ∅ :=
  rfl
#align subsemigroup.coe_bot Subsemigroup.coe_bot
#align add_subsemigroup.coe_bot AddSubsemigroup.coe_bot
-/

/-- The inf of two subsemigroups is their intersection. -/
@[to_additive "The inf of two `add_subsemigroup`s is their intersection."]
instance : HasInf (Subsemigroup M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      mul_mem' := fun _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

/- warning: subsemigroup.coe_inf -> Subsemigroup.coe_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (p : Subsemigroup.{u1} M _inst_1) (p' : Subsemigroup.{u1} M _inst_1), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) p p')) (Inter.inter.{u1} (Set.{u1} M) (Set.hasInter.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) p) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) p'))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (p : Subsemigroup.{u1} M _inst_1) (p' : Subsemigroup.{u1} M _inst_1), Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instHasInfSubsemigroup.{u1} M _inst_1) p p')) (Inter.inter.{u1} (Set.{u1} M) (Set.instInterSet.{u1} M) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) p) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) p'))
Case conversion may be inaccurate. Consider using '#align subsemigroup.coe_inf Subsemigroup.coe_infₓ'. -/
@[simp, to_additive]
theorem coe_inf (p p' : Subsemigroup M) : ((p ⊓ p' : Subsemigroup M) : Set M) = p ∩ p' :=
  rfl
#align subsemigroup.coe_inf Subsemigroup.coe_inf
#align add_subsemigroup.coe_inf AddSubsemigroup.coe_inf

/- warning: subsemigroup.mem_inf -> Subsemigroup.mem_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {p : Subsemigroup.{u1} M _inst_1} {p' : Subsemigroup.{u1} M _inst_1} {x : M}, Iff (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) p p')) (And (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x p) (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x p'))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {p : Subsemigroup.{u1} M _inst_1} {p' : Subsemigroup.{u1} M _inst_1} {x : M}, Iff (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instHasInfSubsemigroup.{u1} M _inst_1) p p')) (And (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x p) (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x p'))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_inf Subsemigroup.mem_infₓ'. -/
@[simp, to_additive]
theorem mem_inf {p p' : Subsemigroup M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align subsemigroup.mem_inf Subsemigroup.mem_inf
#align add_subsemigroup.mem_inf AddSubsemigroup.mem_inf

@[to_additive]
instance : InfSet (Subsemigroup M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      mul_mem' := fun x y hx hy =>
        Set.mem_binterᵢ fun i h =>
          i.mul_mem (by apply Set.mem_interᵢ₂.1 hx i h) (by apply Set.mem_interᵢ₂.1 hy i h) }⟩

/- warning: subsemigroup.coe_Inf -> Subsemigroup.coe_infₛ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Subsemigroup.{u1} M _inst_1)), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (InfSet.infₛ.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) S)) (Set.interᵢ.{u1, succ u1} M (Subsemigroup.{u1} M _inst_1) (fun (s : Subsemigroup.{u1} M _inst_1) => Set.interᵢ.{u1, 0} M (Membership.Mem.{u1, u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} (Subsemigroup.{u1} M _inst_1)) (Set.hasMem.{u1} (Subsemigroup.{u1} M _inst_1)) s S) (fun (H : Membership.Mem.{u1, u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} (Subsemigroup.{u1} M _inst_1)) (Set.hasMem.{u1} (Subsemigroup.{u1} M _inst_1)) s S) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) s)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Subsemigroup.{u1} M _inst_1)), Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) (InfSet.infₛ.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instInfSetSubsemigroup.{u1} M _inst_1) S)) (Set.interᵢ.{u1, succ u1} M (Subsemigroup.{u1} M _inst_1) (fun (s : Subsemigroup.{u1} M _inst_1) => Set.interᵢ.{u1, 0} M (Membership.mem.{u1, u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} (Subsemigroup.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Subsemigroup.{u1} M _inst_1)) s S) (fun (H : Membership.mem.{u1, u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} (Subsemigroup.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Subsemigroup.{u1} M _inst_1)) s S) => SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.coe_Inf Subsemigroup.coe_infₛₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_infₛ (S : Set (Subsemigroup M)) : ((infₛ S : Subsemigroup M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl
#align subsemigroup.coe_Inf Subsemigroup.coe_infₛ
#align add_subsemigroup.coe_Inf AddSubsemigroup.coe_infₛ

/- warning: subsemigroup.mem_Inf -> Subsemigroup.mem_infₛ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {S : Set.{u1} (Subsemigroup.{u1} M _inst_1)} {x : M}, Iff (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x (InfSet.infₛ.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) S)) (forall (p : Subsemigroup.{u1} M _inst_1), (Membership.Mem.{u1, u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} (Subsemigroup.{u1} M _inst_1)) (Set.hasMem.{u1} (Subsemigroup.{u1} M _inst_1)) p S) -> (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x p))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {S : Set.{u1} (Subsemigroup.{u1} M _inst_1)} {x : M}, Iff (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x (InfSet.infₛ.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instInfSetSubsemigroup.{u1} M _inst_1) S)) (forall (p : Subsemigroup.{u1} M _inst_1), (Membership.mem.{u1, u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} (Subsemigroup.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Subsemigroup.{u1} M _inst_1)) p S) -> (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x p))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_Inf Subsemigroup.mem_infₛₓ'. -/
@[to_additive]
theorem mem_infₛ {S : Set (Subsemigroup M)} {x : M} : x ∈ infₛ S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_interᵢ₂
#align subsemigroup.mem_Inf Subsemigroup.mem_infₛ
#align add_subsemigroup.mem_Inf AddSubsemigroup.mem_infₛ

/- warning: subsemigroup.mem_infi -> Subsemigroup.mem_infᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} {S : ι -> (Subsemigroup.{u1} M _inst_1)} {x : M}, Iff (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x (infᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) ι (fun (i : ι) => S i))) (forall (i : ι), Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x (S i))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} {S : ι -> (Subsemigroup.{u1} M _inst_1)} {x : M}, Iff (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x (infᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instInfSetSubsemigroup.{u1} M _inst_1) ι (fun (i : ι) => S i))) (forall (i : ι), Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x (S i))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_infi Subsemigroup.mem_infᵢₓ'. -/
@[to_additive]
theorem mem_infᵢ {ι : Sort _} {S : ι → Subsemigroup M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [infᵢ, mem_Inf, Set.forall_range_iff]
#align subsemigroup.mem_infi Subsemigroup.mem_infᵢ
#align add_subsemigroup.mem_infi AddSubsemigroup.mem_infᵢ

/- warning: subsemigroup.coe_infi -> Subsemigroup.coe_infᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} {S : ι -> (Subsemigroup.{u1} M _inst_1)}, Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (infᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) ι (fun (i : ι) => S i))) (Set.interᵢ.{u1, u2} M ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (S i)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} {S : ι -> (Subsemigroup.{u1} M _inst_1)}, Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) (infᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instInfSetSubsemigroup.{u1} M _inst_1) ι (fun (i : ι) => S i))) (Set.interᵢ.{u1, u2} M ι (fun (i : ι) => SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) (S i)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.coe_infi Subsemigroup.coe_infᵢₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_infᵢ {ι : Sort _} {S : ι → Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [infᵢ, coe_Inf, Set.binterᵢ_range]
#align subsemigroup.coe_infi Subsemigroup.coe_infᵢ
#align add_subsemigroup.coe_infi AddSubsemigroup.coe_infᵢ

/-- subsemigroups of a monoid form a complete lattice. -/
@[to_additive "The `add_subsemigroup`s of an `add_monoid` form a complete lattice."]
instance : CompleteLattice (Subsemigroup M) :=
  {
    completeLatticeOfInf (Subsemigroup M) fun s =>
      IsGLB.of_image (fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe)
        isGLB_binfᵢ with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S x hx => (not_mem_bot hx).elim
    top := ⊤
    le_top := fun S x hx => mem_top x
    inf := (· ⊓ ·)
    infₛ := InfSet.infₛ
    le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun a b x => And.left
    inf_le_right := fun a b x => And.right }

#print Subsemigroup.subsingleton_of_subsingleton /-
@[simp, to_additive]
theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M :=
  by
  constructor <;> intro x y
  have : ∀ a : M, a ∈ (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) not_mem_bot
#align subsemigroup.subsingleton_of_subsingleton Subsemigroup.subsingleton_of_subsingleton
#align add_subsemigroup.subsingleton_of_subsingleton AddSubsemigroup.subsingleton_of_subsingleton
-/

@[to_additive]
instance [hn : Nonempty M] : Nontrivial (Subsemigroup M) :=
  ⟨⟨⊥, ⊤, fun h => by
      obtain ⟨x⟩ := id hn
      refine' absurd (_ : x ∈ ⊥) not_mem_bot
      simp [h]⟩⟩

#print Subsemigroup.closure /-
/-- The `subsemigroup` generated by a set. -/
@[to_additive "The `add_subsemigroup` generated by a set"]
def closure (s : Set M) : Subsemigroup M :=
  infₛ { S | s ⊆ S }
#align subsemigroup.closure Subsemigroup.closure
#align add_subsemigroup.closure AddSubsemigroup.closure
-/

#print Subsemigroup.mem_closure /-
@[to_additive]
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Subsemigroup M, s ⊆ S → x ∈ S :=
  mem_infₛ
#align subsemigroup.mem_closure Subsemigroup.mem_closure
#align add_subsemigroup.mem_closure AddSubsemigroup.mem_closure
-/

#print Subsemigroup.subset_closure /-
/-- The subsemigroup generated by a set includes the set. -/
@[simp, to_additive "The `add_subsemigroup` generated by a set includes the set."]
theorem subset_closure : s ⊆ closure s := fun x hx => mem_closure.2 fun S hS => hS hx
#align subsemigroup.subset_closure Subsemigroup.subset_closure
#align add_subsemigroup.subset_closure AddSubsemigroup.subset_closure
-/

#print Subsemigroup.not_mem_of_not_mem_closure /-
@[to_additive]
theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align subsemigroup.not_mem_of_not_mem_closure Subsemigroup.not_mem_of_not_mem_closure
#align add_subsemigroup.not_mem_of_not_mem_closure AddSubsemigroup.not_mem_of_not_mem_closure
-/

variable {S}

open Set

/- warning: subsemigroup.closure_le -> Subsemigroup.closure_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {s : Set.{u1} M} {S : Subsemigroup.{u1} M _inst_1}, Iff (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Subsemigroup.closure.{u1} M _inst_1 s) S) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {s : Set.{u1} M} {S : Subsemigroup.{u1} M _inst_1}, Iff (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) (Subsemigroup.closure.{u1} M _inst_1 s) S) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.closure_le Subsemigroup.closure_leₓ'. -/
/-- A subsemigroup `S` includes `closure s` if and only if it includes `s`. -/
@[simp,
  to_additive "An additive subsemigroup `S` includes `closure s`\nif and only if it includes `s`"]
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => infₛ_le h⟩
#align subsemigroup.closure_le Subsemigroup.closure_le
#align add_subsemigroup.closure_le AddSubsemigroup.closure_le

/- warning: subsemigroup.closure_mono -> Subsemigroup.closure_mono is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {{s : Set.{u1} M}} {{t : Set.{u1} M}}, (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s t) -> (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Subsemigroup.closure.{u1} M _inst_1 s) (Subsemigroup.closure.{u1} M _inst_1 t))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {{s : Set.{u1} M}} {{t : Set.{u1} M}}, (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s t) -> (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) (Subsemigroup.closure.{u1} M _inst_1 s) (Subsemigroup.closure.{u1} M _inst_1 t))
Case conversion may be inaccurate. Consider using '#align subsemigroup.closure_mono Subsemigroup.closure_monoₓ'. -/
/-- subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive
      "Additive subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,\nthen `closure s ≤ closure t`"]
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure
#align subsemigroup.closure_mono Subsemigroup.closure_mono
#align add_subsemigroup.closure_mono AddSubsemigroup.closure_mono

/- warning: subsemigroup.closure_eq_of_le -> Subsemigroup.closure_eq_of_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {s : Set.{u1} M} {S : Subsemigroup.{u1} M _inst_1}, (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S)) -> (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S (Subsemigroup.closure.{u1} M _inst_1 s)) -> (Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.closure.{u1} M _inst_1 s) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {s : Set.{u1} M} {S : Subsemigroup.{u1} M _inst_1}, (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) S)) -> (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) S (Subsemigroup.closure.{u1} M _inst_1 s)) -> (Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.closure.{u1} M _inst_1 s) S)
Case conversion may be inaccurate. Consider using '#align subsemigroup.closure_eq_of_le Subsemigroup.closure_eq_of_leₓ'. -/
@[to_additive]
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂
#align subsemigroup.closure_eq_of_le Subsemigroup.closure_eq_of_le
#align add_subsemigroup.closure_eq_of_le AddSubsemigroup.closure_eq_of_le

variable (S)

#print Subsemigroup.closure_induction /-
/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim,
  to_additive
      "An induction principle for additive closure membership. If `p`\nholds for all elements of `s`, and is preserved under addition, then `p` holds for all\nelements of the additive closure of `s`."]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, Hmul⟩).2 Hs h
#align subsemigroup.closure_induction Subsemigroup.closure_induction
#align add_subsemigroup.closure_induction AddSubsemigroup.closure_induction
-/

#print Subsemigroup.closure_induction' /-
/-- A dependent version of `subsemigroup.closure_induction`.  -/
@[elab_as_elim, to_additive "A dependent version of `add_subsemigroup.closure_induction`. "]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx := by
  refine' Exists.elim _ fun (hx : x ∈ closure s) (hc : p x hx) => hc
  exact
    closure_induction hx (fun x hx => ⟨_, Hs x hx⟩) fun x y ⟨hx', hx⟩ ⟨hy', hy⟩ =>
      ⟨_, Hmul _ _ _ _ hx hy⟩
#align subsemigroup.closure_induction' Subsemigroup.closure_induction'
#align add_subsemigroup.closure_induction' AddSubsemigroup.closure_induction'
-/

#print Subsemigroup.closure_induction₂ /-
/-- An induction principle for closure membership for predicates with two arguments.  -/
@[elab_as_elim,
  to_additive
      "An induction principle for additive closure membership for\npredicates with two arguments."]
theorem closure_induction₂ {p : M → M → Prop} {x} {y : M} (hx : x ∈ closure s) (hy : y ∈ closure s)
    (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (Hmul_left : ∀ x y z, p x z → p y z → p (x * y) z)
    (Hmul_right : ∀ x y z, p z x → p z y → p z (x * y)) : p x y :=
  closure_induction hx
    (fun x xs => closure_induction hy (Hs x xs) fun z y h₁ h₂ => Hmul_right z _ _ h₁ h₂)
    fun x z h₁ h₂ => Hmul_left _ _ _ h₁ h₂
#align subsemigroup.closure_induction₂ Subsemigroup.closure_induction₂
#align add_subsemigroup.closure_induction₂ AddSubsemigroup.closure_induction₂
-/

#print Subsemigroup.dense_induction /-
/-- If `s` is a dense set in a magma `M`, `subsemigroup.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[elab_as_elim,
  to_additive
      "If `s` is a dense set in an additive monoid `M`,\n`add_subsemigroup.closure s = ⊤`, then in order to prove that some predicate `p` holds\nfor all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify that `p x` and `p y` imply\n`p (x + y)`."]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure s = ⊤) (Hs : ∀ x ∈ s, p x)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  by
  have : ∀ x ∈ closure s, p x := fun x hx => closure_induction hx Hs Hmul
  simpa [hs] using this x
#align subsemigroup.dense_induction Subsemigroup.dense_induction
#align add_subsemigroup.dense_induction AddSubsemigroup.dense_induction
-/

variable (M)

/- warning: subsemigroup.gi -> Subsemigroup.gi is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Mul.{u1} M], GaloisInsertion.{u1, u1} (Set.{u1} M) (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} M) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} M) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} M) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} M) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} M) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} M) (Set.completeBooleanAlgebra.{u1} M))))))) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))) (Subsemigroup.closure.{u1} M _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Mul.{u1} M], GaloisInsertion.{u1, u1} (Set.{u1} M) (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} M) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} M) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} M) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} M) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} M) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} M) (Set.instCompleteBooleanAlgebraSet.{u1} M))))))) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)))) (Subsemigroup.closure.{u1} M _inst_1) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align subsemigroup.gi Subsemigroup.giₓ'. -/
/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : GaloisInsertion (@closure M _) coe
    where
  choice s _ := closure s
  gc s t := closure_le
  le_l_u s := subset_closure
  choice_eq s h := rfl
#align subsemigroup.gi Subsemigroup.gi
#align add_subsemigroup.gi AddSubsemigroup.gi

variable {M}

#print Subsemigroup.closure_eq /-
/-- Closure of a subsemigroup `S` equals `S`. -/
@[simp, to_additive "Additive closure of an additive subsemigroup `S` equals `S`"]
theorem closure_eq : closure (S : Set M) = S :=
  (Subsemigroup.gi M).l_u_eq S
#align subsemigroup.closure_eq Subsemigroup.closure_eq
#align add_subsemigroup.closure_eq AddSubsemigroup.closure_eq
-/

#print Subsemigroup.closure_empty /-
@[simp, to_additive]
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Subsemigroup.gi M).gc.l_bot
#align subsemigroup.closure_empty Subsemigroup.closure_empty
#align add_subsemigroup.closure_empty AddSubsemigroup.closure_empty
-/

#print Subsemigroup.closure_univ /-
@[simp, to_additive]
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤
#align subsemigroup.closure_univ Subsemigroup.closure_univ
#align add_subsemigroup.closure_univ AddSubsemigroup.closure_univ
-/

/- warning: subsemigroup.closure_union -> Subsemigroup.closure_union is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (s : Set.{u1} M) (t : Set.{u1} M), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.closure.{u1} M _inst_1 (Union.union.{u1} (Set.{u1} M) (Set.hasUnion.{u1} M) s t)) (HasSup.sup.{u1} (Subsemigroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1)))) (Subsemigroup.closure.{u1} M _inst_1 s) (Subsemigroup.closure.{u1} M _inst_1 t))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (s : Set.{u1} M) (t : Set.{u1} M), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.closure.{u1} M _inst_1 (Union.union.{u1} (Set.{u1} M) (Set.instUnionSet.{u1} M) s t)) (HasSup.sup.{u1} (Subsemigroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)))) (Subsemigroup.closure.{u1} M _inst_1 s) (Subsemigroup.closure.{u1} M _inst_1 t))
Case conversion may be inaccurate. Consider using '#align subsemigroup.closure_union Subsemigroup.closure_unionₓ'. -/
@[to_additive]
theorem closure_union (s t : Set M) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subsemigroup.gi M).gc.l_sup
#align subsemigroup.closure_union Subsemigroup.closure_union
#align add_subsemigroup.closure_union AddSubsemigroup.closure_union

/- warning: subsemigroup.closure_Union -> Subsemigroup.closure_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} (s : ι -> (Set.{u1} M)), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.closure.{u1} M _inst_1 (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => s i))) (supᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => Subsemigroup.closure.{u1} M _inst_1 (s i)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} (s : ι -> (Set.{u1} M)), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.closure.{u1} M _inst_1 (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => s i))) (supᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)) ι (fun (i : ι) => Subsemigroup.closure.{u1} M _inst_1 (s i)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.closure_Union Subsemigroup.closure_unionᵢₓ'. -/
@[to_additive]
theorem closure_unionᵢ {ι} (s : ι → Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemigroup.gi M).gc.l_supᵢ
#align subsemigroup.closure_Union Subsemigroup.closure_unionᵢ
#align add_subsemigroup.closure_Union AddSubsemigroup.closure_unionᵢ

/- warning: subsemigroup.closure_singleton_le_iff_mem -> Subsemigroup.closure_singleton_le_iff_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (m : M) (p : Subsemigroup.{u1} M _inst_1), Iff (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Subsemigroup.closure.{u1} M _inst_1 (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) m)) p) (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) m p)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (m : M) (p : Subsemigroup.{u1} M _inst_1), Iff (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) (Subsemigroup.closure.{u1} M _inst_1 (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) m)) p) (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) m p)
Case conversion may be inaccurate. Consider using '#align subsemigroup.closure_singleton_le_iff_mem Subsemigroup.closure_singleton_le_iff_memₓ'. -/
@[simp, to_additive]
theorem closure_singleton_le_iff_mem (m : M) (p : Subsemigroup M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]
#align subsemigroup.closure_singleton_le_iff_mem Subsemigroup.closure_singleton_le_iff_mem
#align add_subsemigroup.closure_singleton_le_iff_mem AddSubsemigroup.closure_singleton_le_iff_mem

/- warning: subsemigroup.mem_supr -> Subsemigroup.mem_supᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} (p : ι -> (Subsemigroup.{u1} M _inst_1)) {m : M}, Iff (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) m (supᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => p i))) (forall (N : Subsemigroup.{u1} M _inst_1), (forall (i : ι), LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (p i) N) -> (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) m N))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} (p : ι -> (Subsemigroup.{u1} M _inst_1)) {m : M}, Iff (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) m (supᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)) ι (fun (i : ι) => p i))) (forall (N : Subsemigroup.{u1} M _inst_1), (forall (i : ι), LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) (p i) N) -> (Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) m N))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_supr Subsemigroup.mem_supᵢₓ'. -/
@[to_additive]
theorem mem_supᵢ {ι : Sort _} (p : ι → Subsemigroup M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N :=
  by
  rw [← closure_singleton_le_iff_mem, le_supᵢ_iff]
  simp only [closure_singleton_le_iff_mem]
#align subsemigroup.mem_supr Subsemigroup.mem_supᵢ
#align add_subsemigroup.mem_supr AddSubsemigroup.mem_supᵢ

/- warning: subsemigroup.supr_eq_closure -> Subsemigroup.supᵢ_eq_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} (p : ι -> (Subsemigroup.{u1} M _inst_1)), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (supᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => p i)) (Subsemigroup.closure.{u1} M _inst_1 (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (p i))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {ι : Sort.{u2}} (p : ι -> (Subsemigroup.{u1} M _inst_1)), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (supᵢ.{u1, u2} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)) ι (fun (i : ι) => p i)) (Subsemigroup.closure.{u1} M _inst_1 (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => SetLike.coe.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) (p i))))
Case conversion may be inaccurate. Consider using '#align subsemigroup.supr_eq_closure Subsemigroup.supᵢ_eq_closureₓ'. -/
@[to_additive]
theorem supᵢ_eq_closure {ι : Sort _} (p : ι → Subsemigroup M) :
    (⨆ i, p i) = Subsemigroup.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Subsemigroup.closure_unionᵢ, Subsemigroup.closure_eq]
#align subsemigroup.supr_eq_closure Subsemigroup.supᵢ_eq_closure
#align add_subsemigroup.supr_eq_closure AddSubsemigroup.supᵢ_eq_closure

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

#print MulHom.eqLocus /-
/-- The subsemigroup of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive subsemigroup of elements `x : M` such that `f x = g x`"]
def eqLocus (f g : M →ₙ* N) : Subsemigroup M
    where
  carrier := { x | f x = g x }
  mul_mem' x y (hx : _ = _) (hy : _ = _) := by simp [*]
#align mul_hom.eq_mlocus MulHom.eqLocus
#align add_hom.eq_mlocus AddHom.eqLocus
-/

/- warning: mul_hom.eq_on_mclosure -> MulHom.eqOn_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_3 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_3} {g : MulHom.{u1, u2} M N _inst_1 _inst_3} {s : Set.{u1} M}, (Set.EqOn.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) g) s) -> (Set.EqOn.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) g) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Subsemigroup.closure.{u1} M _inst_1 s)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_3 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_3} {g : MulHom.{u2, u1} M N _inst_1 _inst_3} {s : Set.{u2} M}, (Set.EqOn.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_3)) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_3)) g) s) -> (Set.EqOn.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_3)) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_3)) g) (SetLike.coe.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.closure.{u2} M _inst_1 s)))
Case conversion may be inaccurate. Consider using '#align mul_hom.eq_on_mclosure MulHom.eqOn_closureₓ'. -/
/-- If two mul homomorphisms are equal on a set, then they are equal on its subsemigroup closure. -/
@[to_additive
      "If two add homomorphisms are equal on a set,\nthen they are equal on its additive subsemigroup closure."]
theorem eqOn_closure {f g : M →ₙ* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h
#align mul_hom.eq_on_mclosure MulHom.eqOn_closure
#align add_hom.eq_on_mclosure AddHom.eqOn_closure

/- warning: mul_hom.eq_of_eq_on_mtop -> MulHom.eq_of_eqOn_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_3 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_3} {g : MulHom.{u1, u2} M N _inst_1 _inst_3}, (Set.EqOn.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) g) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Top.top.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasTop.{u1} M _inst_1)))) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_3) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_3 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_3} {g : MulHom.{u2, u1} M N _inst_1 _inst_3}, (Set.EqOn.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_3)) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_3)) g) (SetLike.coe.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Top.top.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instTopSubsemigroup.{u2} M _inst_1)))) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_3) f g)
Case conversion may be inaccurate. Consider using '#align mul_hom.eq_of_eq_on_mtop MulHom.eq_of_eqOn_topₓ'. -/
@[to_additive]
theorem eq_of_eqOn_top {f g : M →ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M)) : f = g :=
  ext fun x => h trivial
#align mul_hom.eq_of_eq_on_mtop MulHom.eq_of_eqOn_top
#align add_hom.eq_of_eq_on_mtop AddHom.eq_of_eqOn_top

/- warning: mul_hom.eq_of_eq_on_mdense -> MulHom.eq_of_eqOn_dense is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_3 : Mul.{u2} N] {s : Set.{u1} M}, (Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.closure.{u1} M _inst_1 s) (Top.top.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasTop.{u1} M _inst_1))) -> (forall {f : MulHom.{u1, u2} M N _inst_1 _inst_3} {g : MulHom.{u1, u2} M N _inst_1 _inst_3}, (Set.EqOn.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) g) s) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_3) f g))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_3 : Mul.{u1} N] {s : Set.{u2} M}, (Eq.{succ u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.closure.{u2} M _inst_1 s) (Top.top.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instTopSubsemigroup.{u2} M _inst_1))) -> (forall {f : MulHom.{u2, u1} M N _inst_1 _inst_3} {g : MulHom.{u2, u1} M N _inst_1 _inst_3}, (Set.EqOn.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_3)) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_3)) g) s) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_3) f g))
Case conversion may be inaccurate. Consider using '#align mul_hom.eq_of_eq_on_mdense MulHom.eq_of_eqOn_denseₓ'. -/
@[to_additive]
theorem eq_of_eqOn_dense {s : Set M} (hs : closure s = ⊤) {f g : M →ₙ* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h
#align mul_hom.eq_of_eq_on_mdense MulHom.eq_of_eqOn_dense
#align add_hom.eq_of_eq_on_mdense AddHom.eq_of_eqOn_dense

end MulHom

end NonAssoc

section Assoc

namespace MulHom

open Subsemigroup

/- warning: mul_hom.of_mdense -> MulHom.ofDense is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Semigroup.{u1} M] [_inst_2 : Semigroup.{u2} N] {s : Set.{u1} M} (f : M -> N), (Eq.{succ u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Subsemigroup.closure.{u1} M (Semigroup.toHasMul.{u1} M _inst_1) s) (Top.top.{u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Subsemigroup.hasTop.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)))) -> (forall (x : M) (y : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s) -> (Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (Semigroup.toHasMul.{u2} N _inst_2)) (f x) (f y)))) -> (MulHom.{u1, u2} M N (Semigroup.toHasMul.{u1} M _inst_1) (Semigroup.toHasMul.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Semigroup.{u1} M] [_inst_2 : Semigroup.{u2} N] {s : Set.{u1} M} (f : M -> N), (Eq.{succ u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (Subsemigroup.closure.{u1} M (Semigroup.toMul.{u1} M _inst_1) s) (Top.top.{u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)) (Subsemigroup.instTopSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_1)))) -> (forall (x : M) (y : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s) -> (Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toMul.{u1} M _inst_1)) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (Semigroup.toMul.{u2} N _inst_2)) (f x) (f y)))) -> (MulHom.{u1, u2} M N (Semigroup.toMul.{u1} M _inst_1) (Semigroup.toMul.{u2} N _inst_2))
Case conversion may be inaccurate. Consider using '#align mul_hom.of_mdense MulHom.ofDenseₓ'. -/
/-- Let `s` be a subset of a semigroup `M` such that the closure of `s` is the whole semigroup.
Then `mul_hom.of_mdense` defines a mul homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive]
def ofDense {M N} [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) : M →ₙ* N
    where
  toFun := f
  map_mul' x y :=
    dense_induction y hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) x
#align mul_hom.of_mdense MulHom.ofDense
#align add_hom.of_mdense AddHom.ofDense

/-- Let `s` be a subset of an additive semigroup `M` such that the closure of `s` is the whole
semigroup.  Then `add_hom.of_mdense` defines an additive homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc AddHom.ofDense

/- warning: mul_hom.coe_of_mdense -> MulHom.coe_ofDense is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Semigroup.{u1} M] [_inst_2 : Semigroup.{u2} N] {s : Set.{u1} M} (f : M -> N) (hs : Eq.{succ u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Subsemigroup.closure.{u1} M (Semigroup.toHasMul.{u1} M _inst_1) s) (Top.top.{u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) (Subsemigroup.hasTop.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)))) (hmul : forall (x : M) (y : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s) -> (Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (Semigroup.toHasMul.{u1} M _inst_1)) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (Semigroup.toHasMul.{u2} N _inst_2)) (f x) (f y)))), Eq.{max (succ u1) (succ u2)} ((fun (_x : MulHom.{u1, u2} M N (Semigroup.toHasMul.{u1} M _inst_1) (Semigroup.toHasMul.{u2} N _inst_2)) => M -> N) (MulHom.ofDense.{u1, u2} M N _inst_1 _inst_2 s f hs hmul)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N (Semigroup.toHasMul.{u1} M _inst_1) (Semigroup.toHasMul.{u2} N _inst_2)) (fun (_x : MulHom.{u1, u2} M N (Semigroup.toHasMul.{u1} M _inst_1) (Semigroup.toHasMul.{u2} N _inst_2)) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N (Semigroup.toHasMul.{u1} M _inst_1) (Semigroup.toHasMul.{u2} N _inst_2)) (MulHom.ofDense.{u1, u2} M N _inst_1 _inst_2 s f hs hmul)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Semigroup.{u2} M] [_inst_2 : Semigroup.{u1} N] {s : Set.{u2} M} (f : M -> N) (hs : Eq.{succ u2} (Subsemigroup.{u2} M (Semigroup.toMul.{u2} M _inst_1)) (Subsemigroup.closure.{u2} M (Semigroup.toMul.{u2} M _inst_1) s) (Top.top.{u2} (Subsemigroup.{u2} M (Semigroup.toMul.{u2} M _inst_1)) (Subsemigroup.instTopSubsemigroup.{u2} M (Semigroup.toMul.{u2} M _inst_1)))) (hmul : forall (x : M) (y : M), (Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) y s) -> (Eq.{succ u1} N (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (Semigroup.toMul.{u2} M _inst_1)) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (Semigroup.toMul.{u1} N _inst_2)) (f x) (f y)))), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N (Semigroup.toMul.{u2} M _inst_1) (Semigroup.toMul.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N (Semigroup.toMul.{u2} M _inst_1) (Semigroup.toMul.{u1} N _inst_2)) M N (Semigroup.toMul.{u2} M _inst_1) (Semigroup.toMul.{u1} N _inst_2) (MulHom.mulHomClass.{u2, u1} M N (Semigroup.toMul.{u2} M _inst_1) (Semigroup.toMul.{u1} N _inst_2))) (MulHom.ofDense.{u2, u1} M N _inst_1 _inst_2 s f hs hmul)) f
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_of_mdense MulHom.coe_ofDenseₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_ofDense [Semigroup M] [Semigroup N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (hmul) : (ofDense f hs hmul : M → N) = f :=
  rfl
#align mul_hom.coe_of_mdense MulHom.coe_ofDense
#align add_hom.coe_of_mdense AddHom.coe_ofDense

end MulHom

end Assoc

