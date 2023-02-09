/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module group_theory.group_action.basic
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.GroupTheory.GroupAction.Group
import Mathbin.Data.Setoid.Basic
import Mathbin.Data.Set.Pointwise.Smul
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Basic properties of group actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file primarily concerns itself with orbits, stabilizers, and other objects defined in terms of
actions. Despite this file being called `basic`, low-level helper lemmas for algebraic manipulation
of `•` belong elsewhere.

## Main definitions

* `mul_action.orbit`
* `mul_action.fixed_points`
* `mul_action.fixed_by`
* `mul_action.stabilizer`

-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Pointwise

open Function

namespace MulAction

variable (α) [Monoid α] [MulAction α β]

#print MulAction.orbit /-
/-- The orbit of an element under an action. -/
@[to_additive "The orbit of an element under an action."]
def orbit (b : β) :=
  Set.range fun x : α => x • b
#align mul_action.orbit MulAction.orbit
#align add_action.orbit AddAction.orbit
-/

variable {α}

#print MulAction.mem_orbit_iff /-
@[to_additive]
theorem mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
  Iff.rfl
#align mul_action.mem_orbit_iff MulAction.mem_orbit_iff
#align add_action.mem_orbit_iff AddAction.mem_orbit_iff
-/

#print MulAction.mem_orbit /-
@[simp, to_additive]
theorem mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
  ⟨x, rfl⟩
#align mul_action.mem_orbit MulAction.mem_orbit
#align add_action.mem_orbit AddAction.mem_orbit
-/

#print MulAction.mem_orbit_self /-
@[simp, to_additive]
theorem mem_orbit_self (b : β) : b ∈ orbit α b :=
  ⟨1, by simp [MulAction.one_smul]⟩
#align mul_action.mem_orbit_self MulAction.mem_orbit_self
#align add_action.mem_orbit_self AddAction.mem_orbit_self
-/

#print MulAction.orbit_nonempty /-
@[to_additive]
theorem orbit_nonempty (b : β) : Set.Nonempty (orbit α b) :=
  Set.range_nonempty _
#align mul_action.orbit_nonempty MulAction.orbit_nonempty
#align add_action.orbit_nonempty AddAction.orbit_nonempty
-/

#print MulAction.mapsTo_smul_orbit /-
@[to_additive]
theorem mapsTo_smul_orbit (a : α) (b : β) : Set.MapsTo ((· • ·) a) (orbit α b) (orbit α b) :=
  Set.range_subset_iff.2 fun a' => ⟨a * a', mul_smul _ _ _⟩
#align mul_action.maps_to_smul_orbit MulAction.mapsTo_smul_orbit
#align add_action.maps_to_vadd_orbit AddAction.mapsTo_vadd_orbit
-/

#print MulAction.smul_orbit_subset /-
@[to_additive]
theorem smul_orbit_subset (a : α) (b : β) : a • orbit α b ⊆ orbit α b :=
  (mapsTo_smul_orbit a b).image_subset
#align mul_action.smul_orbit_subset MulAction.smul_orbit_subset
#align add_action.vadd_orbit_subset AddAction.vadd_orbit_subset
-/

#print MulAction.orbit_smul_subset /-
@[to_additive]
theorem orbit_smul_subset (a : α) (b : β) : orbit α (a • b) ⊆ orbit α b :=
  Set.range_subset_iff.2 fun a' => mul_smul a' a b ▸ mem_orbit _ _
#align mul_action.orbit_smul_subset MulAction.orbit_smul_subset
#align add_action.orbit_vadd_subset AddAction.orbit_vadd_subset
-/

@[to_additive]
instance {b : β} : MulAction α (orbit α b)
    where
  smul a := (mapsTo_smul_orbit a b).restrict _ _ _
  one_smul a := Subtype.ext (one_smul α a)
  mul_smul a a' b' := Subtype.ext (mul_smul a a' b')

/- warning: mul_action.orbit.coe_smul -> MulAction.orbit.coe_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulAction.{u1, u2} α β _inst_1] {b : β} {a : α} {b' : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)}, Eq.{succ u2} β ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)))))) (SMul.smul.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) (MulAction.toHasSmul.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) _inst_1 (MulAction.orbit.mulAction.{u1, u2} α β _inst_1 _inst_2 b)) a b')) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_2) a ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)))))) b'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulAction.{u1, u2} α β _inst_1] {b : β} {a : α} {b' : Set.Elem.{u2} β (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)}, Eq.{succ u2} β (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) (HSMul.hSMul.{u1, u2, u2} α (Set.Elem.{u2} β (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) (Set.Elem.{u2} β (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) (instHSMul.{u1, u2} α (Set.Elem.{u2} β (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) (MulAction.toSMul.{u1, u2} α (Set.Elem.{u2} β (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) _inst_1 (MulAction.instMulActionElemOrbit.{u1, u2} α β _inst_1 _inst_2 b))) a b')) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_2)) a (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (MulAction.orbit.{u1, u2} α β _inst_1 _inst_2 b)) b'))
Case conversion may be inaccurate. Consider using '#align mul_action.orbit.coe_smul MulAction.orbit.coe_smulₓ'. -/
@[simp, to_additive]
theorem orbit.coe_smul {b : β} {a : α} {b' : orbit α b} : ↑(a • b') = a • (b' : β) :=
  rfl
#align mul_action.orbit.coe_smul MulAction.orbit.coe_smul
#align add_action.orbit.coe_vadd AddAction.orbit.coe_vadd

variable (α) (β)

#print MulAction.fixedPoints /-
/-- The set of elements fixed under the whole action. -/
@[to_additive "The set of elements fixed under the whole action."]
def fixedPoints : Set β :=
  { b : β | ∀ x : α, x • b = b }
#align mul_action.fixed_points MulAction.fixedPoints
#align add_action.fixed_points AddAction.fixedPoints
-/

#print MulAction.fixedBy /-
/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
@[to_additive "`fixed_by g` is the subfield of elements fixed by `g`."]
def fixedBy (g : α) : Set β :=
  { x | g • x = x }
#align mul_action.fixed_by MulAction.fixedBy
#align add_action.fixed_by AddAction.fixedBy
-/

#print MulAction.fixed_eq_interᵢ_fixedBy /-
@[to_additive]
theorem fixed_eq_interᵢ_fixedBy : fixedPoints α β = ⋂ g : α, fixedBy α β g :=
  Set.ext fun x =>
    ⟨fun hx => Set.mem_interᵢ.2 fun g => hx g, fun hx g => (Set.mem_interᵢ.1 hx g : _)⟩
#align mul_action.fixed_eq_Inter_fixed_by MulAction.fixed_eq_interᵢ_fixedBy
#align add_action.fixed_eq_Inter_fixed_by AddAction.fixed_eq_interᵢ_fixedBy
-/

variable {α} (β)

#print MulAction.mem_fixedPoints /-
@[simp, to_additive]
theorem mem_fixedPoints {b : β} : b ∈ fixedPoints α β ↔ ∀ x : α, x • b = b :=
  Iff.rfl
#align mul_action.mem_fixed_points MulAction.mem_fixedPoints
#align add_action.mem_fixed_points AddAction.mem_fixedPoints
-/

#print MulAction.mem_fixedBy /-
@[simp, to_additive]
theorem mem_fixedBy {g : α} {b : β} : b ∈ fixedBy α β g ↔ g • b = b :=
  Iff.rfl
#align mul_action.mem_fixed_by MulAction.mem_fixedBy
#align add_action.mem_fixed_by AddAction.mem_fixedBy
-/

#print MulAction.mem_fixedPoints' /-
@[to_additive]
theorem mem_fixedPoints' {b : β} : b ∈ fixedPoints α β ↔ ∀ b', b' ∈ orbit α b → b' = b :=
  ⟨fun h b h₁ =>
    let ⟨x, hx⟩ := mem_orbit_iff.1 h₁
    hx ▸ h x,
    fun h b => h _ (mem_orbit _ _)⟩
#align mul_action.mem_fixed_points' MulAction.mem_fixedPoints'
#align add_action.mem_fixed_points' AddAction.mem_fixedPoints'
-/

variable (α) {β}

#print MulAction.Stabilizer.submonoid /-
/-- The stabilizer of a point `b` as a submonoid of `α`. -/
@[to_additive "The stabilizer of a point `b` as an additive submonoid of `α`."]
def Stabilizer.submonoid (b : β) : Submonoid α
    where
  carrier := { a | a • b = b }
  one_mem' := one_smul _ b
  mul_mem' a a' (ha : a • b = b) (hb : a' • b = b) :=
    show (a * a') • b = b by rw [← smul_smul, hb, ha]
#align mul_action.stabilizer.submonoid MulAction.Stabilizer.submonoid
#align add_action.stabilizer.add_submonoid AddAction.Stabilizer.addSubmonoid
-/

/- warning: mul_action.mem_stabilizer_submonoid_iff -> MulAction.mem_stabilizer_submonoid_iff is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulAction.{u1, u2} α β _inst_1] {b : β} {a : α}, Iff (Membership.Mem.{u1, u1} α (Submonoid.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) α (Submonoid.setLike.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (MulAction.Stabilizer.submonoid.{u1, u2} α β _inst_1 _inst_2 b)) (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β _inst_1 _inst_2) a b) b)
but is expected to have type
  forall (α : Type.{u1}) {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : MulAction.{u1, u2} α β _inst_1] {b : β} {a : α}, Iff (Membership.mem.{u1, u1} α (Submonoid.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) α (Submonoid.instSetLikeSubmonoid.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (MulAction.Stabilizer.submonoid.{u1, u2} α β _inst_1 _inst_2 b)) (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β _inst_1 _inst_2)) a b) b)
Case conversion may be inaccurate. Consider using '#align mul_action.mem_stabilizer_submonoid_iff MulAction.mem_stabilizer_submonoid_iffₓ'. -/
@[simp, to_additive]
theorem mem_stabilizer_submonoid_iff {b : β} {a : α} : a ∈ Stabilizer.submonoid α b ↔ a • b = b :=
  Iff.rfl
#align mul_action.mem_stabilizer_submonoid_iff MulAction.mem_stabilizer_submonoid_iff
#align add_action.mem_stabilizer_add_submonoid_iff AddAction.mem_stabilizer_addSubmonoid_iff

#print MulAction.orbit_eq_univ /-
@[to_additive]
theorem orbit_eq_univ [IsPretransitive α β] (x : β) : orbit α x = Set.univ :=
  (surjective_smul α x).range_eq
#align mul_action.orbit_eq_univ MulAction.orbit_eq_univ
#align add_action.orbit_eq_univ AddAction.orbit_eq_univ
-/

variable {α} {β}

#print MulAction.mem_fixedPoints_iff_card_orbit_eq_one /-
@[to_additive]
theorem mem_fixedPoints_iff_card_orbit_eq_one {a : β} [Fintype (orbit α a)] :
    a ∈ fixedPoints α β ↔ Fintype.card (orbit α a) = 1 :=
  by
  rw [Fintype.card_eq_one_iff, mem_fixed_points]
  constructor
  · exact fun h => ⟨⟨a, mem_orbit_self _⟩, fun ⟨b, ⟨x, hx⟩⟩ => Subtype.eq <| by simp [h x, hx.symm]⟩
  · intro h x
    rcases h with ⟨⟨z, hz⟩, hz₁⟩
    calc
      x • a = z := Subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      _ = a := (Subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm
      
#align mul_action.mem_fixed_points_iff_card_orbit_eq_one MulAction.mem_fixedPoints_iff_card_orbit_eq_one
#align add_action.mem_fixed_points_iff_card_orbit_eq_zero AddAction.mem_fixedPoints_iff_card_orbit_eq_zero
-/

end MulAction

namespace MulAction

variable (α)

variable [Group α] [MulAction α β]

#print MulAction.stabilizer /-
/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive
      "The stabilizer of an element under an action, i.e. what sends the element to itself.\nAn additive subgroup."]
def stabilizer (b : β) : Subgroup α :=
  { Stabilizer.submonoid α b with
    inv_mem' := fun a (ha : a • b = b) => show a⁻¹ • b = b by rw [inv_smul_eq_iff, ha] }
#align mul_action.stabilizer MulAction.stabilizer
#align add_action.stabilizer AddAction.stabilizer
-/

variable {α} {β}

/- warning: mul_action.mem_stabilizer_iff -> MulAction.mem_stabilizer_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {b : β} {a : α}, Iff (Membership.Mem.{u1, u1} α (Subgroup.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} α _inst_1) α (Subgroup.setLike.{u1} α _inst_1)) a (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 b)) (Eq.{succ u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) a b) b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {b : β} {a : α}, Iff (Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_1) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_1)) a (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 b)) (Eq.{succ u2} β (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a b) b)
Case conversion may be inaccurate. Consider using '#align mul_action.mem_stabilizer_iff MulAction.mem_stabilizer_iffₓ'. -/
@[simp, to_additive]
theorem mem_stabilizer_iff {b : β} {a : α} : a ∈ stabilizer α b ↔ a • b = b :=
  Iff.rfl
#align mul_action.mem_stabilizer_iff MulAction.mem_stabilizer_iff
#align add_action.mem_stabilizer_iff AddAction.mem_stabilizer_iff

#print MulAction.smul_orbit /-
@[simp, to_additive]
theorem smul_orbit (a : α) (b : β) : a • orbit α b = orbit α b :=
  (smul_orbit_subset a b).antisymm <|
    calc
      orbit α b = a • a⁻¹ • orbit α b := (smul_inv_smul _ _).symm
      _ ⊆ a • orbit α b := Set.image_subset _ (smul_orbit_subset _ _)
      
#align mul_action.smul_orbit MulAction.smul_orbit
#align add_action.vadd_orbit AddAction.vadd_orbit
-/

#print MulAction.orbit_smul /-
@[simp, to_additive]
theorem orbit_smul (a : α) (b : β) : orbit α (a • b) = orbit α b :=
  (orbit_smul_subset a b).antisymm <|
    calc
      orbit α b = orbit α (a⁻¹ • a • b) := by rw [inv_smul_smul]
      _ ⊆ orbit α (a • b) := orbit_smul_subset _ _
      
#align mul_action.orbit_smul MulAction.orbit_smul
#align add_action.orbit_vadd AddAction.orbit_vadd
-/

/-- The action of a group on an orbit is transitive. -/
@[to_additive "The action of an additive group on an orbit is transitive."]
instance (x : β) : IsPretransitive α (orbit α x) :=
  ⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    use b * a⁻¹
    ext1
    simp [mul_smul]⟩

#print MulAction.orbit_eq_iff /-
@[to_additive]
theorem orbit_eq_iff {a b : β} : orbit α a = orbit α b ↔ a ∈ orbit α b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨c, hc⟩ => hc ▸ orbit_smul _ _⟩
#align mul_action.orbit_eq_iff MulAction.orbit_eq_iff
#align add_action.orbit_eq_iff AddAction.orbit_eq_iff
-/

variable (α) {β}

#print MulAction.mem_orbit_smul /-
@[to_additive]
theorem mem_orbit_smul (g : α) (a : β) : a ∈ orbit α (g • a) := by
  simp only [orbit_smul, mem_orbit_self]
#align mul_action.mem_orbit_smul MulAction.mem_orbit_smul
#align add_action.mem_orbit_vadd AddAction.mem_orbit_vadd
-/

#print MulAction.smul_mem_orbit_smul /-
@[to_additive]
theorem smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ orbit α (h • a) := by
  simp only [orbit_smul, mem_orbit]
#align mul_action.smul_mem_orbit_smul MulAction.smul_mem_orbit_smul
#align add_action.vadd_mem_orbit_vadd AddAction.vadd_mem_orbit_vadd
-/

variable (α) (β)

#print MulAction.orbitRel /-
/-- The relation 'in the same orbit'. -/
@[to_additive "The relation 'in the same orbit'."]
def orbitRel : Setoid β where
  R a b := a ∈ orbit α b
  iseqv :=
    ⟨mem_orbit_self, fun a b => by simp [orbit_eq_iff.symm, eq_comm], fun a b => by
      simp (config := { contextual := true }) [orbit_eq_iff.symm, eq_comm]⟩
#align mul_action.orbit_rel MulAction.orbitRel
#align add_action.orbit_rel AddAction.orbitRel
-/

attribute [local instance] orbit_rel

variable {α} {β}

#print MulAction.quotient_preimage_image_eq_union_mul /-
/-- When you take a set `U` in `β`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `α`. -/
@[to_additive
      "When you take a set `U` in `β`, push it down to the quotient, and pull back, you get\nthe union of the orbit of `U` under `α`."]
theorem quotient_preimage_image_eq_union_mul (U : Set β) :
    Quotient.mk' ⁻¹' (Quotient.mk' '' U) = ⋃ a : α, (· • ·) a '' U :=
  by
  set f : β → Quotient (MulAction.orbitRel α β) := Quotient.mk'
  ext
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨a, rfl⟩ := Quotient.exact hxy
    rw [Set.mem_unionᵢ]
    exact ⟨a⁻¹, a • x, hy, inv_smul_smul a x⟩
  · intro hx
    rw [Set.mem_unionᵢ] at hx
    obtain ⟨a, u, hu₁, hu₂⟩ := hx
    rw [Set.mem_preimage, Set.mem_image_iff_bex]
    refine' ⟨a⁻¹ • x, _, by simp only [Quotient.eq'] <;> use a⁻¹⟩
    rw [← hu₂]
    convert hu₁
    simp only [inv_smul_smul]
#align mul_action.quotient_preimage_image_eq_union_mul MulAction.quotient_preimage_image_eq_union_mul
#align add_action.quotient_preimage_image_eq_union_add AddAction.quotient_preimage_image_eq_union_add
-/

/- warning: mul_action.disjoint_image_image_iff -> MulAction.disjoint_image_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {U : Set.{u2} β} {V : Set.{u2} β}, Iff (Disjoint.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.completeBooleanAlgebra.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.booleanAlgebra.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))))) (Set.image.{u2, u2} β (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) (Quotient.mk'.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) U) (Set.image.{u2, u2} β (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) (Quotient.mk'.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) V)) (forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x U) -> (forall (a : α), Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) a x) V)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {U : Set.{u2} β} {V : Set.{u2} β}, Iff (Disjoint.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.instCompleteBooleanAlgebraSet.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Preorder.toLE.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (PartialOrder.toPreorder.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.instCompleteBooleanAlgebraSet.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)))))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.instCompleteBooleanAlgebraSet.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)))))))) (Set.image.{u2, u2} β (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) (Quotient.mk'.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) U) (Set.image.{u2, u2} β (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) (Quotient.mk'.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) V)) (forall (x : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x U) -> (forall (a : α), Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a x) V)))
Case conversion may be inaccurate. Consider using '#align mul_action.disjoint_image_image_iff MulAction.disjoint_image_image_iffₓ'. -/
@[to_additive]
theorem disjoint_image_image_iff {U V : Set β} :
    Disjoint (Quotient.mk' '' U) (Quotient.mk' '' V) ↔ ∀ x ∈ U, ∀ a : α, a • x ∉ V :=
  by
  set f : β → Quotient (MulAction.orbitRel α β) := Quotient.mk'
  refine'
    ⟨fun h x x_in_U a a_in_V =>
      h.le_bot ⟨⟨x, x_in_U, Quotient.sound ⟨a⁻¹, _⟩⟩, ⟨a • x, a_in_V, rfl⟩⟩, _⟩
  · simp
  · intro h
    rw [Set.disjoint_left]
    rintro x ⟨y, hy₁, hy₂⟩ ⟨z, hz₁, hz₂⟩
    obtain ⟨a, rfl⟩ := Quotient.exact (hz₂.trans hy₂.symm)
    exact h y hy₁ a hz₁
#align mul_action.disjoint_image_image_iff MulAction.disjoint_image_image_iff
#align add_action.disjoint_image_image_iff AddAction.disjoint_image_image_iff

/- warning: mul_action.image_inter_image_iff -> MulAction.image_inter_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (U : Set.{u2} β) (V : Set.{u2} β), Iff (Eq.{succ u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Inter.inter.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.hasInter.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.image.{u2, u2} β (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) (Quotient.mk'.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) U) (Set.image.{u2, u2} β (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) (Quotient.mk'.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) V)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.hasEmptyc.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))))) (forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x U) -> (forall (a : α), Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) a x) V)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (U : Set.{u2} β) (V : Set.{u2} β), Iff (Eq.{succ u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Inter.inter.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.instInterSet.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.image.{u2, u2} β (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) (Quotient.mk'.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) U) (Set.image.{u2, u2} β (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) (Quotient.mk'.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2)) V)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))) (Set.instEmptyCollectionSet.{u2} (Quotient.{succ u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2))))) (forall (x : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x U) -> (forall (a : α), Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a x) V)))
Case conversion may be inaccurate. Consider using '#align mul_action.image_inter_image_iff MulAction.image_inter_image_iffₓ'. -/
@[to_additive]
theorem image_inter_image_iff (U V : Set β) :
    Quotient.mk' '' U ∩ Quotient.mk' '' V = ∅ ↔ ∀ x ∈ U, ∀ a : α, a • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff
#align mul_action.image_inter_image_iff MulAction.image_inter_image_iff
#align add_action.image_inter_image_iff AddAction.image_inter_image_iff

variable (α β)

#print MulAction.orbitRel.Quotient /-
/-- The quotient by `mul_action.orbit_rel`, given a name to enable dot notation. -/
@[reducible,
  to_additive "The quotient by `add_action.orbit_rel`, given a name to enable dot\nnotation."]
def orbitRel.Quotient : Type _ :=
  Quotient <| orbitRel α β
#align mul_action.orbit_rel.quotient MulAction.orbitRel.Quotient
#align add_action.orbit_rel.quotient AddAction.orbitRel.Quotient
-/

variable {α β}

#print MulAction.orbitRel.Quotient.orbit /-
/-- The orbit corresponding to an element of the quotient by `mul_action.orbit_rel` -/
@[to_additive "The orbit corresponding to an element of the quotient by `add_action.orbit_rel`"]
def orbitRel.Quotient.orbit (x : orbitRel.Quotient α β) : Set β :=
  Quotient.liftOn' x (orbit α) fun _ _ => MulAction.orbit_eq_iff.2
#align mul_action.orbit_rel.quotient.orbit MulAction.orbitRel.Quotient.orbit
#align add_action.orbit_rel.quotient.orbit AddAction.orbitRel.Quotient.orbit
-/

#print MulAction.orbitRel.Quotient.orbit_mk /-
@[simp, to_additive]
theorem orbitRel.Quotient.orbit_mk (b : β) :
    orbitRel.Quotient.orbit (Quotient.mk'' b : orbitRel.Quotient α β) = orbit α b :=
  rfl
#align mul_action.orbit_rel.quotient.orbit_mk MulAction.orbitRel.Quotient.orbit_mk
#align add_action.orbit_rel.quotient.orbit_mk AddAction.orbitRel.Quotient.orbit_mk
-/

#print MulAction.orbitRel.Quotient.mem_orbit /-
@[to_additive]
theorem orbitRel.Quotient.mem_orbit {b : β} {x : orbitRel.Quotient α β} :
    b ∈ x.orbit ↔ Quotient.mk'' b = x :=
  by
  induction x using Quotient.inductionOn'
  rw [Quotient.eq'']
  rfl
#align mul_action.orbit_rel.quotient.mem_orbit MulAction.orbitRel.Quotient.mem_orbit
#align add_action.orbit_rel.quotient.mem_orbit AddAction.orbitRel.Quotient.mem_orbit
-/

#print MulAction.orbitRel.Quotient.orbit_eq_orbit_out /-
/-- Note that `hφ = quotient.out_eq'` is a useful choice here. -/
@[to_additive "Note that `hφ = quotient.out_eq'` is a useful choice here."]
theorem orbitRel.Quotient.orbit_eq_orbit_out (x : orbitRel.Quotient α β)
    {φ : orbitRel.Quotient α β → β} (hφ : RightInverse φ Quotient.mk'') :
    orbitRel.Quotient.orbit x = orbit α (φ x) :=
  by
  conv_lhs => rw [← hφ x]
  induction x using Quotient.inductionOn'
  rfl
#align mul_action.orbit_rel.quotient.orbit_eq_orbit_out MulAction.orbitRel.Quotient.orbit_eq_orbit_out
#align add_action.orbit_rel.quotient.orbit_eq_orbit_out AddAction.orbitRel.Quotient.orbit_eq_orbit_out
-/

variable (α) (β)

-- mathport name: exprΩ
local notation "Ω" => orbitRel.Quotient α β

#print MulAction.selfEquivSigmaOrbits' /-
/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.

This version is expressed in terms of `mul_action.orbit_rel.quotient.orbit` instead of
`mul_action.orbit`, to avoid mentioning `quotient.out'`. -/
@[to_additive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group\naction.\n\nThis version is expressed in terms of `add_action.orbit_rel.quotient.orbit` instead of\n`add_action.orbit`, to avoid mentioning `quotient.out'`. "]
def selfEquivSigmaOrbits' : β ≃ Σω : Ω, ω.orbit :=
  calc
    β ≃ Σω : Ω, { b // Quotient.mk'' b = ω } := (Equiv.sigmaFiberEquiv Quotient.mk'').symm
    _ ≃ Σω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun ω =>
        Equiv.subtypeEquivRight fun x => orbitRel.Quotient.mem_orbit.symm
    
#align mul_action.self_equiv_sigma_orbits' MulAction.selfEquivSigmaOrbits'
#align add_action.self_equiv_sigma_orbits' AddAction.selfEquivSigmaOrbits'
-/

#print MulAction.selfEquivSigmaOrbits /-
/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive
      "Decomposition of a type `X` as a disjoint union of its orbits under an additive group\naction."]
def selfEquivSigmaOrbits : β ≃ Σω : Ω, orbit α ω.out' :=
  (selfEquivSigmaOrbits' α β).trans <|
    Equiv.sigmaCongrRight fun i =>
      Equiv.Set.ofEq <| orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'
#align mul_action.self_equiv_sigma_orbits MulAction.selfEquivSigmaOrbits
#align add_action.self_equiv_sigma_orbits AddAction.selfEquivSigmaOrbits
-/

variable {α β}

/- warning: mul_action.stabilizer_smul_eq_stabilizer_map_conj -> MulAction.stabilizer_smul_eq_stabilizer_map_conj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (g : α) (x : β), Eq.{succ u1} (Subgroup.{u1} α _inst_1) (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) g x)) (Subgroup.map.{u1, u1} α _inst_1 α _inst_1 (MulEquiv.toMonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.group.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) (fun (_x : MonoidHom.{u1, u1} α (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.group.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) => α -> (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (MonoidHom.hasCoeToFun.{u1, u1} α (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.group.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) (MulAut.conj.{u1} α _inst_1) g)) (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (g : α) (x : β), Eq.{succ u1} (Subgroup.{u1} α _inst_1) (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) g x)) (Subgroup.map.{u1, u1} α _inst_1 α _inst_1 (MulEquiv.toMonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.instGroupMulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.instGroupMulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) α (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (MulOneClass.toMul.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.instGroupMulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.instGroupMulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) α (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.instGroupMulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (MonoidHom.monoidHomClass.{u1, u1} α (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (MulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (MulAut.instGroupMulAut.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))))) (MulAut.conj.{u1} α _inst_1) g)) (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x))
Case conversion may be inaccurate. Consider using '#align mul_action.stabilizer_smul_eq_stabilizer_map_conj MulAction.stabilizer_smul_eq_stabilizer_map_conjₓ'. -/
/-- If the stabilizer of `x` is `S`, then the stabilizer of `g • x` is `gSg⁻¹`. -/
theorem stabilizer_smul_eq_stabilizer_map_conj (g : α) (x : β) :
    stabilizer α (g • x) = (stabilizer α x).map (MulAut.conj g).toMonoidHom :=
  by
  ext h
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul, mul_left_inv,
    one_smul, ← mem_stabilizer_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
#align mul_action.stabilizer_smul_eq_stabilizer_map_conj MulAction.stabilizer_smul_eq_stabilizer_map_conj

/- warning: mul_action.stabilizer_equiv_stabilizer_of_orbit_rel -> MulAction.stabilizerEquivStabilizerOfOrbitRel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {x : β} {y : β}, (Setoid.Rel.{u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2) x y) -> (MulEquiv.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_1) α (Subgroup.setLike.{u1} α _inst_1)) (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x)) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_1) α (Subgroup.setLike.{u1} α _inst_1)) (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 y)) (Subgroup.mul.{u1} α _inst_1 (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x)) (Subgroup.mul.{u1} α _inst_1 (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {x : β} {y : β}, (Setoid.Rel.{u2} β (MulAction.orbitRel.{u1, u2} α β _inst_1 _inst_2) x y) -> (MulEquiv.{u1, u1} (Subtype.{succ u1} α (fun (x_1 : α) => Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_1) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_1)) x_1 (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x))) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_1) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_1)) x (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 y))) (Subgroup.mul.{u1} α _inst_1 (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x)) (Subgroup.mul.{u1} α _inst_1 (MulAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 y)))
Case conversion may be inaccurate. Consider using '#align mul_action.stabilizer_equiv_stabilizer_of_orbit_rel MulAction.stabilizerEquivStabilizerOfOrbitRelₓ'. -/
/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {x y : β} (h : (orbitRel α β).Rel x y) :
    stabilizer α x ≃* stabilizer α y :=
  let g : α := Classical.choose h
  have hg : g • y = x := Classical.choose_spec h
  have this : stabilizer α x = (stabilizer α y).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  (MulEquiv.subgroupCongr this).trans ((MulAut.conj g).subgroupMap <| stabilizer α y).symm
#align mul_action.stabilizer_equiv_stabilizer_of_orbit_rel MulAction.stabilizerEquivStabilizerOfOrbitRel

end MulAction

namespace AddAction

variable [AddGroup α] [AddAction α β]

/- warning: add_action.stabilizer_vadd_eq_stabilizer_map_conj -> AddAction.stabilizer_vadd_eq_stabilizer_map_conj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : AddAction.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))] (g : α) (x : β), Eq.{succ u1} (AddSubgroup.{u1} α _inst_1) (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 (VAdd.vadd.{u1, u2} α β (AddAction.toHasVadd.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2) g x)) (AddSubgroup.map.{u1, u1} α _inst_1 α _inst_1 (AddEquiv.toAddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))))) (fun (_x : AddMonoidHom.{u1, u1} α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))))) => α -> (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))) (AddMonoidHom.hasCoeToFun.{u1, u1} α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))))) (AddAut.conj.{u1} α _inst_1) g)) (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : AddAction.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))] (g : α) (x : β), Eq.{succ u1} (AddSubgroup.{u1} α _inst_1) (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 (HVAdd.hVAdd.{u1, u2, u2} α β β (instHVAdd.{u1, u2} α β (AddAction.toVAdd.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2)) g x)) (AddSubgroup.map.{u1, u1} α _inst_1 α _inst_1 (AddEquiv.toAddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => Additive.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))))) α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))) (AddZeroClass.toAdd.{u1} (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))))) α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))))))) (AddMonoidHom.addMonoidHomClass.{u1, u1} α (Additive.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Additive.addZeroClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Monoid.toMulOneClass.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (DivInvMonoid.toMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (Group.toDivInvMonoid.{u1} (AddAut.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) (AddAut.group.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))))))) (AddAut.conj.{u1} α _inst_1) g)) (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x))
Case conversion may be inaccurate. Consider using '#align add_action.stabilizer_vadd_eq_stabilizer_map_conj AddAction.stabilizer_vadd_eq_stabilizer_map_conjₓ'. -/
/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
theorem stabilizer_vadd_eq_stabilizer_map_conj (g : α) (x : β) :
    stabilizer α (g +ᵥ x) = (stabilizer α x).map (AddAut.conj g).toAddMonoidHom :=
  by
  ext h
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g), vadd_vadd, vadd_vadd, vadd_vadd,
    add_left_neg, zero_vadd, ← mem_stabilizer_iff, AddSubgroup.mem_map_equiv,
    AddAut.conj_symm_apply]
#align add_action.stabilizer_vadd_eq_stabilizer_map_conj AddAction.stabilizer_vadd_eq_stabilizer_map_conj

/- warning: add_action.stabilizer_equiv_stabilizer_of_orbit_rel -> AddAction.stabilizerEquivStabilizerOfOrbitRel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : AddAction.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))] {x : β} {y : β}, (Setoid.Rel.{u2} β (AddAction.orbitRel.{u1, u2} α β _inst_1 _inst_2) x y) -> (AddEquiv.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} α _inst_1) α (AddSubgroup.setLike.{u1} α _inst_1)) (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x)) (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} α _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} α _inst_1) α (AddSubgroup.setLike.{u1} α _inst_1)) (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 y)) (AddSubgroup.add.{u1} α _inst_1 (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x)) (AddSubgroup.add.{u1} α _inst_1 (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : AddAction.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))] {x : β} {y : β}, (Setoid.Rel.{u2} β (AddAction.orbitRel.{u1, u2} α β _inst_1 _inst_2) x y) -> (AddEquiv.{u1, u1} (Subtype.{succ u1} α (fun (x_1 : α) => Membership.mem.{u1, u1} α (AddSubgroup.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} α _inst_1) α (AddSubgroup.instSetLikeAddSubgroup.{u1} α _inst_1)) x_1 (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x))) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (AddSubgroup.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} α _inst_1) α (AddSubgroup.instSetLikeAddSubgroup.{u1} α _inst_1)) x (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 y))) (AddSubgroup.add.{u1} α _inst_1 (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 x)) (AddSubgroup.add.{u1} α _inst_1 (AddAction.stabilizer.{u1, u2} α β _inst_1 _inst_2 y)))
Case conversion may be inaccurate. Consider using '#align add_action.stabilizer_equiv_stabilizer_of_orbit_rel AddAction.stabilizerEquivStabilizerOfOrbitRelₓ'. -/
/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizerEquivStabilizerOfOrbitRel {x y : β} (h : (orbitRel α β).Rel x y) :
    stabilizer α x ≃+ stabilizer α y :=
  let g : α := Classical.choose h
  have hg : g +ᵥ y = x := Classical.choose_spec h
  have this : stabilizer α x = (stabilizer α y).map (AddAut.conj g).toAddMonoidHom := by
    rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj]
  (AddEquiv.addSubgroupCongr this).trans ((AddAut.conj g).addSubgroupMap <| stabilizer α y).symm
#align add_action.stabilizer_equiv_stabilizer_of_orbit_rel AddAction.stabilizerEquivStabilizerOfOrbitRel

end AddAction

/- warning: smul_cancel_of_non_zero_divisor -> smul_cancel_of_non_zero_divisor is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : NonUnitalNonAssocRing.{u2} R] [_inst_3 : DistribMulAction.{u1, u2} M R _inst_1 (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2))))] (k : M), (forall (x : R), (Eq.{succ u2} R (SMul.smul.{u1, u2} M R (SMulZeroClass.toHasSmul.{u1, u2} M R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2)))) _inst_3))) k x) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R _inst_2))))))) -> (Eq.{succ u2} R x (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R _inst_2)))))))) -> (forall {a : R} {b : R}, (Eq.{succ u2} R (SMul.smul.{u1, u2} M R (SMulZeroClass.toHasSmul.{u1, u2} M R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2)))) _inst_3))) k a) (SMul.smul.{u1, u2} M R (SMulZeroClass.toHasSmul.{u1, u2} M R (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2)))))) (DistribSMul.toSmulZeroClass.{u1, u2} M R (AddMonoid.toAddZeroClass.{u2} R (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2))))) (DistribMulAction.toDistribSMul.{u1, u2} M R _inst_1 (SubNegMonoid.toAddMonoid.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddCommGroup.toAddGroup.{u2} R (NonUnitalNonAssocRing.toAddCommGroup.{u2} R _inst_2)))) _inst_3))) k b)) -> (Eq.{succ u2} R a b))
but is expected to have type
  forall {M : Type.{u2}} {R : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : NonUnitalNonAssocRing.{u1} R] [_inst_3 : DistribMulAction.{u2, u1} M R _inst_1 (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_2))))] (k : M), (forall (x : R), (Eq.{succ u1} R (HSMul.hSMul.{u2, u1, u1} M R R (instHSMul.{u2, u1} M R (SMulZeroClass.toSMul.{u2, u1} M R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (DistribSMul.toSMulZeroClass.{u2, u1} M R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u1} M R _inst_1 (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_2)))) _inst_3)))) k x) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_2)))))) -> (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_2))))))) -> (forall {a : R} {b : R}, (Eq.{succ u1} R (HSMul.hSMul.{u2, u1, u1} M R R (instHSMul.{u2, u1} M R (SMulZeroClass.toSMul.{u2, u1} M R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (DistribSMul.toSMulZeroClass.{u2, u1} M R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u1} M R _inst_1 (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_2)))) _inst_3)))) k a) (HSMul.hSMul.{u2, u1, u1} M R R (instHSMul.{u2, u1} M R (SMulZeroClass.toSMul.{u2, u1} M R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (DistribSMul.toSMulZeroClass.{u2, u1} M R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_2))))) (DistribMulAction.toDistribSMul.{u2, u1} M R _inst_1 (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_2)))) _inst_3)))) k b)) -> (Eq.{succ u1} R a b))
Case conversion may be inaccurate. Consider using '#align smul_cancel_of_non_zero_divisor smul_cancel_of_non_zero_divisorₓ'. -/
/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `is_smul_regular`.
The typeclass that restricts all terms of `M` to have this property is `no_zero_smul_divisors`. -/
theorem smul_cancel_of_non_zero_divisor {M R : Type _} [Monoid M] [NonUnitalNonAssocRing R]
    [DistribMulAction M R] (k : M) (h : ∀ x : R, k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) :
    a = b := by
  rw [← sub_eq_zero]
  refine' h _ _
  rw [smul_sub, h', sub_self]
#align smul_cancel_of_non_zero_divisor smul_cancel_of_non_zero_divisor

