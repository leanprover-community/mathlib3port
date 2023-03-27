/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module deprecated.ring
! leanprover-community/mathlib commit 10708587e81b68c763fcdb7505f279d52e569768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Deprecated.Group

/-!
# Unbundled semiring and ring homomorphisms (deprecated)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled semiring and ring homomorphisms. Instead of using
this file, please use `ring_hom`, defined in `algebra.hom.ring`, with notation `→+*`, for
morphisms between semirings or rings. For example use `φ : A →+* B` to represent a
ring homomorphism.

## Main Definitions

`is_semiring_hom` (deprecated), `is_ring_hom` (deprecated)

## Tags

is_semiring_hom, is_ring_hom

-/


universe u v w

variable {α : Type u}

#print IsSemiringHom /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_zero] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_one] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_add] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_mul] [] -/
/-- Predicate for semiring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
structure IsSemiringHom {α : Type u} {β : Type v} [Semiring α] [Semiring β] (f : α → β) : Prop where
  map_zero : f 0 = 0
  map_one : f 1 = 1
  map_add : ∀ {x y}, f (x + y) = f x + f y
  map_mul : ∀ {x y}, f (x * y) = f x * f y
#align is_semiring_hom IsSemiringHom
-/

namespace IsSemiringHom

variable {β : Type v} [Semiring α] [Semiring β]

variable {f : α → β} (hf : IsSemiringHom f) {x y : α}

#print IsSemiringHom.id /-
/-- The identity map is a semiring homomorphism. -/
theorem id : IsSemiringHom (@id α) := by refine' { .. } <;> intros <;> rfl
#align is_semiring_hom.id IsSemiringHom.id
-/

/- warning: is_semiring_hom.comp -> IsSemiringHom.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Semiring.{u2} β] {f : α -> β}, (IsSemiringHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {γ : Type.{u3}} [_inst_3 : Semiring.{u3} γ] {g : β -> γ}, (IsSemiringHom.{u2, u3} β γ _inst_2 _inst_3 g) -> (IsSemiringHom.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Semiring.{u2} α] [_inst_2 : Semiring.{u3} β] {f : α -> β}, (IsSemiringHom.{u2, u3} α β _inst_1 _inst_2 f) -> (forall {γ : Type.{u1}} [_inst_3 : Semiring.{u1} γ] {g : β -> γ}, (IsSemiringHom.{u3, u1} β γ _inst_2 _inst_3 g) -> (IsSemiringHom.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u2, succ u3, succ u1} α β γ g f)))
Case conversion may be inaccurate. Consider using '#align is_semiring_hom.comp IsSemiringHom.compₓ'. -/
/-- The composition of two semiring homomorphisms is a semiring homomorphism. -/
theorem comp (hf : IsSemiringHom f) {γ} [Semiring γ] {g : β → γ} (hg : IsSemiringHom g) :
    IsSemiringHom (g ∘ f) :=
  { map_zero := by simpa [map_zero hf] using map_zero hg
    map_one := by simpa [map_one hf] using map_one hg
    map_add := fun x y => by simp [map_add hf, map_add hg]
    map_mul := fun x y => by simp [map_mul hf, map_mul hg] }
#align is_semiring_hom.comp IsSemiringHom.comp

#print IsSemiringHom.to_isAddMonoidHom /-
/-- A semiring homomorphism is an additive monoid homomorphism. -/
theorem to_isAddMonoidHom (hf : IsSemiringHom f) : IsAddMonoidHom f :=
  { ‹IsSemiringHom f› with }
#align is_semiring_hom.to_is_add_monoid_hom IsSemiringHom.to_isAddMonoidHom
-/

#print IsSemiringHom.to_isMonoidHom /-
/-- A semiring homomorphism is a monoid homomorphism. -/
theorem to_isMonoidHom (hf : IsSemiringHom f) : IsMonoidHom f :=
  { ‹IsSemiringHom f› with }
#align is_semiring_hom.to_is_monoid_hom IsSemiringHom.to_isMonoidHom
-/

end IsSemiringHom

#print IsRingHom /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_one] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_mul] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_add] [] -/
/-- Predicate for ring homomorphisms (deprecated -- use the bundled `ring_hom` version). -/
structure IsRingHom {α : Type u} {β : Type v} [Ring α] [Ring β] (f : α → β) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ {x y}, f (x * y) = f x * f y
  map_add : ∀ {x y}, f (x + y) = f x + f y
#align is_ring_hom IsRingHom
-/

namespace IsRingHom

variable {β : Type v} [Ring α] [Ring β]

#print IsRingHom.of_semiring /-
/-- A map of rings that is a semiring homomorphism is also a ring homomorphism. -/
theorem of_semiring {f : α → β} (H : IsSemiringHom f) : IsRingHom f :=
  { H with }
#align is_ring_hom.of_semiring IsRingHom.of_semiring
-/

variable {f : α → β} (hf : IsRingHom f) {x y : α}

/- warning: is_ring_hom.map_zero -> IsRingHom.map_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))))))) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β (Ring.toSemiring.{u2} β _inst_2))))))
Case conversion may be inaccurate. Consider using '#align is_ring_hom.map_zero IsRingHom.map_zeroₓ'. -/
/-- Ring homomorphisms map zero to zero. -/
theorem map_zero (hf : IsRingHom f) : f 0 = 0 :=
  calc
    f 0 = f (0 + 0) - f 0 := by rw [hf.map_add] <;> simp
    _ = 0 := by simp
    
#align is_ring_hom.map_zero IsRingHom.map_zero

/- warning: is_ring_hom.map_neg -> IsRingHom.map_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β} {x : α}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Eq.{succ u2} β (f (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))))) x)) (Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddGroupWithOne.toAddGroup.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β _inst_2))))) (f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β} {x : α}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Eq.{succ u2} β (f (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) x)) (Neg.neg.{u2} β (Ring.toNeg.{u2} β _inst_2) (f x)))
Case conversion may be inaccurate. Consider using '#align is_ring_hom.map_neg IsRingHom.map_negₓ'. -/
/-- Ring homomorphisms preserve additive inverses. -/
theorem map_neg (hf : IsRingHom f) : f (-x) = -f x :=
  calc
    f (-x) = f (-x + x) - f x := by rw [hf.map_add] <;> simp
    _ = -f x := by simp [hf.map_zero]
    
#align is_ring_hom.map_neg IsRingHom.map_neg

/- warning: is_ring_hom.map_sub -> IsRingHom.map_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β} {x : α} {y : α}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Eq.{succ u2} β (f (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))))) x y)) (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddGroupWithOne.toAddGroup.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β _inst_2)))))) (f x) (f y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β} {x : α} {y : α}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Eq.{succ u2} β (f (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) x y)) (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (Ring.toSub.{u2} β _inst_2)) (f x) (f y)))
Case conversion may be inaccurate. Consider using '#align is_ring_hom.map_sub IsRingHom.map_subₓ'. -/
/-- Ring homomorphisms preserve subtraction. -/
theorem map_sub (hf : IsRingHom f) : f (x - y) = f x - f y := by
  simp [sub_eq_add_neg, hf.map_add, hf.map_neg]
#align is_ring_hom.map_sub IsRingHom.map_sub

#print IsRingHom.id /-
/-- The identity map is a ring homomorphism. -/
theorem id : IsRingHom (@id α) := by refine' { .. } <;> intros <;> rfl
#align is_ring_hom.id IsRingHom.id
-/

/- warning: is_ring_hom.comp -> IsRingHom.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {γ : Type.{u3}} [_inst_3 : Ring.{u3} γ] {g : β -> γ}, (IsRingHom.{u2, u3} β γ _inst_2 _inst_3 g) -> (IsRingHom.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Ring.{u2} α] [_inst_2 : Ring.{u3} β] {f : α -> β}, (IsRingHom.{u2, u3} α β _inst_1 _inst_2 f) -> (forall {γ : Type.{u1}} [_inst_3 : Ring.{u1} γ] {g : β -> γ}, (IsRingHom.{u3, u1} β γ _inst_2 _inst_3 g) -> (IsRingHom.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u2, succ u3, succ u1} α β γ g f)))
Case conversion may be inaccurate. Consider using '#align is_ring_hom.comp IsRingHom.compₓ'. -/
-- see Note [no instance on morphisms]
/-- The composition of two ring homomorphisms is a ring homomorphism. -/
theorem comp (hf : IsRingHom f) {γ} [Ring γ] {g : β → γ} (hg : IsRingHom g) : IsRingHom (g ∘ f) :=
  { map_add := fun x y => by simp [map_add hf] <;> rw [map_add hg] <;> rfl
    map_mul := fun x y => by simp [map_mul hf] <;> rw [map_mul hg] <;> rfl
    map_one := by simp [map_one hf] <;> exact map_one hg }
#align is_ring_hom.comp IsRingHom.comp

#print IsRingHom.to_isSemiringHom /-
/-- A ring homomorphism is also a semiring homomorphism. -/
theorem to_isSemiringHom (hf : IsRingHom f) : IsSemiringHom f :=
  { ‹IsRingHom f› with map_zero := map_zero hf }
#align is_ring_hom.to_is_semiring_hom IsRingHom.to_isSemiringHom
-/

/- warning: is_ring_hom.to_is_add_group_hom -> IsRingHom.to_isAddGroupHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (IsAddGroupHom.{u1, u2} α β (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))) (AddGroupWithOne.toAddGroup.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β _inst_2))) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} β] {f : α -> β}, (IsRingHom.{u1, u2} α β _inst_1 _inst_2 f) -> (IsAddGroupHom.{u1, u2} α β (AddGroupWithOne.toAddGroup.{u1} α (Ring.toAddGroupWithOne.{u1} α _inst_1)) (AddGroupWithOne.toAddGroup.{u2} β (Ring.toAddGroupWithOne.{u2} β _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align is_ring_hom.to_is_add_group_hom IsRingHom.to_isAddGroupHomₓ'. -/
theorem to_isAddGroupHom (hf : IsRingHom f) : IsAddGroupHom f :=
  { map_add := fun _ _ => hf.map_add }
#align is_ring_hom.to_is_add_group_hom IsRingHom.to_isAddGroupHom

end IsRingHom

variable {β : Type v} {γ : Type w} [rα : Semiring α] [rβ : Semiring β]

namespace RingHom

section

include rα rβ

#print RingHom.of /-
/-- Interpret `f : α → β` with `is_semiring_hom f` as a ring homomorphism. -/
def of {f : α → β} (hf : IsSemiringHom f) : α →+* β :=
  { MonoidHom.of hf.to_isMonoidHom, AddMonoidHom.of hf.to_isAddMonoidHom with toFun := f }
#align ring_hom.of RingHom.of
-/

/- warning: ring_hom.coe_of -> RingHom.coe_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [rα : Semiring.{u1} α] [rβ : Semiring.{u2} β] {f : α -> β} (hf : IsSemiringHom.{u1, u2} α β rα rβ f), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) (fun (_x : RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) => α -> β) (RingHom.hasCoeToFun.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) (RingHom.of.{u1, u2} α β rα rβ f hf)) f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {rα : Semiring.{u1} α} {rβ : Semiring.{u2} β} {f : α -> β} (hf : IsSemiringHom.{u1, u2} α β rα rβ f), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) α β (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α rα))) (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β rβ))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α rα)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β rβ)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ) (RingHom.instRingHomClassRingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ))))) (RingHom.of.{u1, u2} α β rα rβ f hf)) f
Case conversion may be inaccurate. Consider using '#align ring_hom.coe_of RingHom.coe_ofₓ'. -/
@[simp]
theorem coe_of {f : α → β} (hf : IsSemiringHom f) : ⇑(of hf) = f :=
  rfl
#align ring_hom.coe_of RingHom.coe_of

/- warning: ring_hom.to_is_semiring_hom -> RingHom.to_isSemiringHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [rα : Semiring.{u1} α] [rβ : Semiring.{u2} β] (f : RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)), IsSemiringHom.{u1, u2} α β rα rβ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) (fun (_x : RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) => α -> β) (RingHom.hasCoeToFun.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {rα : Semiring.{u1} α} {rβ : Semiring.{u2} β} (f : RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)), IsSemiringHom.{u1, u2} α β rα rβ (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) α β (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α rα))) (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β rβ))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α rα)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β rβ)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ)) α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ) (RingHom.instRingHomClassRingHom.{u1, u2} α β (Semiring.toNonAssocSemiring.{u1} α rα) (Semiring.toNonAssocSemiring.{u2} β rβ))))) f)
Case conversion may be inaccurate. Consider using '#align ring_hom.to_is_semiring_hom RingHom.to_isSemiringHomₓ'. -/
theorem to_isSemiringHom (f : α →+* β) : IsSemiringHom f :=
  { map_zero := f.map_zero
    map_one := f.map_one
    map_add := f.map_add
    map_mul := f.map_mul }
#align ring_hom.to_is_semiring_hom RingHom.to_isSemiringHom

end

/- warning: ring_hom.to_is_ring_hom -> RingHom.to_isRingHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : Ring.{u2} γ] (g : RingHom.{u1, u2} α γ (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} γ (Ring.toNonAssocRing.{u2} γ _inst_2))), IsRingHom.{u1, u2} α γ _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α γ (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} γ (Ring.toNonAssocRing.{u2} γ _inst_2))) (fun (_x : RingHom.{u1, u2} α γ (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} γ (Ring.toNonAssocRing.{u2} γ _inst_2))) => α -> γ) (RingHom.hasCoeToFun.{u1, u2} α γ (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} γ (Ring.toNonAssocRing.{u2} γ _inst_2))) g)
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Ring.{u2} α] [_inst_2 : Ring.{u1} γ] (g : RingHom.{u2, u1} α γ (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2))), IsRingHom.{u2, u1} α γ _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} α γ (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => γ) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} α γ (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2))) α γ (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} γ (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} α γ (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2))) α γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} γ (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} α γ (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2))) α γ (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} α γ (NonAssocRing.toNonAssocSemiring.{u2} α (Ring.toNonAssocRing.{u2} α _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} γ (Ring.toNonAssocRing.{u1} γ _inst_2)))))) g)
Case conversion may be inaccurate. Consider using '#align ring_hom.to_is_ring_hom RingHom.to_isRingHomₓ'. -/
theorem to_isRingHom {α γ} [Ring α] [Ring γ] (g : α →+* γ) : IsRingHom g :=
  IsRingHom.of_semiring g.to_isSemiringHom
#align ring_hom.to_is_ring_hom RingHom.to_isRingHom

end RingHom

