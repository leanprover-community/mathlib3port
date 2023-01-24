/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module deprecated.group
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Hom.Ring
import Mathbin.Algebra.Hom.Units

/-!
# Unbundled monoid and group homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled monoid and group homomorphisms. Instead of using
this file, please use `monoid_hom`, defined in `algebra.hom.group`, with notation `→*`, for
morphisms between monoids or groups. For example use `φ : G →* H` to represent a group
homomorphism between multiplicative groups, and `ψ : A →+ B` to represent a group homomorphism
between additive groups.

## Main Definitions

`is_monoid_hom` (deprecated), `is_group_hom` (deprecated)

## Tags

is_group_hom, is_monoid_hom

-/


universe u v

variable {α : Type u} {β : Type v}

#print IsAddHom /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_add] [] -/
/-- Predicate for maps which preserve an addition. -/
structure IsAddHom {α β : Type _} [Add α] [Add β] (f : α → β) : Prop where
  map_add : ∀ x y, f (x + y) = f x + f y
#align is_add_hom IsAddHom
-/

#print IsMulHom /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_mul] [] -/
/-- Predicate for maps which preserve a multiplication. -/
@[to_additive]
structure IsMulHom {α β : Type _} [Mul α] [Mul β] (f : α → β) : Prop where
  map_mul : ∀ x y, f (x * y) = f x * f y
#align is_mul_hom IsMulHom
#align is_add_hom IsAddHom
-/

namespace IsMulHom

variable [Mul α] [Mul β] {γ : Type _} [Mul γ]

#print IsMulHom.id /-
/-- The identity map preserves multiplication. -/
@[to_additive "The identity map preserves addition"]
theorem id : IsMulHom (id : α → α) :=
  { map_mul := fun _ _ => rfl }
#align is_mul_hom.id IsMulHom.id
#align is_add_hom.id IsAddHom.id
-/

/- warning: is_mul_hom.comp -> IsMulHom.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] {γ : Type.{u3}} [_inst_3 : Mul.{u3} γ] {f : α -> β} {g : β -> γ}, (IsMulHom.{u1, u2} α β _inst_1 _inst_2 f) -> (IsMulHom.{u2, u3} β γ _inst_2 _inst_3 g) -> (IsMulHom.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Mul.{u2} α] [_inst_2 : Mul.{u3} β] {γ : Type.{u1}} [_inst_3 : Mul.{u1} γ] {f : α -> β} {g : β -> γ}, (IsMulHom.{u2, u3} α β _inst_1 _inst_2 f) -> (IsMulHom.{u3, u1} β γ _inst_2 _inst_3 g) -> (IsMulHom.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u2, succ u3, succ u1} α β γ g f))
Case conversion may be inaccurate. Consider using '#align is_mul_hom.comp IsMulHom.compₓ'. -/
/-- The composition of maps which preserve multiplication, also preserves multiplication. -/
@[to_additive "The composition of addition preserving maps also preserves addition"]
theorem comp {f : α → β} {g : β → γ} (hf : IsMulHom f) (hg : IsMulHom g) : IsMulHom (g ∘ f) :=
  { map_mul := fun x y => by simp only [Function.comp, hf.map_mul, hg.map_mul] }
#align is_mul_hom.comp IsMulHom.comp
#align is_add_hom.comp IsAddHom.comp

/- warning: is_mul_hom.mul -> IsMulHom.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : Semigroup.{u1} α] [_inst_5 : CommSemigroup.{u2} β] {f : α -> β} {g : α -> β}, (IsMulHom.{u1, u2} α β (Semigroup.toHasMul.{u1} α _inst_4) (Semigroup.toHasMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_5)) f) -> (IsMulHom.{u1, u2} α β (Semigroup.toHasMul.{u1} α _inst_4) (Semigroup.toHasMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_5)) g) -> (IsMulHom.{u1, u2} α β (Semigroup.toHasMul.{u1} α _inst_4) (Semigroup.toHasMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_5)) (fun (a : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Semigroup.toHasMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_5))) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : Semigroup.{u2} α] [_inst_5 : CommSemigroup.{u1} β] {f : α -> β} {g : α -> β}, (IsMulHom.{u2, u1} α β (Semigroup.toMul.{u2} α _inst_4) (Semigroup.toMul.{u1} β (CommSemigroup.toSemigroup.{u1} β _inst_5)) f) -> (IsMulHom.{u2, u1} α β (Semigroup.toMul.{u2} α _inst_4) (Semigroup.toMul.{u1} β (CommSemigroup.toSemigroup.{u1} β _inst_5)) g) -> (IsMulHom.{u2, u1} α β (Semigroup.toMul.{u2} α _inst_4) (Semigroup.toMul.{u1} β (CommSemigroup.toSemigroup.{u1} β _inst_5)) (fun (a : α) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Semigroup.toMul.{u1} β (CommSemigroup.toSemigroup.{u1} β _inst_5))) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align is_mul_hom.mul IsMulHom.mulₓ'. -/
/-- A product of maps which preserve multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive
      "A sum of maps which preserves addition, preserves addition when the target\nis commutative."]
theorem mul {α β} [Semigroup α] [CommSemigroup β] {f g : α → β} (hf : IsMulHom f)
    (hg : IsMulHom g) : IsMulHom fun a => f a * g a :=
  {
    map_mul := fun a b => by
      simp only [hf.map_mul, hg.map_mul, mul_comm, mul_assoc, mul_left_comm] }
#align is_mul_hom.mul IsMulHom.mul
#align is_add_hom.add IsAddHom.add

/- warning: is_mul_hom.inv -> IsMulHom.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_4 : Mul.{u1} α] [_inst_5 : CommGroup.{u2} β] {f : α -> β}, (IsMulHom.{u1, u2} α β _inst_4 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β (CommGroup.toGroup.{u2} β _inst_5))))) f) -> (IsMulHom.{u1, u2} α β _inst_4 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β (CommGroup.toGroup.{u2} β _inst_5))))) (fun (a : α) => Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β (CommGroup.toGroup.{u2} β _inst_5))) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_4 : Mul.{u2} α] [_inst_5 : CommGroup.{u1} β] {f : α -> β}, (IsMulHom.{u2, u1} α β _inst_4 (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_5))))) f) -> (IsMulHom.{u2, u1} α β _inst_4 (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_5))))) (fun (a : α) => Inv.inv.{u1} β (InvOneClass.toInv.{u1} β (DivInvOneMonoid.toInvOneClass.{u1} β (DivisionMonoid.toDivInvOneMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β (CommGroup.toDivisionCommMonoid.{u1} β _inst_5))))) (f a)))
Case conversion may be inaccurate. Consider using '#align is_mul_hom.inv IsMulHom.invₓ'. -/
/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive
      "The negation of a map which preserves addition, preserves addition when\nthe target is commutative."]
theorem inv {α β} [Mul α] [CommGroup β] {f : α → β} (hf : IsMulHom f) : IsMulHom fun a => (f a)⁻¹ :=
  { map_mul := fun a b => (hf.map_mul a b).symm ▸ mul_inv _ _ }
#align is_mul_hom.inv IsMulHom.inv
#align is_add_hom.neg IsAddHom.neg

end IsMulHom

#print IsAddMonoidHom /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_zero] [] -/
/-- Predicate for add_monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
structure IsAddMonoidHom [AddZeroClass α] [AddZeroClass β] (f : α → β) extends IsAddHom f :
  Prop where
  map_zero : f 0 = 0
#align is_add_monoid_hom IsAddMonoidHom
-/

#print IsMonoidHom /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`map_one] [] -/
/-- Predicate for monoid homomorphisms (deprecated -- use the bundled `monoid_hom` version). -/
@[to_additive]
structure IsMonoidHom [MulOneClass α] [MulOneClass β] (f : α → β) extends IsMulHom f : Prop where
  map_one : f 1 = 1
#align is_monoid_hom IsMonoidHom
#align is_add_monoid_hom IsAddMonoidHom
-/

namespace MonoidHom

variable {M : Type _} {N : Type _} [mM : MulOneClass M] [mN : MulOneClass N]

include mM mN

#print MonoidHom.of /-
/-- Interpret a map `f : M → N` as a homomorphism `M →* N`. -/
@[to_additive "Interpret a map `f : M → N` as a homomorphism `M →+ N`."]
def of {f : M → N} (h : IsMonoidHom f) : M →* N
    where
  toFun := f
  map_one' := h.2
  map_mul' := h.1.1
#align monoid_hom.of MonoidHom.of
#align add_monoid_hom.of AddMonoidHom.of
-/

variable {mM mN}

/- warning: monoid_hom.coe_of -> MonoidHom.coe_of is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulOneClass.{u1} M} {mN : MulOneClass.{u2} N} {f : M -> N} (hf : IsMonoidHom.{u1, u2} M N mM mN f), Eq.{max (succ u1) (succ u2)} (M -> N) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N mM mN) (fun (_x : MonoidHom.{u1, u2} M N mM mN) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N mM mN) (MonoidHom.of.{u1, u2} M N mM mN f hf)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {mM : MulOneClass.{u2} M} {mN : MulOneClass.{u1} N} {f : M -> N} (hf : IsMonoidHom.{u2, u1} M N mM mN f), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N mM mN) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM mN) M N (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} N mN) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM mN) M N mM mN (MonoidHom.monoidHomClass.{u2, u1} M N mM mN))) (MonoidHom.of.{u2, u1} M N mM mN f hf)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_of MonoidHom.coe_ofₓ'. -/
@[simp, to_additive]
theorem coe_of {f : M → N} (hf : IsMonoidHom f) : ⇑(MonoidHom.of hf) = f :=
  rfl
#align monoid_hom.coe_of MonoidHom.coe_of
#align add_monoid_hom.coe_of AddMonoidHom.coe_of

/- warning: monoid_hom.is_monoid_hom_coe -> MonoidHom.isMonoidHom_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulOneClass.{u1} M} {mN : MulOneClass.{u2} N} (f : MonoidHom.{u1, u2} M N mM mN), IsMonoidHom.{u1, u2} M N mM mN (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N mM mN) (fun (_x : MonoidHom.{u1, u2} M N mM mN) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N mM mN) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {mM : MulOneClass.{u2} M} {mN : MulOneClass.{u1} N} (f : MonoidHom.{u2, u1} M N mM mN), IsMonoidHom.{u2, u1} M N mM mN (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N mM mN) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM mN) M N (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} N mN) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM mN) M N mM mN (MonoidHom.monoidHomClass.{u2, u1} M N mM mN))) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.is_monoid_hom_coe MonoidHom.isMonoidHom_coeₓ'. -/
@[to_additive]
theorem isMonoidHom_coe (f : M →* N) : IsMonoidHom (f : M → N) :=
  { map_mul := f.map_mul
    map_one := f.map_one }
#align monoid_hom.is_monoid_hom_coe MonoidHom.isMonoidHom_coe

end MonoidHom

namespace MulEquiv

variable {M : Type _} {N : Type _} [MulOneClass M] [MulOneClass N]

/- warning: mul_equiv.is_mul_hom -> MulEquiv.isMulHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (h : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)), IsMulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) h)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (h : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)), IsMulHom.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2))))) h)
Case conversion may be inaccurate. Consider using '#align mul_equiv.is_mul_hom MulEquiv.isMulHomₓ'. -/
/-- A multiplicative isomorphism preserves multiplication (deprecated). -/
@[to_additive "An additive isomorphism preserves addition (deprecated)."]
theorem isMulHom (h : M ≃* N) : IsMulHom h :=
  ⟨h.map_mul⟩
#align mul_equiv.is_mul_hom MulEquiv.isMulHom

/- warning: mul_equiv.is_monoid_hom -> MulEquiv.isMonoidHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (h : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)), IsMonoidHom.{u1, u2} M N _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) h)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (h : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)), IsMonoidHom.{u2, u1} M N _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2))))) h)
Case conversion may be inaccurate. Consider using '#align mul_equiv.is_monoid_hom MulEquiv.isMonoidHomₓ'. -/
/-- A multiplicative bijection between two monoids is a monoid hom
  (deprecated -- use `mul_equiv.to_monoid_hom`). -/
@[to_additive
      "An additive bijection between two additive monoids is an additive\nmonoid hom (deprecated). "]
theorem isMonoidHom (h : M ≃* N) : IsMonoidHom h :=
  { map_mul := h.map_mul
    map_one := h.map_one }
#align mul_equiv.is_monoid_hom MulEquiv.isMonoidHom

end MulEquiv

namespace IsMonoidHom

variable [MulOneClass α] [MulOneClass β] {f : α → β} (hf : IsMonoidHom f)

/- warning: is_monoid_hom.map_mul -> IsMonoidHom.map_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : MulOneClass.{u2} β] {f : α -> β}, (IsMonoidHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (x : α) (y : α), Eq.{succ u2} β (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) x y)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β _inst_2)) (f x) (f y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : MulOneClass.{u2} β] {f : α -> β}, (IsMonoidHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (x : α) (y : α), Eq.{succ u2} β (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x y)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toMul.{u2} β _inst_2)) (f x) (f y)))
Case conversion may be inaccurate. Consider using '#align is_monoid_hom.map_mul IsMonoidHom.map_mul'ₓ'. -/
/-- A monoid homomorphism preserves multiplication. -/
@[to_additive "An additive monoid homomorphism preserves addition."]
theorem map_mul' (x y) : f (x * y) = f x * f y :=
  hf.map_mul x y
#align is_monoid_hom.map_mul IsMonoidHom.map_mul'

/- warning: is_monoid_hom.inv -> IsMonoidHom.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : MulOneClass.{u1} α] [_inst_4 : CommGroup.{u2} β] {f : α -> β}, (IsMonoidHom.{u1, u2} α β _inst_3 (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β (CommGroup.toGroup.{u2} β _inst_4)))) f) -> (IsMonoidHom.{u1, u2} α β _inst_3 (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β (CommGroup.toGroup.{u2} β _inst_4)))) (fun (a : α) => Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β (CommGroup.toGroup.{u2} β _inst_4))) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : MulOneClass.{u2} α] [_inst_4 : CommGroup.{u1} β] {f : α -> β}, (IsMonoidHom.{u2, u1} α β _inst_3 (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_4)))) f) -> (IsMonoidHom.{u2, u1} α β _inst_3 (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_4)))) (fun (a : α) => Inv.inv.{u1} β (InvOneClass.toInv.{u1} β (DivInvOneMonoid.toInvOneClass.{u1} β (DivisionMonoid.toDivInvOneMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β (CommGroup.toDivisionCommMonoid.{u1} β _inst_4))))) (f a)))
Case conversion may be inaccurate. Consider using '#align is_monoid_hom.inv IsMonoidHom.invₓ'. -/
/-- The inverse of a map which preserves multiplication,
preserves multiplication when the target is commutative. -/
@[to_additive
      "The negation of a map which preserves addition, preserves addition\nwhen the target is commutative."]
theorem inv {α β} [MulOneClass α] [CommGroup β] {f : α → β} (hf : IsMonoidHom f) :
    IsMonoidHom fun a => (f a)⁻¹ :=
  { map_one := hf.map_one.symm ▸ inv_one
    map_mul := fun a b => (hf.map_mul a b).symm ▸ mul_inv _ _ }
#align is_monoid_hom.inv IsMonoidHom.inv
#align is_add_monoid_hom.neg IsAddMonoidHom.neg

end IsMonoidHom

/- warning: is_mul_hom.to_is_monoid_hom -> IsMulHom.to_isMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsMulHom.{u1, u2} α β (MulOneClass.toHasMul.{u1} α _inst_1) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2)))) f) -> (IsMonoidHom.{u1, u2} α β _inst_1 (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsMulHom.{u1, u2} α β (MulOneClass.toMul.{u1} α _inst_1) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2)))) f) -> (IsMonoidHom.{u1, u2} α β _inst_1 (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align is_mul_hom.to_is_monoid_hom IsMulHom.to_isMonoidHomₓ'. -/
/-- A map to a group preserving multiplication is a monoid homomorphism. -/
@[to_additive "A map to an additive group preserving addition is an additive monoid\nhomomorphism."]
theorem IsMulHom.to_isMonoidHom [MulOneClass α] [Group β] {f : α → β} (hf : IsMulHom f) :
    IsMonoidHom f :=
  { map_one := mul_right_eq_self.1 <| by rw [← hf.map_mul, one_mul]
    map_mul := hf.map_mul }
#align is_mul_hom.to_is_monoid_hom IsMulHom.to_isMonoidHom

namespace IsMonoidHom

variable [MulOneClass α] [MulOneClass β] {f : α → β}

#print IsMonoidHom.id /-
/-- The identity map is a monoid homomorphism. -/
@[to_additive "The identity map is an additive monoid homomorphism."]
theorem id : IsMonoidHom (@id α) :=
  { map_one := rfl
    map_mul := fun _ _ => rfl }
#align is_monoid_hom.id IsMonoidHom.id
#align is_add_monoid_hom.id IsAddMonoidHom.id
-/

/- warning: is_monoid_hom.comp -> IsMonoidHom.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : MulOneClass.{u2} β] {f : α -> β}, (IsMonoidHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {γ : Type.{u3}} [_inst_3 : MulOneClass.{u3} γ] {g : β -> γ}, (IsMonoidHom.{u2, u3} β γ _inst_2 _inst_3 g) -> (IsMonoidHom.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : MulOneClass.{u2} α] [_inst_2 : MulOneClass.{u3} β] {f : α -> β}, (IsMonoidHom.{u2, u3} α β _inst_1 _inst_2 f) -> (forall {γ : Type.{u1}} [_inst_3 : MulOneClass.{u1} γ] {g : β -> γ}, (IsMonoidHom.{u3, u1} β γ _inst_2 _inst_3 g) -> (IsMonoidHom.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u2, succ u3, succ u1} α β γ g f)))
Case conversion may be inaccurate. Consider using '#align is_monoid_hom.comp IsMonoidHom.compₓ'. -/
/-- The composite of two monoid homomorphisms is a monoid homomorphism. -/
@[to_additive
      "The composite of two additive monoid homomorphisms is an additive monoid\nhomomorphism."]
theorem comp (hf : IsMonoidHom f) {γ} [MulOneClass γ] {g : β → γ} (hg : IsMonoidHom g) :
    IsMonoidHom (g ∘ f) :=
  { IsMulHom.comp hf.to_is_mul_hom hg.to_is_mul_hom with
    map_one := show g _ = 1 by rw [hf.map_one, hg.map_one] }
#align is_monoid_hom.comp IsMonoidHom.comp
#align is_add_monoid_hom.comp IsAddMonoidHom.comp

end IsMonoidHom

namespace IsAddMonoidHom

/- warning: is_add_monoid_hom.is_add_monoid_hom_mul_left -> IsAddMonoidHom.isAddMonoidHom_mul_left is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} γ] (x : γ), IsAddMonoidHom.{u1, u1} γ γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} γ _inst_1))) (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} γ _inst_1))) (fun (y : γ) => HMul.hMul.{u1, u1, u1} γ γ γ (instHMul.{u1} γ (Distrib.toHasMul.{u1} γ (NonUnitalNonAssocSemiring.toDistrib.{u1} γ _inst_1))) x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} γ] (x : γ), IsAddMonoidHom.{u1, u1} γ γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} γ _inst_1))) (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} γ _inst_1))) (fun (y : γ) => HMul.hMul.{u1, u1, u1} γ γ γ (instHMul.{u1} γ (NonUnitalNonAssocSemiring.toMul.{u1} γ _inst_1)) x y)
Case conversion may be inaccurate. Consider using '#align is_add_monoid_hom.is_add_monoid_hom_mul_left IsAddMonoidHom.isAddMonoidHom_mul_leftₓ'. -/
/-- Left multiplication in a ring is an additive monoid morphism. -/
theorem isAddMonoidHom_mul_left {γ : Type _} [NonUnitalNonAssocSemiring γ] (x : γ) :
    IsAddMonoidHom fun y : γ => x * y :=
  { map_zero := mul_zero x
    map_add := fun y z => mul_add x y z }
#align is_add_monoid_hom.is_add_monoid_hom_mul_left IsAddMonoidHom.isAddMonoidHom_mul_left

/- warning: is_add_monoid_hom.is_add_monoid_hom_mul_right -> IsAddMonoidHom.isAddMonoidHom_mul_right is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} γ] (x : γ), IsAddMonoidHom.{u1, u1} γ γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} γ _inst_1))) (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} γ _inst_1))) (fun (y : γ) => HMul.hMul.{u1, u1, u1} γ γ γ (instHMul.{u1} γ (Distrib.toHasMul.{u1} γ (NonUnitalNonAssocSemiring.toDistrib.{u1} γ _inst_1))) y x)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} γ] (x : γ), IsAddMonoidHom.{u1, u1} γ γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} γ _inst_1))) (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} γ _inst_1))) (fun (y : γ) => HMul.hMul.{u1, u1, u1} γ γ γ (instHMul.{u1} γ (NonUnitalNonAssocSemiring.toMul.{u1} γ _inst_1)) y x)
Case conversion may be inaccurate. Consider using '#align is_add_monoid_hom.is_add_monoid_hom_mul_right IsAddMonoidHom.isAddMonoidHom_mul_rightₓ'. -/
/-- Right multiplication in a ring is an additive monoid morphism. -/
theorem isAddMonoidHom_mul_right {γ : Type _} [NonUnitalNonAssocSemiring γ] (x : γ) :
    IsAddMonoidHom fun y : γ => y * x :=
  { map_zero := zero_mul x
    map_add := fun y z => add_mul y z x }
#align is_add_monoid_hom.is_add_monoid_hom_mul_right IsAddMonoidHom.isAddMonoidHom_mul_right

end IsAddMonoidHom

#print IsAddGroupHom /-
/-- Predicate for additive group homomorphism (deprecated -- use bundled `monoid_hom`). -/
structure IsAddGroupHom [AddGroup α] [AddGroup β] (f : α → β) extends IsAddHom f : Prop
#align is_add_group_hom IsAddGroupHom
-/

#print IsGroupHom /-
/-- Predicate for group homomorphisms (deprecated -- use bundled `monoid_hom`). -/
@[to_additive]
structure IsGroupHom [Group α] [Group β] (f : α → β) extends IsMulHom f : Prop
#align is_group_hom IsGroupHom
#align is_add_group_hom IsAddGroupHom
-/

/- warning: monoid_hom.is_group_hom -> MonoidHom.isGroupHom is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {_x : Group.{u1} G} {_x_1 : Group.{u2} H} (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _x))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _x_1)))), IsGroupHom.{u1, u2} G H _x _x_1 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _x))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _x_1)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _x))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _x_1)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _x))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _x_1)))) f)
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} {_x : Group.{u2} G} {_x_1 : Group.{u1} H} (f : MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1)))), IsGroupHom.{u2, u1} G H _x _x_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : G) => H) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1)))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1)))) G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1))) (MonoidHom.monoidHomClass.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1)))))) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.is_group_hom MonoidHom.isGroupHomₓ'. -/
@[to_additive]
theorem MonoidHom.isGroupHom {G H : Type _} {_ : Group G} {_ : Group H} (f : G →* H) :
    IsGroupHom (f : G → H) :=
  { map_mul := f.map_mul }
#align monoid_hom.is_group_hom MonoidHom.isGroupHom

/- warning: mul_equiv.is_group_hom -> MulEquiv.isGroupHom is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {_x : Group.{u1} G} {_x_1 : Group.{u2} H} (h : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _x)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _x_1))))), IsGroupHom.{u1, u2} G H _x _x_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _x)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _x_1))))) (fun (_x : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _x)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _x_1))))) => G -> H) (MulEquiv.hasCoeToFun.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _x)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _x_1))))) h)
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} {_x : Group.{u2} G} {_x_1 : Group.{u1} H} (h : MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1))))), IsGroupHom.{u2, u1} G H _x _x_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1))))) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1))))) G H (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1))))) G H (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1))))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1)))) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _x)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _x_1)))))))) h)
Case conversion may be inaccurate. Consider using '#align mul_equiv.is_group_hom MulEquiv.isGroupHomₓ'. -/
@[to_additive]
theorem MulEquiv.isGroupHom {G H : Type _} {_ : Group G} {_ : Group H} (h : G ≃* H) :
    IsGroupHom h :=
  { map_mul := h.map_mul }
#align mul_equiv.is_group_hom MulEquiv.isGroupHom

/- warning: is_group_hom.mk' -> IsGroupHom.mk' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (forall (x : α) (y : α), Eq.{succ u2} β (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x y)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))))) (f x) (f y))) -> (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (forall (x : α) (y : α), Eq.{succ u2} β (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x y)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))))) (f x) (f y))) -> (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_group_hom.mk' IsGroupHom.mk'ₓ'. -/
/-- Construct `is_group_hom` from its only hypothesis. -/
@[to_additive "Construct `is_add_group_hom` from its only hypothesis."]
theorem IsGroupHom.mk' [Group α] [Group β] {f : α → β} (hf : ∀ x y, f (x * y) = f x * f y) :
    IsGroupHom f :=
  { map_mul := hf }
#align is_group_hom.mk' IsGroupHom.mk'
#align is_add_group_hom.mk' IsAddGroupHom.mk'

namespace IsGroupHom

variable [Group α] [Group β] {f : α → β} (hf : IsGroupHom f)

open IsMulHom (map_mul)

/- warning: is_group_hom.map_mul -> IsGroupHom.map_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (x : α) (y : α), Eq.{succ u2} β (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x y)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))))) (f x) (f y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (x : α) (y : α), Eq.{succ u2} β (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x y)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))))) (f x) (f y)))
Case conversion may be inaccurate. Consider using '#align is_group_hom.map_mul IsGroupHom.map_mul'ₓ'. -/
theorem map_mul' : ∀ x y, f (x * y) = f x * f y :=
  hf.to_is_mul_hom.map_mul
#align is_group_hom.map_mul IsGroupHom.map_mul'

#print IsGroupHom.to_isMonoidHom /-
/-- A group homomorphism is a monoid homomorphism. -/
@[to_additive "An additive group homomorphism is an additive monoid homomorphism."]
theorem to_isMonoidHom : IsMonoidHom f :=
  hf.to_is_mul_hom.to_is_monoid_hom
#align is_group_hom.to_is_monoid_hom IsGroupHom.to_isMonoidHom
-/

/- warning: is_group_hom.map_one -> IsGroupHom.map_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (InvOneClass.toOne.{u2} β (DivInvOneMonoid.toInvOneClass.{u2} β (DivisionMonoid.toDivInvOneMonoid.{u2} β (Group.toDivisionMonoid.{u2} β _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align is_group_hom.map_one IsGroupHom.map_oneₓ'. -/
/-- A group homomorphism sends 1 to 1. -/
@[to_additive "An additive group homomorphism sends 0 to 0."]
theorem map_one : f 1 = 1 :=
  hf.to_is_monoid_hom.map_one
#align is_group_hom.map_one IsGroupHom.map_one
#align is_add_group_hom.map_zero IsAddGroupHom.map_zero

/- warning: is_group_hom.map_inv -> IsGroupHom.map_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (a : α), Eq.{succ u2} β (f (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2)) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (a : α), Eq.{succ u2} β (f (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (Inv.inv.{u2} β (InvOneClass.toInv.{u2} β (DivInvOneMonoid.toInvOneClass.{u2} β (DivisionMonoid.toDivInvOneMonoid.{u2} β (Group.toDivisionMonoid.{u2} β _inst_2)))) (f a)))
Case conversion may be inaccurate. Consider using '#align is_group_hom.map_inv IsGroupHom.map_invₓ'. -/
/-- A group homomorphism sends inverses to inverses. -/
@[to_additive "An additive group homomorphism sends negations to negations."]
theorem map_inv (hf : IsGroupHom f) (a : α) : f a⁻¹ = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by rw [← hf.map_mul, inv_mul_self, hf.map_one]
#align is_group_hom.map_inv IsGroupHom.map_inv
#align is_add_group_hom.map_neg IsAddGroupHom.map_neg

/- warning: is_group_hom.map_div -> IsGroupHom.map_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivInvMonoid.toHasDiv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))) (f a) (f b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b)) (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivInvMonoid.toDiv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2))) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align is_group_hom.map_div IsGroupHom.map_divₓ'. -/
@[to_additive]
theorem map_div (hf : IsGroupHom f) (a b : α) : f (a / b) = f a / f b := by
  simp_rw [div_eq_mul_inv, hf.map_mul, hf.map_inv]
#align is_group_hom.map_div IsGroupHom.map_div
#align is_add_group_hom.map_sub IsAddGroupHom.map_sub

#print IsGroupHom.id /-
/-- The identity is a group homomorphism. -/
@[to_additive "The identity is an additive group homomorphism."]
theorem id : IsGroupHom (@id α) :=
  { map_mul := fun _ _ => rfl }
#align is_group_hom.id IsGroupHom.id
#align is_add_group_hom.id IsAddGroupHom.id
-/

/- warning: is_group_hom.comp -> IsGroupHom.comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (forall {γ : Type.{u3}} [_inst_3 : Group.{u3} γ] {g : β -> γ}, (IsGroupHom.{u2, u3} β γ _inst_2 _inst_3 g) -> (IsGroupHom.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : Group.{u3} β] {f : α -> β}, (IsGroupHom.{u2, u3} α β _inst_1 _inst_2 f) -> (forall {γ : Type.{u1}} [_inst_3 : Group.{u1} γ] {g : β -> γ}, (IsGroupHom.{u3, u1} β γ _inst_2 _inst_3 g) -> (IsGroupHom.{u2, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u2, succ u3, succ u1} α β γ g f)))
Case conversion may be inaccurate. Consider using '#align is_group_hom.comp IsGroupHom.compₓ'. -/
/-- The composition of two group homomorphisms is a group homomorphism. -/
@[to_additive
      "The composition of two additive group homomorphisms is an additive\ngroup homomorphism."]
theorem comp (hf : IsGroupHom f) {γ} [Group γ] {g : β → γ} (hg : IsGroupHom g) :
    IsGroupHom (g ∘ f) :=
  { IsMulHom.comp hf.to_is_mul_hom hg.to_is_mul_hom with }
#align is_group_hom.comp IsGroupHom.comp
#align is_add_group_hom.comp IsAddGroupHom.comp

/- warning: is_group_hom.injective_iff -> IsGroupHom.injective_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Iff (Function.Injective.{succ u1, succ u2} α β f) (forall (a : α), (Eq.{succ u2} β (f a) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_2)))))))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : Group.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_1 _inst_2 f) -> (Iff (Function.Injective.{succ u1, succ u2} α β f) (forall (a : α), (Eq.{succ u2} β (f a) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (InvOneClass.toOne.{u2} β (DivInvOneMonoid.toInvOneClass.{u2} β (DivisionMonoid.toDivInvOneMonoid.{u2} β (Group.toDivisionMonoid.{u2} β _inst_2))))))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align is_group_hom.injective_iff IsGroupHom.injective_iffₓ'. -/
/-- A group homomorphism is injective iff its kernel is trivial. -/
@[to_additive "An additive group homomorphism is injective if its kernel is trivial."]
theorem injective_iff {f : α → β} (hf : IsGroupHom f) :
    Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h _ => by rw [← hf.map_one] <;> exact @h _ _, fun h x y hxy =>
    eq_of_div_eq_one <| h _ <| by rwa [hf.map_div, div_eq_one]⟩
#align is_group_hom.injective_iff IsGroupHom.injective_iff
#align is_add_group_hom.injective_iff IsAddGroupHom.injective_iff

/- warning: is_group_hom.mul -> IsGroupHom.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] [_inst_4 : CommGroup.{u2} β] {f : α -> β} {g : α -> β}, (IsGroupHom.{u1, u2} α β _inst_3 (CommGroup.toGroup.{u2} β _inst_4) f) -> (IsGroupHom.{u1, u2} α β _inst_3 (CommGroup.toGroup.{u2} β _inst_4) g) -> (IsGroupHom.{u1, u2} α β _inst_3 (CommGroup.toGroup.{u2} β _inst_4) (fun (a : α) => HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β (CommGroup.toGroup.{u2} β _inst_4)))))) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Group.{u2} α] [_inst_4 : CommGroup.{u1} β] {f : α -> β} {g : α -> β}, (IsGroupHom.{u2, u1} α β _inst_3 (CommGroup.toGroup.{u1} β _inst_4) f) -> (IsGroupHom.{u2, u1} α β _inst_3 (CommGroup.toGroup.{u1} β _inst_4) g) -> (IsGroupHom.{u2, u1} α β _inst_3 (CommGroup.toGroup.{u1} β _inst_4) (fun (a : α) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_4)))))) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align is_group_hom.mul IsGroupHom.mulₓ'. -/
/-- The product of group homomorphisms is a group homomorphism if the target is commutative. -/
@[to_additive
      "The sum of two additive group homomorphisms is an additive group homomorphism\nif the target is commutative."]
theorem mul {α β} [Group α] [CommGroup β] {f g : α → β} (hf : IsGroupHom f) (hg : IsGroupHom g) :
    IsGroupHom fun a => f a * g a :=
  { map_mul := (hf.to_is_mul_hom.mul hg.to_is_mul_hom).map_mul }
#align is_group_hom.mul IsGroupHom.mul
#align is_add_group_hom.add IsAddGroupHom.add

/- warning: is_group_hom.inv -> IsGroupHom.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] [_inst_4 : CommGroup.{u2} β] {f : α -> β}, (IsGroupHom.{u1, u2} α β _inst_3 (CommGroup.toGroup.{u2} β _inst_4) f) -> (IsGroupHom.{u1, u2} α β _inst_3 (CommGroup.toGroup.{u2} β _inst_4) (fun (a : α) => Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β (CommGroup.toGroup.{u2} β _inst_4))) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Group.{u2} α] [_inst_4 : CommGroup.{u1} β] {f : α -> β}, (IsGroupHom.{u2, u1} α β _inst_3 (CommGroup.toGroup.{u1} β _inst_4) f) -> (IsGroupHom.{u2, u1} α β _inst_3 (CommGroup.toGroup.{u1} β _inst_4) (fun (a : α) => Inv.inv.{u1} β (InvOneClass.toInv.{u1} β (DivInvOneMonoid.toInvOneClass.{u1} β (DivisionMonoid.toDivInvOneMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β (CommGroup.toDivisionCommMonoid.{u1} β _inst_4))))) (f a)))
Case conversion may be inaccurate. Consider using '#align is_group_hom.inv IsGroupHom.invₓ'. -/
/-- The inverse of a group homomorphism is a group homomorphism if the target is commutative. -/
@[to_additive
      "The negation of an additive group homomorphism is an additive group homomorphism\nif the target is commutative."]
theorem inv {α β} [Group α] [CommGroup β] {f : α → β} (hf : IsGroupHom f) :
    IsGroupHom fun a => (f a)⁻¹ :=
  { map_mul := hf.to_is_mul_hom.inv.map_mul }
#align is_group_hom.inv IsGroupHom.inv
#align is_add_group_hom.neg IsAddGroupHom.neg

end IsGroupHom

namespace RingHom

/-!
These instances look redundant, because `deprecated.ring` provides `is_ring_hom` for a `→+*`.
Nevertheless these are harmless, and helpful for stripping out dependencies on `deprecated.ring`.
-/


variable {R : Type _} {S : Type _}

section

variable [NonAssocSemiring R] [NonAssocSemiring S]

/- warning: ring_hom.to_is_monoid_hom -> RingHom.to_isMonoidHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NonAssocSemiring.{u2} S] (f : RingHom.{u1, u2} R S _inst_1 _inst_2), IsMonoidHom.{u1, u2} R S (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} S (NonAssocSemiring.toMulZeroOneClass.{u2} S _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S _inst_1 _inst_2) (fun (_x : RingHom.{u1, u2} R S _inst_1 _inst_2) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S _inst_1 _inst_2) f)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : NonAssocSemiring.{u2} R] [_inst_2 : NonAssocSemiring.{u1} S] (f : RingHom.{u2, u1} R S _inst_1 _inst_2), IsMonoidHom.{u2, u1} R S (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u2, u1} R S _inst_1 _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align ring_hom.to_is_monoid_hom RingHom.to_isMonoidHomₓ'. -/
theorem to_isMonoidHom (f : R →+* S) : IsMonoidHom f :=
  { map_one := f.map_one
    map_mul := f.map_mul }
#align ring_hom.to_is_monoid_hom RingHom.to_isMonoidHom

/- warning: ring_hom.to_is_add_monoid_hom -> RingHom.to_isAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NonAssocSemiring.{u2} S] (f : RingHom.{u1, u2} R S _inst_1 _inst_2), IsAddMonoidHom.{u1, u2} R S (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1)))) (AddMonoid.toAddZeroClass.{u2} S (AddMonoidWithOne.toAddMonoid.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S _inst_2)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S _inst_1 _inst_2) (fun (_x : RingHom.{u1, u2} R S _inst_1 _inst_2) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S _inst_1 _inst_2) f)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : NonAssocSemiring.{u2} R] [_inst_2 : NonAssocSemiring.{u1} S] (f : RingHom.{u2, u1} R S _inst_1 _inst_2), IsAddMonoidHom.{u2, u1} R S (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R _inst_1)))) (AddMonoid.toAddZeroClass.{u1} S (AddMonoidWithOne.toAddMonoid.{u1} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} S (NonAssocSemiring.toAddCommMonoidWithOne.{u1} S _inst_2)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S _inst_1 _inst_2) R S _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u2, u1} R S _inst_1 _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align ring_hom.to_is_add_monoid_hom RingHom.to_isAddMonoidHomₓ'. -/
theorem to_isAddMonoidHom (f : R →+* S) : IsAddMonoidHom f :=
  { map_zero := f.map_zero
    map_add := f.map_add }
#align ring_hom.to_is_add_monoid_hom RingHom.to_isAddMonoidHom

end

section

variable [Ring R] [Ring S]

/- warning: ring_hom.to_is_add_group_hom -> RingHom.to_isAddGroupHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))), IsAddGroupHom.{u1, u2} R S (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (AddGroupWithOne.toAddGroup.{u2} S (NonAssocRing.toAddGroupWithOne.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_2))) f)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_2 : Ring.{u1} S] (f : RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))), IsAddGroupHom.{u2, u1} R S (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1)) (AddGroupWithOne.toAddGroup.{u1} S (Ring.toAddGroupWithOne.{u1} S _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2))) R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_2)))))) f)
Case conversion may be inaccurate. Consider using '#align ring_hom.to_is_add_group_hom RingHom.to_isAddGroupHomₓ'. -/
theorem to_isAddGroupHom (f : R →+* S) : IsAddGroupHom f :=
  { map_add := f.map_add }
#align ring_hom.to_is_add_group_hom RingHom.to_isAddGroupHom

end

end RingHom

/- warning: inv.is_group_hom -> Inv.isGroupHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α], IsGroupHom.{u1, u1} α α (CommGroup.toGroup.{u1} α _inst_1) (CommGroup.toGroup.{u1} α _inst_1) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α], IsGroupHom.{u1, u1} α α (CommGroup.toGroup.{u1} α _inst_1) (CommGroup.toGroup.{u1} α _inst_1) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align inv.is_group_hom Inv.isGroupHomₓ'. -/
/-- Inversion is a group homomorphism if the group is commutative. -/
@[to_additive Neg.is_add_group_hom
      "Negation is an `add_group` homomorphism if the `add_group` is commutative."]
theorem Inv.isGroupHom [CommGroup α] : IsGroupHom (Inv.inv : α → α) :=
  { map_mul := mul_inv }
#align inv.is_group_hom Inv.isGroupHom

/- warning: is_add_group_hom.sub -> IsAddGroupHom.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : AddCommGroup.{u2} β] {f : α -> β} {g : α -> β}, (IsAddGroupHom.{u1, u2} α β _inst_1 (AddCommGroup.toAddGroup.{u2} β _inst_2) f) -> (IsAddGroupHom.{u1, u2} α β _inst_1 (AddCommGroup.toAddGroup.{u2} β _inst_2) g) -> (IsAddGroupHom.{u1, u2} α β _inst_1 (AddCommGroup.toAddGroup.{u2} β _inst_2) (fun (a : α) => HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_2)))) (f a) (g a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddGroup.{u2} α] [_inst_2 : AddCommGroup.{u1} β] {f : α -> β} {g : α -> β}, (IsAddGroupHom.{u2, u1} α β _inst_1 (AddCommGroup.toAddGroup.{u1} β _inst_2) f) -> (IsAddGroupHom.{u2, u1} α β _inst_1 (AddCommGroup.toAddGroup.{u1} β _inst_2) g) -> (IsAddGroupHom.{u2, u1} α β _inst_1 (AddCommGroup.toAddGroup.{u1} β _inst_2) (fun (a : α) => HSub.hSub.{u1, u1, u1} β β β (instHSub.{u1} β (SubNegMonoid.toSub.{u1} β (AddGroup.toSubNegMonoid.{u1} β (AddCommGroup.toAddGroup.{u1} β _inst_2)))) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align is_add_group_hom.sub IsAddGroupHom.subₓ'. -/
/-- The difference of two additive group homomorphisms is an additive group
homomorphism if the target is commutative. -/
theorem IsAddGroupHom.sub {α β} [AddGroup α] [AddCommGroup β] {f g : α → β} (hf : IsAddGroupHom f)
    (hg : IsAddGroupHom g) : IsAddGroupHom fun a => f a - g a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align is_add_group_hom.sub IsAddGroupHom.sub

namespace Units

variable {M : Type _} {N : Type _} [Monoid M] [Monoid N]

/- warning: units.map' -> Units.map' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] {f : M -> N}, (IsMonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) f) -> (MonoidHom.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (Units.mulOneClass.{u1} M _inst_1) (Units.mulOneClass.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] {f : M -> N}, (IsMonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) f) -> (MonoidHom.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (Units.instMulOneClassUnits.{u1} M _inst_1) (Units.instMulOneClassUnits.{u2} N _inst_2))
Case conversion may be inaccurate. Consider using '#align units.map' Units.map'ₓ'. -/
/-- The group homomorphism on units induced by a multiplicative morphism. -/
@[reducible]
def map' {f : M → N} (hf : IsMonoidHom f) : Mˣ →* Nˣ :=
  map (MonoidHom.of hf)
#align units.map' Units.map'

/- warning: units.coe_map' -> Units.coe_map' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] {f : M -> N} (hf : IsMonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) f) (x : Units.{u1} M _inst_1), Eq.{succ u2} N ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} N _inst_2) N (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} N _inst_2) N (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} N _inst_2) N (coeBase.{succ u2, succ u2} (Units.{u2} N _inst_2) N (Units.hasCoe.{u2} N _inst_2)))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (Units.mulOneClass.{u1} M _inst_1) (Units.mulOneClass.{u2} N _inst_2)) (fun (_x : MonoidHom.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (Units.mulOneClass.{u1} M _inst_1) (Units.mulOneClass.{u2} N _inst_2)) => (Units.{u1} M _inst_1) -> (Units.{u2} N _inst_2)) (MonoidHom.hasCoeToFun.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (Units.mulOneClass.{u1} M _inst_1) (Units.mulOneClass.{u2} N _inst_2)) (Units.map'.{u1, u2} M N _inst_1 _inst_2 f hf) x)) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] {f : M -> N} (hf : IsMonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) f) (x : Units.{u2} M _inst_1), Eq.{succ u1} N (Units.val.{u1} N _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u2} M _inst_1) (Units.instMulOneClassUnits.{u1} N _inst_2)) (Units.{u2} M _inst_1) (fun (_x : Units.{u2} M _inst_1) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Units.{u2} M _inst_1) => Units.{u1} N _inst_2) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u2} M _inst_1) (Units.instMulOneClassUnits.{u1} N _inst_2)) (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u2} M _inst_1) (Units.instMulOneClassUnits.{u1} N _inst_2)) (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u2} M _inst_1) (Units.instMulOneClassUnits.{u1} N _inst_2) (MonoidHom.monoidHomClass.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u2} M _inst_1) (Units.instMulOneClassUnits.{u1} N _inst_2)))) (Units.map'.{u2, u1} M N _inst_1 _inst_2 f hf) x)) (f (Units.val.{u2} M _inst_1 x))
Case conversion may be inaccurate. Consider using '#align units.coe_map' Units.coe_map'ₓ'. -/
@[simp]
theorem coe_map' {f : M → N} (hf : IsMonoidHom f) (x : Mˣ) : ↑((map' hf : Mˣ → Nˣ) x) = f x :=
  rfl
#align units.coe_map' Units.coe_map'

/- warning: units.coe_is_monoid_hom -> Units.coe_isMonoidHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], IsMonoidHom.{u1, u1} (Units.{u1} M _inst_1) M (Units.mulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u1} M _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], IsMonoidHom.{u1, u1} (Units.{u1} M _inst_1) M (Units.instMulOneClassUnits.{u1} M _inst_1) (Monoid.toMulOneClass.{u1} M _inst_1) (fun (x._@.Mathlib.Deprecated.Group._hyg.1887 : Units.{u1} M _inst_1) => Units.val.{u1} M _inst_1 x._@.Mathlib.Deprecated.Group._hyg.1887)
Case conversion may be inaccurate. Consider using '#align units.coe_is_monoid_hom Units.coe_isMonoidHomₓ'. -/
theorem coe_isMonoidHom : IsMonoidHom (coe : Mˣ → M) :=
  (coeHom M).is_monoid_hom_coe
#align units.coe_is_monoid_hom Units.coe_isMonoidHom

end Units

namespace IsUnit

variable {M : Type _} {N : Type _} [Monoid M] [Monoid N] {x : M}

/- warning: is_unit.map' -> IsUnit.map' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] {f : M -> N}, (IsMonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) f) -> (forall {x : M}, (IsUnit.{u1} M _inst_1 x) -> (IsUnit.{u2} N _inst_2 (f x)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] {f : M -> N}, (IsMonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) f) -> (forall {x : M}, (IsUnit.{u2} M _inst_1 x) -> (IsUnit.{u1} N _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align is_unit.map' IsUnit.map'ₓ'. -/
theorem map' {f : M → N} (hf : IsMonoidHom f) {x : M} (h : IsUnit x) : IsUnit (f x) :=
  h.map (MonoidHom.of hf)
#align is_unit.map' IsUnit.map'

end IsUnit

/- warning: additive.is_add_hom -> Additive.isAddHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] {f : α -> β}, (IsMulHom.{u1, u2} α β _inst_1 _inst_2 f) -> (IsAddHom.{u1, u2} (Additive.{u1} α) (Additive.{u2} β) (Additive.hasAdd.{u1} α _inst_1) (Additive.hasAdd.{u2} β _inst_2) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] {f : α -> β}, (IsMulHom.{u1, u2} α β _inst_1 _inst_2 f) -> (IsAddHom.{u1, u2} (Additive.{u1} α) (Additive.{u2} β) (Additive.add.{u1} α _inst_1) (Additive.add.{u2} β _inst_2) f)
Case conversion may be inaccurate. Consider using '#align additive.is_add_hom Additive.isAddHomₓ'. -/
theorem Additive.isAddHom [Mul α] [Mul β] {f : α → β} (hf : IsMulHom f) :
    @IsAddHom (Additive α) (Additive β) _ _ f :=
  { map_add := IsMulHom.map_mul hf }
#align additive.is_add_hom Additive.isAddHom

/- warning: multiplicative.is_mul_hom -> Multiplicative.isMulHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Add.{u1} α] [_inst_2 : Add.{u2} β] {f : α -> β}, (IsAddHom.{u1, u2} α β _inst_1 _inst_2 f) -> (IsMulHom.{u1, u2} (Multiplicative.{u1} α) (Multiplicative.{u2} β) (Multiplicative.hasMul.{u1} α _inst_1) (Multiplicative.hasMul.{u2} β _inst_2) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Add.{u1} α] [_inst_2 : Add.{u2} β] {f : α -> β}, (IsAddHom.{u1, u2} α β _inst_1 _inst_2 f) -> (IsMulHom.{u1, u2} (Multiplicative.{u1} α) (Multiplicative.{u2} β) (Multiplicative.mul.{u1} α _inst_1) (Multiplicative.mul.{u2} β _inst_2) f)
Case conversion may be inaccurate. Consider using '#align multiplicative.is_mul_hom Multiplicative.isMulHomₓ'. -/
theorem Multiplicative.isMulHom [Add α] [Add β] {f : α → β} (hf : IsAddHom f) :
    @IsMulHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { map_mul := IsAddHom.map_add hf }
#align multiplicative.is_mul_hom Multiplicative.isMulHom

#print Additive.isAddMonoidHom /-
-- defeq abuse
theorem Additive.isAddMonoidHom [MulOneClass α] [MulOneClass β] {f : α → β} (hf : IsMonoidHom f) :
    @IsAddMonoidHom (Additive α) (Additive β) _ _ f :=
  { Additive.isAddHom hf.to_is_mul_hom with map_zero := hf.map_one }
#align additive.is_add_monoid_hom Additive.isAddMonoidHom
-/

#print Multiplicative.isMonoidHom /-
theorem Multiplicative.isMonoidHom [AddZeroClass α] [AddZeroClass β] {f : α → β}
    (hf : IsAddMonoidHom f) : @IsMonoidHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { Multiplicative.isMulHom hf.to_is_add_hom with map_one := IsAddMonoidHom.map_zero hf }
#align multiplicative.is_monoid_hom Multiplicative.isMonoidHom
-/

#print Additive.isAddGroupHom /-
theorem Additive.isAddGroupHom [Group α] [Group β] {f : α → β} (hf : IsGroupHom f) :
    @IsAddGroupHom (Additive α) (Additive β) _ _ f :=
  { map_add := hf.to_is_mul_hom.map_mul }
#align additive.is_add_group_hom Additive.isAddGroupHom
-/

#print Multiplicative.isGroupHom /-
theorem Multiplicative.isGroupHom [AddGroup α] [AddGroup β] {f : α → β} (hf : IsAddGroupHom f) :
    @IsGroupHom (Multiplicative α) (Multiplicative β) _ _ f :=
  { map_mul := hf.to_is_add_hom.map_add }
#align multiplicative.is_group_hom Multiplicative.isGroupHom
-/

