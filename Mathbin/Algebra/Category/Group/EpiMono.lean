/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebra.category.Group.epi_mono
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.EquivalenceGroupAddGroup
import Mathbin.GroupTheory.QuotientGroup

/-!
# Monomorphisms and epimorphisms in `Group`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
In this file, we prove monomorphisms in category of group are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/


noncomputable section

universe u v

namespace MonoidHom

open QuotientGroup

variable {A : Type u} {B : Type v}

section

variable [Group A] [Group B]

/- warning: monoid_hom.ker_eq_bot_of_cancel -> MonoidHom.ker_eq_bot_of_cancel is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align monoid_hom.ker_eq_bot_of_cancel MonoidHom.ker_eq_bot_of_cancelₓ'. -/
@[to_additive AddMonoidHom.ker_eq_bot_of_cancel]
theorem ker_eq_bot_of_cancel {f : A →* B} (h : ∀ u v : f.ker →* A, f.comp u = f.comp v → u = v) :
    f.ker = ⊥ := by simpa using _root_.congr_arg range (h f.ker.subtype 1 (by tidy))
#align monoid_hom.ker_eq_bot_of_cancel MonoidHom.ker_eq_bot_of_cancel
#align add_monoid_hom.ker_eq_bot_of_cancel AddMonoidHom.ker_eq_bot_of_cancel

end

section

variable [CommGroup A] [CommGroup B]

/- warning: monoid_hom.range_eq_top_of_cancel -> MonoidHom.range_eq_top_of_cancel is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align monoid_hom.range_eq_top_of_cancel MonoidHom.range_eq_top_of_cancelₓ'. -/
@[to_additive AddMonoidHom.range_eq_top_of_cancel]
theorem range_eq_top_of_cancel {f : A →* B}
    (h : ∀ u v : B →* B ⧸ f.range, u.comp f = v.comp f → u = v) : f.range = ⊤ :=
  by
  specialize h 1 (QuotientGroup.mk' _) _
  · ext1
    simp only [one_apply, coe_comp, coe_mk', Function.comp_apply]
    rw [show (1 : B ⧸ f.range) = (1 : B) from QuotientGroup.mk_one _, QuotientGroup.eq, inv_one,
      one_mul]
    exact ⟨x, rfl⟩
  replace h : (QuotientGroup.mk' _).ker = (1 : B →* B ⧸ f.range).ker := by rw [h]
  rwa [ker_one, QuotientGroup.ker_mk'] at h
#align monoid_hom.range_eq_top_of_cancel MonoidHom.range_eq_top_of_cancel
#align add_monoid_hom.range_eq_top_of_cancel AddMonoidHom.range_eq_top_of_cancel

end

end MonoidHom

section

open CategoryTheory

namespace GroupCat

variable {A B : GroupCat.{u}} (f : A ⟶ B)

/- warning: Group.ker_eq_bot_of_mono -> GroupCat.ker_eq_bot_of_mono is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B) [_inst_1 : CategoryTheory.Mono.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1} A B f], Eq.{succ u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A)) (MonoidHom.ker.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B))) f) (Bot.bot.{u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A)) (Subgroup.hasBot.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A)))
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B) [_inst_1 : CategoryTheory.Mono.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1} A B f], Eq.{succ u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A)) (MonoidHom.ker.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) ((fun {α : Type.{u1}} (h : Group.{u1} α) => DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α h)) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B))) f) (Bot.bot.{u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A)) (Subgroup.instBotSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A)))
Case conversion may be inaccurate. Consider using '#align Group.ker_eq_bot_of_mono GroupCat.ker_eq_bot_of_monoₓ'. -/
@[to_additive AddGroupCat.ker_eq_bot_of_mono]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v =>
    (@cancel_mono _ _ _ _ _ f _ (show GroupCat.of f.ker ⟶ A from u) _).1
#align Group.ker_eq_bot_of_mono GroupCat.ker_eq_bot_of_mono
#align AddGroup.ker_eq_bot_of_mono AddGroupCat.ker_eq_bot_of_mono

/- warning: Group.mono_iff_ker_eq_bot -> GroupCat.mono_iff_ker_eq_bot is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B), Iff (CategoryTheory.Mono.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1} A B f) (Eq.{succ u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A)) (MonoidHom.ker.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B))) f) (Bot.bot.{u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A)) (Subgroup.hasBot.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A))))
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B), Iff (CategoryTheory.Mono.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1} A B f) (Eq.{succ u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A)) (MonoidHom.ker.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) ((fun {α : Type.{u1}} (h : Group.{u1} α) => DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α h)) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B))) f) (Bot.bot.{u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A)) (Subgroup.instBotSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A))))
Case conversion may be inaccurate. Consider using '#align Group.mono_iff_ker_eq_bot GroupCat.mono_iff_ker_eq_botₓ'. -/
@[to_additive AddGroupCat.mono_iff_ker_eq_bot]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun h => @ker_eq_bot_of_mono f h, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩
#align Group.mono_iff_ker_eq_bot GroupCat.mono_iff_ker_eq_bot
#align AddGroup.mono_iff_ker_eq_bot AddGroupCat.mono_iff_ker_eq_bot

/- warning: Group.mono_iff_injective -> GroupCat.mono_iff_injective is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B), Iff (CategoryTheory.Mono.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1} A B f) (Function.Injective.{succ u1, succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B) (fun (_x : MonoidHom.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} A))) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B)))) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B)) (MonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} A))) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B)))) f))
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B), Iff (CategoryTheory.Mono.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1} A B f) (Function.Injective.{succ u1, succ u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (fun (_x : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) => CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (MulOneClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A))))) (MulOneClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B)))) (MonoidHom.monoidHomClass.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))))) f))
Case conversion may be inaccurate. Consider using '#align Group.mono_iff_injective GroupCat.mono_iff_injectiveₓ'. -/
@[to_additive AddGroupCat.mono_iff_injective]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f
#align Group.mono_iff_injective GroupCat.mono_iff_injective
#align AddGroup.mono_iff_injective AddGroupCat.mono_iff_injective

namespace SurjectiveOfEpiAuxs

-- mathport name: exprX
local notation "X" => Set.range (Function.swap leftCoset f.range.carrier)

#print GroupCat.SurjectiveOfEpiAuxs.XWithInfinity /-
/-- Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
@[nolint has_nonempty_instance]
inductive XWithInfinity
  | from_coset : Set.range (Function.swap leftCoset f.range.carrier) → X_with_infinity
  | infinity : X_with_infinity
#align Group.surjective_of_epi_auxs.X_with_infinity GroupCat.SurjectiveOfEpiAuxs.XWithInfinity
-/

open XWithInfinity Equiv.Perm

open Coset

-- mathport name: exprX'
local notation "X'" => XWithInfinity f

-- mathport name: «expr∞»
local notation "∞" => XWithInfinity.infinity

-- mathport name: exprSX'
local notation "SX'" => Equiv.Perm X'

instance : SMul B X'
    where smul b x :=
    match x with
    | from_coset y =>
      fromCoset
        ⟨b *l y, by
          rw [← Subtype.val_eq_coe, ← y.2.choose_spec, leftCoset_assoc]
          use b * y.2.some⟩
    | ∞ => ∞

/- warning: Group.surjective_of_epi_auxs.mul_smul -> GroupCat.SurjectiveOfEpiAuxs.mul_smul is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B) (b : coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (b' : coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (x : GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f), Eq.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (SMul.smul.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.hasSmul.{u1} A B f) (HMul.hMul.{u1, u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (instHMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (MulOneClass.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (Group.toDivInvMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (GroupCat.group.{u1} B)))))) b b') x) (SMul.smul.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.hasSmul.{u1} A B f) b (SMul.smul.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.hasSmul.{u1} A B f) b' x))
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B) (b : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (b' : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (x : GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f), Eq.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (HSMul.hSMul.{u1, u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (instHSMul.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.instSMulαGroupXWithInfinity.{u1} A B f)) (HMul.hMul.{u1, u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (instHMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (MulOneClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup.0.GroupCat.instMulOneClassαGroup.{u1} B))) b b') x) (HSMul.hSMul.{u1, u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (instHSMul.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.instSMulαGroupXWithInfinity.{u1} A B f)) b (HSMul.hSMul.{u1, u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (instHSMul.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.instSMulαGroupXWithInfinity.{u1} A B f)) b' x))
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.mul_smul GroupCat.SurjectiveOfEpiAuxs.mul_smulₓ'. -/
theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x :=
  match x with
  | from_coset y => by
    change from_coset _ = from_coset _
    simp only [← Subtype.val_eq_coe, leftCoset_assoc]
  | ∞ => rfl
#align Group.surjective_of_epi_auxs.mul_smul GroupCat.SurjectiveOfEpiAuxs.mul_smul

/- warning: Group.surjective_of_epi_auxs.one_smul -> GroupCat.SurjectiveOfEpiAuxs.one_smul is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B) (x : GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f), Eq.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (SMul.smul.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.hasSmul.{u1} A B f) (OfNat.ofNat.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) 1 (OfNat.mk.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) 1 (One.one.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (MulOneClass.toHasOne.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (Group.toDivInvMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (GroupCat.group.{u1} B)))))))) x) x
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B) (x : GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f), Eq.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (HSMul.hSMul.{u1, u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (instHSMul.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.instSMulαGroupXWithInfinity.{u1} A B f)) (OfNat.ofNat.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) 1 (One.toOfNat1.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (InvOneClass.toOne.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvOneMonoid.toInvOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivisionMonoid.toDivInvOneMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivisionMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B))))))) x) x
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.one_smul GroupCat.SurjectiveOfEpiAuxs.one_smulₓ'. -/
theorem one_smul (x : X') : (1 : B) • x = x :=
  match x with
  | from_coset y => by
    change from_coset _ = from_coset _
    simp only [← Subtype.val_eq_coe, one_leftCoset, Subtype.ext_iff_val]
  | ∞ => rfl
#align Group.surjective_of_epi_auxs.one_smul GroupCat.SurjectiveOfEpiAuxs.one_smul

/- warning: Group.surjective_of_epi_auxs.from_coset_eq_of_mem_range -> GroupCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.from_coset_eq_of_mem_range GroupCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_rangeₓ'. -/
theorem fromCoset_eq_of_mem_range {b : B} (hb : b ∈ f.range) :
    fromCoset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ =
      fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
  by
  congr
  change b *l f.range = f.range
  nth_rw 2 [show (f.range : Set B) = 1 *l f.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff, mul_one]
  exact Subgroup.inv_mem _ hb
#align Group.surjective_of_epi_auxs.from_coset_eq_of_mem_range GroupCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range

/- warning: Group.surjective_of_epi_auxs.from_coset_ne_of_nin_range -> GroupCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.from_coset_ne_of_nin_range GroupCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_rangeₓ'. -/
theorem fromCoset_ne_of_nin_range {b : B} (hb : b ∉ f.range) :
    fromCoset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ ≠
      fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
  by
  intro r
  simp only [Subtype.mk_eq_mk] at r
  change b *l f.range = f.range at r
  nth_rw 2 [show (f.range : Set B) = 1 *l f.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff, mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)
#align Group.surjective_of_epi_auxs.from_coset_ne_of_nin_range GroupCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range

instance : DecidableEq X' :=
  Classical.decEq _

#print GroupCat.SurjectiveOfEpiAuxs.tau /-
/-- Let `τ` be the permutation on `X'` exchanging `f.range` and the point at infinity.
-/
noncomputable def tau : SX' :=
  Equiv.swap (fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) ∞
#align Group.surjective_of_epi_auxs.tau GroupCat.SurjectiveOfEpiAuxs.tau
-/

-- mathport name: exprτ
local notation "τ" => tau f

#print GroupCat.SurjectiveOfEpiAuxs.τ_apply_infinity /-
theorem τ_apply_infinity : τ ∞ = fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
  Equiv.swap_apply_right _ _
#align Group.surjective_of_epi_auxs.τ_apply_infinity GroupCat.SurjectiveOfEpiAuxs.τ_apply_infinity
-/

/- warning: Group.surjective_of_epi_auxs.τ_apply_from_coset clashes with Group.surjective_of_epi_auxs.τ_apply_fromCoset -> GroupCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.τ_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.τ_apply_fromCosetₓ'. -/
#print GroupCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset /-
theorem τ_apply_fromCoset : τ (fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) = ∞ :=
  Equiv.swap_apply_left _ _
#align Group.surjective_of_epi_auxs.τ_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset
-/

theorem τ_apply_from_coset' (x : B) (hx : x ∈ f.range) :
    τ (fromCoset ⟨x *l f.range.carrier, ⟨x, rfl⟩⟩) = ∞ :=
  (fromCoset_eq_of_mem_range _ hx).symm ▸ τ_apply_fromCoset _
#align Group.surjective_of_epi_auxs.τ_apply_from_coset' GroupCat.SurjectiveOfEpiAuxs.τ_apply_from_coset'

/- warning: Group.surjective_of_epi_auxs.τ_symm_apply_from_coset clashes with Group.surjective_of_epi_auxs.τ_symm_apply_fromCoset -> GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCoset
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.τ_symm_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCosetₓ'. -/
#print GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCoset /-
theorem τ_symm_apply_fromCoset :
    (Equiv.symm τ) (fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) = ∞ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_left]
#align Group.surjective_of_epi_auxs.τ_symm_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCoset
-/

#print GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity /-
theorem τ_symm_apply_infinity :
    (Equiv.symm τ) ∞ = fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ := by
  rw [tau, Equiv.symm_swap, Equiv.swap_apply_right]
#align Group.surjective_of_epi_auxs.τ_symm_apply_infinity GroupCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity
-/

#print GroupCat.SurjectiveOfEpiAuxs.g /-
/-- Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending
point at infinity to point at infinity and sending coset `y` to `β *l y`.
-/
def g : B →* SX'
    where
  toFun β :=
    { toFun := fun x => β • x
      invFun := fun x => β⁻¹ • x
      left_inv := fun x => by
        dsimp only
        rw [← mul_smul, mul_left_inv, one_smul]
      right_inv := fun x => by
        dsimp only
        rw [← mul_smul, mul_right_inv, one_smul] }
  map_one' := by
    ext
    simp [one_smul]
  map_mul' b1 b2 := by
    ext
    simp [mul_smul]
#align Group.surjective_of_epi_auxs.G GroupCat.SurjectiveOfEpiAuxs.g
-/

-- mathport name: exprg
local notation "g" => g f

#print GroupCat.SurjectiveOfEpiAuxs.h /-
/-- Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
def h : B →* SX' where
  toFun β := (τ.symm.trans (g β)).trans τ
  map_one' := by
    ext
    simp
  map_mul' b1 b2 := by
    ext
    simp
#align Group.surjective_of_epi_auxs.H GroupCat.SurjectiveOfEpiAuxs.h
-/

-- mathport name: exprh
local notation "h" => h f

/-!
The strategy is the following: assuming `epi f`
* prove that `f.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.range`, then `h x ≠ g x` at the coset `f.range`.
-/


/- warning: Group.surjective_of_epi_auxs.g_apply_from_coset clashes with Group.surjective_of_epi_auxs.g_apply_fromCoset -> GroupCat.SurjectiveOfEpiAuxs.g_apply_fromCoset
warning: Group.surjective_of_epi_auxs.g_apply_from_coset -> GroupCat.SurjectiveOfEpiAuxs.g_apply_fromCoset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.g_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.g_apply_fromCosetₓ'. -/
theorem g_apply_fromCoset (x : B) (y : X) : (g x) (fromCoset y) = fromCoset ⟨x *l y, by tidy⟩ :=
  rfl
#align Group.surjective_of_epi_auxs.g_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.g_apply_fromCoset

#print GroupCat.SurjectiveOfEpiAuxs.g_apply_infinity /-
theorem g_apply_infinity (x : B) : (g x) ∞ = ∞ :=
  rfl
#align Group.surjective_of_epi_auxs.g_apply_infinity GroupCat.SurjectiveOfEpiAuxs.g_apply_infinity
-/

/- warning: Group.surjective_of_epi_auxs.h_apply_infinity -> GroupCat.SurjectiveOfEpiAuxs.h_apply_infinity is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.h_apply_infinity GroupCat.SurjectiveOfEpiAuxs.h_apply_infinityₓ'. -/
theorem h_apply_infinity (x : B) (hx : x ∈ f.range) : (h x) ∞ = ∞ :=
  by
  simp only [H, MonoidHom.coe_mk, Equiv.toFun_as_coe, Equiv.coe_trans, Function.comp_apply]
  rw [τ_symm_apply_infinity, g_apply_from_coset]
  simpa only [← Subtype.val_eq_coe] using τ_apply_from_coset' f x hx
#align Group.surjective_of_epi_auxs.h_apply_infinity GroupCat.SurjectiveOfEpiAuxs.h_apply_infinity

/- warning: Group.surjective_of_epi_auxs.h_apply_from_coset clashes with Group.surjective_of_epi_auxs.h_apply_fromCoset -> GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.h_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCosetₓ'. -/
#print GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset /-
theorem h_apply_fromCoset (x : B) :
    (h x) (fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) =
      fromCoset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
  by simp [H, τ_symm_apply_from_coset, g_apply_infinity, τ_apply_infinity]
#align Group.surjective_of_epi_auxs.h_apply_from_coset GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset
-/

theorem h_apply_from_coset' (x : B) (b : B) (hb : b ∈ f.range) :
    (h x) (fromCoset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) =
      fromCoset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ :=
  (fromCoset_eq_of_mem_range _ hb).symm ▸ h_apply_fromCoset f x
#align Group.surjective_of_epi_auxs.h_apply_from_coset' GroupCat.SurjectiveOfEpiAuxs.h_apply_from_coset'

/- warning: Group.surjective_of_epi_auxs.h_apply_from_coset_nin_range clashes with Group.surjective_of_epi_auxs.h_apply_fromCoset_nin_range -> GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range
warning: Group.surjective_of_epi_auxs.h_apply_from_coset_nin_range -> GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.h_apply_from_coset_nin_range GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_rangeₓ'. -/
theorem h_apply_fromCoset_nin_range (x : B) (hx : x ∈ f.range) (b : B) (hb : b ∉ f.range) :
    (h x) (fromCoset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) =
      fromCoset ⟨x * b *l f.range.carrier, ⟨x * b, rfl⟩⟩ :=
  by
  simp only [H, tau, MonoidHom.coe_mk, Equiv.toFun_as_coe, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap,
    @Equiv.swap_apply_of_ne_of_ne X' _ (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) ∞
      (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) (from_coset_ne_of_nin_range _ hb) (by simp)]
  simp only [g_apply_from_coset, ← Subtype.val_eq_coe, leftCoset_assoc]
  refine' Equiv.swap_apply_of_ne_of_ne (from_coset_ne_of_nin_range _ fun r => hb _) (by simp)
  convert Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) r
  rw [← mul_assoc, mul_left_inv, one_mul]
#align Group.surjective_of_epi_auxs.h_apply_from_coset_nin_range GroupCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range

/- warning: Group.surjective_of_epi_auxs.agree -> GroupCat.SurjectiveOfEpiAuxs.agree is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.agree GroupCat.SurjectiveOfEpiAuxs.agreeₓ'. -/
theorem agree : f.range.carrier = { x | h x = g x } :=
  by
  refine' Set.ext fun b => ⟨_, fun hb : h b = g b => by_contradiction fun r => _⟩
  · rintro ⟨a, rfl⟩
    change h (f a) = g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [g_apply_from_coset]
      by_cases m : y ∈ f.range
      · rw [h_apply_from_coset' _ _ _ m, from_coset_eq_of_mem_range _ m]
        change from_coset _ = from_coset ⟨f a *l (y *l _), _⟩
        simpa only [← from_coset_eq_of_mem_range _ (Subgroup.mul_mem _ ⟨a, rfl⟩ m), leftCoset_assoc]
      · rw [h_apply_from_coset_nin_range _ _ ⟨_, rfl⟩ _ m]
        simpa only [← Subtype.val_eq_coe, leftCoset_assoc]
    · rw [g_apply_infinity, h_apply_infinity _ _ ⟨_, rfl⟩]
  · have eq1 :
      (h b) (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) =
        from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩ :=
      by simp [H, tau, g_apply_infinity]
    have eq2 :
      (g b) (from_coset ⟨f.range.carrier, ⟨1, one_leftCoset _⟩⟩) =
        from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ :=
      rfl
    exact (from_coset_ne_of_nin_range _ r).symm (by rw [← eq1, ← eq2, FunLike.congr_fun hb])
#align Group.surjective_of_epi_auxs.agree GroupCat.SurjectiveOfEpiAuxs.agree

#print GroupCat.SurjectiveOfEpiAuxs.comp_eq /-
theorem comp_eq : (f ≫ show B ⟶ GroupCat.of SX' from g) = f ≫ h :=
  FunLike.ext _ _ fun a => by
    simp only [comp_apply, show h (f a) = _ from (by simp [← agree] : f a ∈ { b | h b = g b })]
#align Group.surjective_of_epi_auxs.comp_eq GroupCat.SurjectiveOfEpiAuxs.comp_eq
-/

/- warning: Group.surjective_of_epi_auxs.g_ne_h -> GroupCat.SurjectiveOfEpiAuxs.g_ne_h is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B) (x : coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B), (Not (Membership.Mem.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (GroupCat.group.{u1} B)) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (GroupCat.group.{u1} B)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Subgroup.setLike.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (GroupCat.group.{u1} B))) x (MonoidHom.range.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (GroupCat.group.{u1} B) f))) -> (Ne.{succ u1} (MonoidHom.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (Equiv.Perm.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (Group.toDivInvMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} GroupCat.{u1} Type.{u1} GroupCat.hasCoeToSort.{u1} B) (GroupCat.group.{u1} B)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)) (Equiv.Perm.permGroup.{u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)))))) (GroupCat.SurjectiveOfEpiAuxs.g.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.h.{u1} A B f))
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B) (x : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B), (Not (Membership.mem.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B)) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Subgroup.instSetLikeSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B))) x (MonoidHom.range.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B) f))) -> (Ne.{succ u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Equiv.Perm.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)) (_private.Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup.0.GroupCat.instMulOneClassαGroup.{u1} B) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)) (Equiv.Perm.permGroup.{u1} (GroupCat.SurjectiveOfEpiAuxs.XWithInfinity.{u1} A B f)))))) (GroupCat.SurjectiveOfEpiAuxs.g.{u1} A B f) (GroupCat.SurjectiveOfEpiAuxs.h.{u1} A B f))
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi_auxs.g_ne_h GroupCat.SurjectiveOfEpiAuxs.g_ne_hₓ'. -/
theorem g_ne_h (x : B) (hx : x ∉ f.range) : g ≠ h :=
  by
  intro r
  replace r :=
    FunLike.congr_fun (FunLike.congr_fun r x) (from_coset ⟨f.range, ⟨1, one_leftCoset _⟩⟩)
  rw [H, g_apply_from_coset, MonoidHom.coe_mk, tau] at r
  simp only [MonoidHom.coe_range, Subtype.coe_mk, Equiv.symm_swap, Equiv.toFun_as_coe,
    Equiv.coe_trans, Function.comp_apply] at r
  erw [Equiv.swap_apply_left, g_apply_infinity, Equiv.swap_apply_right] at r
  exact from_coset_ne_of_nin_range _ hx r
#align Group.surjective_of_epi_auxs.g_ne_h GroupCat.SurjectiveOfEpiAuxs.g_ne_h

end SurjectiveOfEpiAuxs

/- warning: Group.surjective_of_epi -> GroupCat.surjective_of_epi is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B) [_inst_1 : CategoryTheory.Epi.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1} A B f], Function.Surjective.{succ u1, succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B) (fun (_x : MonoidHom.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} A))) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B)))) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B)) (MonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} A))) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B)))) f)
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B) [_inst_1 : CategoryTheory.Epi.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1} A B f], Function.Surjective.{succ u1, succ u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (fun (_x : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) => CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (MulOneClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A))))) (MulOneClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B)))) (MonoidHom.monoidHomClass.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))))) f)
Case conversion may be inaccurate. Consider using '#align Group.surjective_of_epi GroupCat.surjective_of_epiₓ'. -/
theorem surjective_of_epi [Epi f] : Function.Surjective f :=
  by
  by_contra r
  push_neg  at r
  rcases r with ⟨b, hb⟩
  exact
    surjective_of_epi_auxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      ((cancel_epi f).1 (surjective_of_epi_auxs.comp_eq f))
#align Group.surjective_of_epi GroupCat.surjective_of_epi

/- warning: Group.epi_iff_surjective -> GroupCat.epi_iff_surjective is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1} A B f) (Function.Surjective.{succ u1, succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B) (fun (_x : MonoidHom.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} A))) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B)))) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B)) (MonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} A))) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} Group.{u1} B)))) f))
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1} A B f) (Function.Surjective.{succ u1, succ u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (fun (_x : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) => CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (MulOneClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A))))) (MulOneClass.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B)))) (MonoidHom.monoidHomClass.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα.{u1} A)))) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (Group.toDivInvMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα.{u1} B))))))) f))
Case conversion may be inaccurate. Consider using '#align Group.epi_iff_surjective GroupCat.epi_iff_surjectiveₓ'. -/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  ⟨fun h => @surjective_of_epi f h, ConcreteCategory.epi_of_surjective _⟩
#align Group.epi_iff_surjective GroupCat.epi_iff_surjective

/- warning: Group.epi_iff_range_eq_top -> GroupCat.epi_iff_range_eq_top is a dubious translation:
lean 3 declaration is
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} GroupCat.{u1} GroupCat.largeCategory.{u1} A B f) (Eq.{succ u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (GroupCat.group.{u1} B)) (MonoidHom.range.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) A) (GroupCat.group.{u1} A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (GroupCat.group.{u1} B) f) (Top.top.{u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (GroupCat.group.{u1} B)) (Subgroup.hasTop.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Group.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Group.{u1}) B) (GroupCat.group.{u1} B))))
but is expected to have type
  forall {A : GroupCat.{u1}} {B : GroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} GroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} GroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} GroupCat.{u1} instGroupCatLargeCategory.{u1} A B f) (Eq.{succ u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B)) (MonoidHom.range.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} A) (GroupCat.instGroupα_1.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B) f) (Top.top.{u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B)) (Subgroup.instTopSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} Group.{u1} B) (GroupCat.instGroupα_1.{u1} B))))
Case conversion may be inaccurate. Consider using '#align Group.epi_iff_range_eq_top GroupCat.epi_iff_range_eq_topₓ'. -/
theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (Subgroup.eq_top_iff' f.range).symm
#align Group.epi_iff_range_eq_top GroupCat.epi_iff_range_eq_top

end GroupCat

namespace AddGroupCat

variable {A B : AddGroupCat.{u}} (f : A ⟶ B)

/- warning: AddGroup.epi_iff_surjective -> AddGroupCat.epi_iff_surjective is a dubious translation:
lean 3 declaration is
  forall {A : AddGroupCat.{u1}} {B : AddGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddGroupCat.{u1} AddGroupCat.largeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} AddGroupCat.{u1} AddGroupCat.largeCategory.{u1} A B f) (Function.Surjective.{succ u1, succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} AddGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddGroupCat.{u1} AddGroupCat.largeCategory.{u1})) A B) (fun (_x : AddMonoidHom.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (AddMonoid.toAddZeroClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) (AddGroup.toAddMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) (CategoryTheory.Bundled.str.{u1, u1} AddGroup.{u1} A))) (AddMonoid.toAddZeroClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (AddGroup.toAddMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} AddGroup.{u1} B)))) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B)) (AddMonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (AddMonoid.toAddZeroClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) (AddGroup.toAddMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) (CategoryTheory.Bundled.str.{u1, u1} AddGroup.{u1} A))) (AddMonoid.toAddZeroClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (AddGroup.toAddMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} AddGroup.{u1} B)))) f))
but is expected to have type
  forall {A : AddGroupCat.{u1}} {B : AddGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddGroupCat.{u1} instAddGroupCatLargeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} AddGroupCat.{u1} instAddGroupCatLargeCategory.{u1} A B f) (Function.Surjective.{succ u1, succ u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroupCat.instGroupα.{u1} A)))) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (fun (_x : CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) => CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroupCat.instGroupα.{u1} A)))) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddZeroClass.toAdd.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroupCat.instGroupα.{u1} A))))) (AddZeroClass.toAdd.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα.{u1} B))))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroupCat.instGroupα.{u1} A)))) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα.{u1} B))))) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroupCat.instGroupα.{u1} A)))) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα.{u1} B)))) (AddMonoidHom.addMonoidHomClass.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroupCat.instGroupα.{u1} A)))) (AddMonoid.toAddZeroClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (SubNegMonoid.toAddMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroup.toSubNegMonoid.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα.{u1} B))))))) f))
Case conversion may be inaccurate. Consider using '#align AddGroup.epi_iff_surjective AddGroupCat.epi_iff_surjectiveₓ'. -/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f :=
  by
  have i1 : epi f ↔ epi (Group_AddGroup_equivalence.inverse.map f) :=
    by
    refine' ⟨_, Group_AddGroup_equivalence.inverse.epi_of_epi_map⟩
    intro e'
    apply Group_AddGroup_equivalence.inverse.map_epi
  rwa [GroupCat.epi_iff_surjective] at i1
#align AddGroup.epi_iff_surjective AddGroupCat.epi_iff_surjective

/- warning: AddGroup.epi_iff_range_eq_top -> AddGroupCat.epi_iff_range_eq_top is a dubious translation:
lean 3 declaration is
  forall {A : AddGroupCat.{u1}} {B : AddGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddGroupCat.{u1} AddGroupCat.largeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} AddGroupCat.{u1} AddGroupCat.largeCategory.{u1} A B f) (Eq.{succ u1} (AddSubgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (AddGroupCat.addGroup.{u1} B)) (AddMonoidHom.range.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) A) (AddGroupCat.addGroup.{u1} A) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (AddGroupCat.addGroup.{u1} B) f) (Top.top.{u1} (AddSubgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (AddGroupCat.addGroup.{u1} B)) (AddSubgroup.hasTop.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddGroup.{u1}) B) (AddGroupCat.addGroup.{u1} B))))
but is expected to have type
  forall {A : AddGroupCat.{u1}} {B : AddGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddGroupCat.{u1} instAddGroupCatLargeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} AddGroupCat.{u1} instAddGroupCatLargeCategory.{u1} A B f) (Eq.{succ u1} (AddSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα_1.{u1} B)) (AddMonoidHom.range.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} A) (AddGroupCat.instGroupα_1.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα_1.{u1} B) f) (Top.top.{u1} (AddSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα_1.{u1} B)) (AddSubgroup.instTopAddSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddGroup.{u1} B) (AddGroupCat.instGroupα_1.{u1} B))))
Case conversion may be inaccurate. Consider using '#align AddGroup.epi_iff_range_eq_top AddGroupCat.epi_iff_range_eq_topₓ'. -/
theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  Iff.trans (epi_iff_surjective _) (AddSubgroup.eq_top_iff' f.range).symm
#align AddGroup.epi_iff_range_eq_top AddGroupCat.epi_iff_range_eq_top

end AddGroupCat

namespace GroupCat

variable {A B : GroupCat.{u}} (f : A ⟶ B)

#print GroupCat.forget_groupCat_preserves_mono /-
@[to_additive]
instance forget_groupCat_preserves_mono : (forget GroupCat).PreservesMonomorphisms
    where preserves X Y f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e
#align Group.forget_Group_preserves_mono GroupCat.forget_groupCat_preserves_mono
#align AddGroup.forget_Group_preserves_mono AddGroupCat.forget_groupCat_preserves_mono
-/

#print GroupCat.forget_groupCat_preserves_epi /-
@[to_additive]
instance forget_groupCat_preserves_epi : (forget GroupCat).PreservesEpimorphisms
    where preserves X Y f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e
#align Group.forget_Group_preserves_epi GroupCat.forget_groupCat_preserves_epi
#align AddGroup.forget_Group_preserves_epi AddGroupCat.forget_groupCat_preserves_epi
-/

end GroupCat

namespace CommGroupCat

variable {A B : CommGroupCat.{u}} (f : A ⟶ B)

/- warning: CommGroup.ker_eq_bot_of_mono -> CommGroupCat.ker_eq_bot_of_mono is a dubious translation:
lean 3 declaration is
  forall {A : CommGroupCat.{u1}} {B : CommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} CommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommGroupCat.{u1} CommGroupCat.largeCategory.{u1})) A B) [_inst_1 : CategoryTheory.Mono.{u1, succ u1} CommGroupCat.{u1} CommGroupCat.largeCategory.{u1} A B f], Eq.{succ u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A))) (MonoidHom.ker.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} CommGroup.{u1} B)))) f) (Bot.bot.{u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A))) (Subgroup.hasBot.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A))))
but is expected to have type
  forall {A : CommGroupCat.{u1}} {B : CommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} CommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommGroupCat.{u1} instCommGroupCatLargeCategory.{u1})) A B) [_inst_1 : CategoryTheory.Mono.{u1, succ u1} CommGroupCat.{u1} instCommGroupCatLargeCategory.{u1} A B f], Eq.{succ u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A)) (MonoidHom.ker.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) ((fun {α : Type.{u1}} (h : Group.{u1} α) => DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α h)) (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (CommGroup.toGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (CategoryTheory.Bundled.str.{u1, u1} CommGroup.{u1} B)))) f) (Bot.bot.{u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A)) (Subgroup.instBotSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A)))
Case conversion may be inaccurate. Consider using '#align CommGroup.ker_eq_bot_of_mono CommGroupCat.ker_eq_bot_of_monoₓ'. -/
@[to_additive AddCommGroupCat.ker_eq_bot_of_mono]
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  MonoidHom.ker_eq_bot_of_cancel fun u v =>
    (@cancel_mono _ _ _ _ _ f _ (show CommGroupCat.of f.ker ⟶ A from u) _).1
#align CommGroup.ker_eq_bot_of_mono CommGroupCat.ker_eq_bot_of_mono
#align AddCommGroup.ker_eq_bot_of_mono AddCommGroupCat.ker_eq_bot_of_mono

/- warning: CommGroup.mono_iff_ker_eq_bot -> CommGroupCat.mono_iff_ker_eq_bot is a dubious translation:
lean 3 declaration is
  forall {A : CommGroupCat.{u1}} {B : CommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} CommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommGroupCat.{u1} CommGroupCat.largeCategory.{u1})) A B), Iff (CategoryTheory.Mono.{u1, succ u1} CommGroupCat.{u1} CommGroupCat.largeCategory.{u1} A B f) (Eq.{succ u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A))) (MonoidHom.ker.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (Group.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CategoryTheory.Bundled.str.{u1, u1} CommGroup.{u1} B)))) f) (Bot.bot.{u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A))) (Subgroup.hasBot.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A)))))
but is expected to have type
  forall {A : CommGroupCat.{u1}} {B : CommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} CommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommGroupCat.{u1} instCommGroupCatLargeCategory.{u1})) A B), Iff (CategoryTheory.Mono.{u1, succ u1} CommGroupCat.{u1} instCommGroupCatLargeCategory.{u1} A B f) (Eq.{succ u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A)) (MonoidHom.ker.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (Monoid.toMulOneClass.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) ((fun {α : Type.{u1}} (h : Group.{u1} α) => DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α h)) (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (CommGroup.toGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (CategoryTheory.Bundled.str.{u1, u1} CommGroup.{u1} B)))) f) (Bot.bot.{u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A)) (Subgroup.instBotSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A))))
Case conversion may be inaccurate. Consider using '#align CommGroup.mono_iff_ker_eq_bot CommGroupCat.mono_iff_ker_eq_botₓ'. -/
@[to_additive AddCommGroupCat.mono_iff_ker_eq_bot]
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun h => @ker_eq_bot_of_mono f h, fun h =>
    ConcreteCategory.mono_of_injective _ <| (MonoidHom.ker_eq_bot_iff f).1 h⟩
#align CommGroup.mono_iff_ker_eq_bot CommGroupCat.mono_iff_ker_eq_bot
#align AddCommGroup.mono_iff_ker_eq_bot AddCommGroupCat.mono_iff_ker_eq_bot

/- warning: CommGroup.mono_iff_injective -> CommGroupCat.mono_iff_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align CommGroup.mono_iff_injective CommGroupCat.mono_iff_injectiveₓ'. -/
@[to_additive AddCommGroupCat.mono_iff_injective]
theorem mono_iff_injective : Mono f ↔ Function.Injective f :=
  Iff.trans (mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f
#align CommGroup.mono_iff_injective CommGroupCat.mono_iff_injective
#align AddCommGroup.mono_iff_injective AddCommGroupCat.mono_iff_injective

/- warning: CommGroup.range_eq_top_of_epi -> CommGroupCat.range_eq_top_of_epi is a dubious translation:
lean 3 declaration is
  forall {A : CommGroupCat.{u1}} {B : CommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} CommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommGroupCat.{u1} CommGroupCat.largeCategory.{u1})) A B) [_inst_1 : CategoryTheory.Epi.{u1, succ u1} CommGroupCat.{u1} CommGroupCat.largeCategory.{u1} A B f], Eq.{succ u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroupCat.commGroupInstance.{u1} B))) (MonoidHom.range.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroupCat.commGroupInstance.{u1} B)) f) (Top.top.{u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroupCat.commGroupInstance.{u1} B))) (Subgroup.hasTop.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroupCat.commGroupInstance.{u1} B))))
but is expected to have type
  forall {A : CommGroupCat.{u1}} {B : CommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} CommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommGroupCat.{u1} instCommGroupCatLargeCategory.{u1})) A B) [_inst_1 : CategoryTheory.Epi.{u1, succ u1} CommGroupCat.{u1} instCommGroupCatLargeCategory.{u1} A B f], Eq.{succ u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} B)) (MonoidHom.range.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} B) f) (Top.top.{u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} B)) (Subgroup.instTopSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} B)))
Case conversion may be inaccurate. Consider using '#align CommGroup.range_eq_top_of_epi CommGroupCat.range_eq_top_of_epiₓ'. -/
@[to_additive]
theorem range_eq_top_of_epi [Epi f] : f.range = ⊤ :=
  MonoidHom.range_eq_top_of_cancel fun u v h =>
    (@cancel_epi _ _ _ _ _ f _ (show B ⟶ ⟨B ⧸ MonoidHom.range f⟩ from u) v).1 h
#align CommGroup.range_eq_top_of_epi CommGroupCat.range_eq_top_of_epi
#align AddCommGroup.range_eq_top_of_epi AddCommGroupCat.range_eq_top_of_epi

/- warning: CommGroup.epi_iff_range_eq_top -> CommGroupCat.epi_iff_range_eq_top is a dubious translation:
lean 3 declaration is
  forall {A : CommGroupCat.{u1}} {B : CommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} CommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommGroupCat.{u1} CommGroupCat.largeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} CommGroupCat.{u1} CommGroupCat.largeCategory.{u1} A B f) (Eq.{succ u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroupCat.commGroupInstance.{u1} B))) (MonoidHom.range.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) A) (CommGroupCat.commGroupInstance.{u1} A)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroupCat.commGroupInstance.{u1} B)) f) (Top.top.{u1} (Subgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroupCat.commGroupInstance.{u1} B))) (Subgroup.hasTop.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroup.toGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} CommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} CommGroup.{u1}) B) (CommGroupCat.commGroupInstance.{u1} B)))))
but is expected to have type
  forall {A : CommGroupCat.{u1}} {B : CommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} CommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommGroupCat.{u1} instCommGroupCatLargeCategory.{u1})) A B), Iff (CategoryTheory.Epi.{u1, succ u1} CommGroupCat.{u1} instCommGroupCatLargeCategory.{u1} A B f) (Eq.{succ u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} B)) (MonoidHom.range.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} A) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} A) (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} B) f) (Top.top.{u1} (Subgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} B)) (Subgroup.instTopSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommGroup.{u1} B) (_private.Mathlib.Algebra.Category.GroupCat.EpiMono.0.CommGroupCat.instGroupαCommGroup.{u1} B))))
Case conversion may be inaccurate. Consider using '#align CommGroup.epi_iff_range_eq_top CommGroupCat.epi_iff_range_eq_topₓ'. -/
@[to_additive]
theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  ⟨fun hf => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| MonoidHom.range_top_iff_surjective.mp hf⟩
#align CommGroup.epi_iff_range_eq_top CommGroupCat.epi_iff_range_eq_top
#align AddCommGroup.epi_iff_range_eq_top AddCommGroupCat.epi_iff_range_eq_top

/- warning: CommGroup.epi_iff_surjective -> CommGroupCat.epi_iff_surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align CommGroup.epi_iff_surjective CommGroupCat.epi_iff_surjectiveₓ'. -/
@[to_additive]
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, MonoidHom.range_top_iff_surjective]
#align CommGroup.epi_iff_surjective CommGroupCat.epi_iff_surjective
#align AddCommGroup.epi_iff_surjective AddCommGroupCat.epi_iff_surjective

#print CommGroupCat.forget_commGroupCat_preserves_mono /-
@[to_additive]
instance forget_commGroupCat_preserves_mono : (forget CommGroupCat).PreservesMonomorphisms
    where preserves X Y f e := by rwa [mono_iff_injective, ← CategoryTheory.mono_iff_injective] at e
#align CommGroup.forget_CommGroup_preserves_mono CommGroupCat.forget_commGroupCat_preserves_mono
#align AddCommGroup.forget_CommGroup_preserves_mono AddCommGroupCat.forget_commGroupCat_preserves_mono
-/

#print CommGroupCat.forget_commGroupCat_preserves_epi /-
@[to_additive]
instance forget_commGroupCat_preserves_epi : (forget CommGroupCat).PreservesEpimorphisms
    where preserves X Y f e := by rwa [epi_iff_surjective, ← CategoryTheory.epi_iff_surjective] at e
#align CommGroup.forget_CommGroup_preserves_epi CommGroupCat.forget_commGroupCat_preserves_epi
#align AddCommGroup.forget_CommGroup_preserves_epi AddCommGroupCat.forget_commGroupCat_preserves_epi
-/

end CommGroupCat

end

