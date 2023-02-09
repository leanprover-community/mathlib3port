/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.option
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Finset.Option

/-!
# fintype instances for option

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

open Finset Function

instance {α : Type _} [Fintype α] : Fintype (Option α) :=
  ⟨univ.insertNone, fun a => by simp⟩

/- warning: univ_option -> univ_option is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} (Option.{u1} α)) (Finset.univ.{u1} (Option.{u1} α) (Option.fintype.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))))) (fun (_x : RelEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) => (Finset.{u1} α) -> (Finset.{u1} (Option.{u1} α))) (RelEmbedding.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) (Finset.insertNone.{u1} α) (Finset.univ.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} (Option.{u1} α)) (Finset.univ.{u1} (Option.{u1} α) (instFintypeOption.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)))) (RelEmbedding.toEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u1} (Option.{u1} α)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u1} (Option.{u1} α)) => LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.insertNone.{u1} α)) (Finset.univ.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align univ_option univ_optionₓ'. -/
theorem univ_option (α : Type _) [Fintype α] : (univ : Finset (Option α)) = insertNone univ :=
  rfl
#align univ_option univ_option

/- warning: fintype.card_option -> Fintype.card_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{1} Nat (Fintype.card.{u1} (Option.{u1} α) (Option.fintype.{u1} α _inst_1)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Fintype.card.{u1} α _inst_1) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{1} Nat (Fintype.card.{u1} (Option.{u1} α) (instFintypeOption.{u1} α _inst_1)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fintype.card.{u1} α _inst_1) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align fintype.card_option Fintype.card_optionₓ'. -/
@[simp]
theorem Fintype.card_option {α : Type _} [Fintype α] :
    Fintype.card (Option α) = Fintype.card α + 1 :=
  (Finset.card_cons _).trans <| congr_arg₂ _ (card_map _) rfl
#align fintype.card_option Fintype.card_option

#print fintypeOfOption /-
/-- If `option α` is a `fintype` then so is `α` -/
def fintypeOfOption {α : Type _} [Fintype (Option α)] : Fintype α :=
  ⟨Finset.eraseNone (Fintype.elems (Option α)), fun x =>
    mem_eraseNone.mpr (Fintype.complete (some x))⟩
#align fintype_of_option fintypeOfOption
-/

#print fintypeOfOptionEquiv /-
/-- A type is a `fintype` if its successor (using `option`) is a `fintype`. -/
def fintypeOfOptionEquiv [Fintype α] (f : α ≃ Option β) : Fintype β :=
  haveI := Fintype.ofEquiv _ f
  fintypeOfOption
#align fintype_of_option_equiv fintypeOfOptionEquiv
-/

namespace Fintype

#print Fintype.truncRecEmptyOption /-
/-- A recursor principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
def truncRecEmptyOption {P : Type u → Sort v} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
    (h_empty : P PEmpty) (h_option : ∀ {α} [Fintype α] [DecidableEq α], P α → P (Option α))
    (α : Type u) [Fintype α] [DecidableEq α] : Trunc (P α) :=
  by
  suffices ∀ n : ℕ, Trunc (P (ULift <| Fin n))
    by
    apply Trunc.bind (this (Fintype.card α))
    intro h
    apply Trunc.map _ (Fintype.truncEquivFin α)
    intro e
    exact of_equiv (equiv.ulift.trans e.symm) h
  intro n
  induction' n with n ih
  · have : card PEmpty = card (ULift (Fin 0)) := by simp only [card_fin, card_pempty, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.mk
    refine' of_equiv e h_empty
  · have : card (Option (ULift (Fin n))) = card (ULift (Fin n.succ)) := by
      simp only [card_fin, card_option, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.map _ ih
    intro ih
    refine' of_equiv e (h_option ih)
#align fintype.trunc_rec_empty_option Fintype.truncRecEmptyOption
-/

/- warning: fintype.induction_empty_option -> Fintype.induction_empty_option is a dubious translation:
lean 3 declaration is
  forall {P : forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α], Prop}, (forall (α : Type.{u1}) (β : Type.{u1}) [_inst_2 : Fintype.{u1} β] (e : Equiv.{succ u1, succ u1} α β), (P α (Fintype.ofEquiv.{u1, u1} α β _inst_2 (Equiv.symm.{succ u1, succ u1} α β e))) -> (P β _inst_2)) -> (P PEmpty.{succ u1} (Fintype.ofIsEmpty.{u1} PEmpty.{succ u1} PEmpty.isEmpty.{succ u1})) -> (forall (α : Type.{u1}) [_inst_3 : Fintype.{u1} α], (P α _inst_3) -> (P (Option.{u1} α) (Option.fintype.{u1} α _inst_3))) -> (forall (α : Type.{u1}) [_inst_4 : Fintype.{u1} α], P α _inst_4)
but is expected to have type
  forall {P : forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α], Prop}, (forall (α : Type.{u1}) (β : Type.{u1}) [_inst_2 : Fintype.{u1} β] (e : Equiv.{succ u1, succ u1} α β), (P α (Fintype.ofEquiv.{u1, u1} α β _inst_2 (Equiv.symm.{succ u1, succ u1} α β e))) -> (P β _inst_2)) -> (P PEmpty.{succ u1} (Fintype.ofIsEmpty.{u1} PEmpty.{succ u1} instIsEmptyPEmpty.{succ u1})) -> (forall (α : Type.{u1}) [_inst_3 : Fintype.{u1} α], (P α _inst_3) -> (P (Option.{u1} α) (instFintypeOption.{u1} α _inst_3))) -> (forall (α : Type.{u1}) [_inst_4 : Fintype.{u1} α], P α _inst_4)
Case conversion may be inaccurate. Consider using '#align fintype.induction_empty_option Fintype.induction_empty_optionₓ'. -/
/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
@[elab_as_elim]
theorem induction_empty_option {P : ∀ (α : Type u) [Fintype α], Prop}
    (of_equiv : ∀ (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.ofEquiv α β ‹_› e.symm) → @P β ‹_›)
    (h_empty : P PEmpty) (h_option : ∀ (α) [Fintype α], P α → P (Option α)) (α : Type u)
    [Fintype α] : P α :=
  by
  obtain ⟨p⟩ :=
    @trunc_rec_empty_option (fun α => ∀ h, @P α h) (fun α β e hα hβ => @of_equiv α β hβ e (hα _))
      (fun _i => by convert h_empty) _ α _ (Classical.decEq α)
  · exact p _
  · rintro α hα - Pα hα'
    skip
    convert h_option α (Pα _)
#align fintype.induction_empty_option Fintype.induction_empty_option

end Fintype

#print Finite.induction_empty_option /-
/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
theorem Finite.induction_empty_option {P : Type u → Prop} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
    (h_empty : P PEmpty) (h_option : ∀ {α} [Fintype α], P α → P (Option α)) (α : Type u)
    [Finite α] : P α := by
  cases nonempty_fintype α
  refine' Fintype.induction_empty_option _ _ _ α
  exacts[fun α β _ => of_equiv, h_empty, @h_option]
#align finite.induction_empty_option Finite.induction_empty_option
-/

