/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module set_theory.cardinal.finite
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Defs
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Finite Cardinality Functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main Definitions

* `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`.
* `part_enat.card α` is the cardinality of `α` as an extended natural number
  (`part ℕ` implementation). If `α` is infinite, `part_enat.card α = ⊤`.
-/


open Cardinal

noncomputable section

open BigOperators

variable {α β : Type _}

namespace Nat

#print Nat.card /-
/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
protected def card (α : Type _) : ℕ :=
  (mk α).toNat
#align nat.card Nat.card
-/

#print Nat.card_eq_fintype_card /-
@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_toNat_eq_card
#align nat.card_eq_fintype_card Nat.card_eq_fintype_card
-/

#print Nat.card_eq_zero_of_infinite /-
@[simp]
theorem card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 :=
  mk_toNat_of_infinite
#align nat.card_eq_zero_of_infinite Nat.card_eq_zero_of_infinite
-/

#print Nat.finite_of_card_ne_zero /-
theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α :=
  not_infinite_iff_finite.mp <| h ∘ @Nat.card_eq_zero_of_infinite α
#align nat.finite_of_card_ne_zero Nat.finite_of_card_ne_zero
-/

/- warning: nat.card_congr -> Nat.card_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (Equiv.{succ u1, succ u2} α β) -> (Eq.{1} Nat (Nat.card.{u1} α) (Nat.card.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, (Equiv.{succ u2, succ u1} α β) -> (Eq.{1} Nat (Nat.card.{u2} α) (Nat.card.{u1} β))
Case conversion may be inaccurate. Consider using '#align nat.card_congr Nat.card_congrₓ'. -/
theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  Cardinal.toNat_congr f
#align nat.card_congr Nat.card_congr

/- warning: nat.card_eq_of_bijective -> Nat.card_eq_of_bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), (Function.Bijective.{succ u1, succ u2} α β f) -> (Eq.{1} Nat (Nat.card.{u1} α) (Nat.card.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), (Function.Bijective.{succ u2, succ u1} α β f) -> (Eq.{1} Nat (Nat.card.{u2} α) (Nat.card.{u1} β))
Case conversion may be inaccurate. Consider using '#align nat.card_eq_of_bijective Nat.card_eq_of_bijectiveₓ'. -/
theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)
#align nat.card_eq_of_bijective Nat.card_eq_of_bijective

#print Nat.card_eq_of_equiv_fin /-
theorem card_eq_of_equiv_fin {α : Type _} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by
  simpa using card_congr f
#align nat.card_eq_of_equiv_fin Nat.card_eq_of_equiv_fin
-/

#print Nat.equivFinOfCardPos /-
/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `fin (nat.card α)`. See also `finite.equiv_fin`. -/
def equivFinOfCardPos {α : Type _} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) :=
  by
  cases fintypeOrInfinite α
  · simpa using Fintype.equivFin α
  · simpa using h
#align nat.equiv_fin_of_card_pos Nat.equivFinOfCardPos
-/

#print Nat.card_of_subsingleton /-
theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 :=
  by
  letI := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card, Fintype.card_ofSubsingleton a]
#align nat.card_of_subsingleton Nat.card_of_subsingleton
-/

#print Nat.card_unique /-
@[simp]
theorem card_unique [Unique α] : Nat.card α = 1 :=
  card_of_subsingleton default
#align nat.card_unique Nat.card_unique
-/

#print Nat.card_eq_one_iff_unique /-
theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  Cardinal.toNat_eq_one_iff_unique
#align nat.card_eq_one_iff_unique Nat.card_eq_one_iff_unique
-/

#print Nat.card_eq_two_iff /-
theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α :=
  (toNat_eq_iff two_ne_zero).trans <| Iff.trans (by rw [Nat.cast_two]) mk_eq_two_iff
#align nat.card_eq_two_iff Nat.card_eq_two_iff
-/

#print Nat.card_eq_two_iff' /-
theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x :=
  (toNat_eq_iff two_ne_zero).trans <| Iff.trans (by rw [Nat.cast_two]) (mk_eq_two_iff' x)
#align nat.card_eq_two_iff' Nat.card_eq_two_iff'
-/

#print Nat.card_of_isEmpty /-
theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp
#align nat.card_of_is_empty Nat.card_of_isEmpty
-/

/- warning: nat.card_prod -> Nat.card_prod is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), Eq.{1} Nat (Nat.card.{max u1 u2} (Prod.{u1, u2} α β)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Nat.card.{u1} α) (Nat.card.{u2} β))
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}), Eq.{1} Nat (Nat.card.{max u1 u2} (Prod.{u2, u1} α β)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Nat.card.{u2} α) (Nat.card.{u1} β))
Case conversion may be inaccurate. Consider using '#align nat.card_prod Nat.card_prodₓ'. -/
@[simp]
theorem card_prod (α β : Type _) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp only [Nat.card, mk_prod, to_nat_mul, to_nat_lift]
#align nat.card_prod Nat.card_prod

/- warning: nat.card_ulift -> Nat.card_uLift is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), Eq.{1} Nat (Nat.card.{max u1 u2} (ULift.{u2, u1} α)) (Nat.card.{u1} α)
but is expected to have type
  forall (α : Type.{u2}), Eq.{1} Nat (Nat.card.{max u2 u1} (ULift.{u1, u2} α)) (Nat.card.{u2} α)
Case conversion may be inaccurate. Consider using '#align nat.card_ulift Nat.card_uLiftₓ'. -/
@[simp]
theorem card_uLift (α : Type _) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift
#align nat.card_ulift Nat.card_uLift

#print Nat.card_pLift /-
@[simp]
theorem card_pLift (α : Type _) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift
#align nat.card_plift Nat.card_pLift
-/

#print Nat.card_pi /-
theorem card_pi {β : α → Type _} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, to_nat_lift, to_nat_finset_prod]
#align nat.card_pi Nat.card_pi
-/

/- warning: nat.card_fun -> Nat.card_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u1} α], Eq.{1} Nat (Nat.card.{max u1 u2} (α -> β)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (Nat.card.{u2} β) (Nat.card.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Finite.{succ u2} α], Eq.{1} Nat (Nat.card.{max u2 u1} (α -> β)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (Nat.card.{u1} β) (Nat.card.{u2} α))
Case conversion may be inaccurate. Consider using '#align nat.card_fun Nat.card_funₓ'. -/
theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α :=
  by
  haveI := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
#align nat.card_fun Nat.card_fun

#print Nat.card_zMod /-
@[simp]
theorem card_zMod (n : ℕ) : Nat.card (ZMod n) = n :=
  by
  cases n
  · exact Nat.card_eq_zero_of_infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]
#align nat.card_zmod Nat.card_zMod
-/

end Nat

namespace PartENat

#print PartENat.card /-
/-- `part_enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `part_enat.card α = ⊤`. -/
def card (α : Type _) : PartENat :=
  (mk α).toPartENat
#align part_enat.card PartENat.card
-/

/- warning: part_enat.card_eq_coe_fintype_card -> PartENat.card_eq_coe_fintype_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{1} PartENat (PartENat.card.{u1} α) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{1} PartENat (PartENat.card.{u1} α) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) (Fintype.card.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align part_enat.card_eq_coe_fintype_card PartENat.card_eq_coe_fintype_cardₓ'. -/
@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α :=
  mk_toPartENat_eq_coe_card
#align part_enat.card_eq_coe_fintype_card PartENat.card_eq_coe_fintype_card

#print PartENat.card_eq_top_of_infinite /-
@[simp]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ :=
  mk_toPartENat_of_infinite
#align part_enat.card_eq_top_of_infinite PartENat.card_eq_top_of_infinite
-/

end PartENat

