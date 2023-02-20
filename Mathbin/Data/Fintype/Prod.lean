/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.prod
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Finset.Prod

/-!
# fintype instance for the product of two fintypes.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

open Finset Function

namespace Set

variable {s t : Set α}

/- warning: set.to_finset_prod -> Set.toFinset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β) [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_2 : Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t)] [_inst_3 : Fintype.{max u1 u2} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (Prod.{u1, u2} α β)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t))], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.toFinset.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t) _inst_3) (Finset.product.{u1, u2} α β (Set.toFinset.{u1} α s _inst_1) (Set.toFinset.{u2} β t _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β) [_inst_1 : Fintype.{u2} (Set.Elem.{u2} α s)] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} β t)] [_inst_3 : Fintype.{max u2 u1} (Set.Elem.{max u2 u1} (Prod.{u2, u1} α β) (Set.prod.{u2, u1} α β s t))], Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Prod.{u2, u1} α β)) (Set.toFinset.{max u2 u1} (Prod.{u2, u1} α β) (Set.prod.{u2, u1} α β s t) _inst_3) (Finset.product.{u2, u1} α β (Set.toFinset.{u2} α s _inst_1) (Set.toFinset.{u1} β t _inst_2))
Case conversion may be inaccurate. Consider using '#align set.to_finset_prod Set.toFinset_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem toFinset_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s ×ˢ t)] :
    (s ×ˢ t).toFinset = s.toFinset ×ˢ t.toFinset :=
  by
  ext
  simp
#align set.to_finset_prod Set.toFinset_prod

#print Set.toFinset_off_diag /-
theorem toFinset_off_diag {s : Set α} [DecidableEq α] [Fintype s] [Fintype s.offDiag] :
    s.offDiag.toFinset = s.toFinset.offDiag :=
  Finset.ext <| by simp
#align set.to_finset_off_diag Set.toFinset_off_diag
-/

end Set

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance (α β : Type _) [Fintype α] [Fintype β] : Fintype (α × β) :=
  ⟨univ ×ˢ univ, fun ⟨a, b⟩ => by simp⟩

/- warning: finset.univ_product_univ -> Finset.univ_product_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β (Finset.univ.{u1} α _inst_1) (Finset.univ.{u2} β _inst_2)) (Finset.univ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.fintype.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β (Finset.univ.{u2} α _inst_1) (Finset.univ.{u1} β _inst_2)) (Finset.univ.{max u2 u1} (Prod.{u2, u1} α β) (instFintypeProd.{u2, u1} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align finset.univ_product_univ Finset.univ_product_univₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Finset.univ_product_univ {α β : Type _} [Fintype α] [Fintype β] :
    (univ : Finset α) ×ˢ (univ : Finset β) = univ :=
  rfl
#align finset.univ_product_univ Finset.univ_product_univ

/- warning: fintype.card_prod -> Fintype.card_prod is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], Eq.{1} Nat (Fintype.card.{max u1 u2} (Prod.{u1, u2} α β) (Prod.fintype.{u1, u2} α β _inst_1 _inst_2)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], Eq.{1} Nat (Fintype.card.{max u1 u2} (Prod.{u2, u1} α β) (instFintypeProd.{u2, u1} α β _inst_1 _inst_2)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_prod Fintype.card_prodₓ'. -/
@[simp]
theorem Fintype.card_prod (α β : Type _) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β :=
  card_product _ _
#align fintype.card_prod Fintype.card_prod

section

open Classical

#print infinite_prod /-
@[simp]
theorem infinite_prod : Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ Infinite β :=
  by
  refine'
    ⟨fun H => _, fun H =>
      H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [and_comm]; contrapose! H; intro H'
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  haveI := fintypeOfNotInfinite (H.1 ⟨b⟩); haveI := fintypeOfNotInfinite (H.2 ⟨a⟩)
  exact H'.false
#align infinite_prod infinite_prod
-/

#print Pi.infinite_of_left /-
instance Pi.infinite_of_left {ι : Sort _} {π : ι → Sort _} [∀ i, Nontrivial <| π i] [Infinite ι] :
    Infinite (∀ i : ι, π i) :=
  by
  choose m n hm using fun i => exists_pair_ne (π i)
  refine'
    Infinite.of_injective (fun i => m.update i (n i)) fun x y h => Classical.not_not.1 fun hne => _
  simp_rw [update_eq_iff, update_noteq hne] at h
  exact (hm x h.1.symm).elim
#align pi.infinite_of_left Pi.infinite_of_left
-/

/- warning: pi.infinite_of_exists_right -> Pi.infinite_of_exists_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} (i : ι) [_inst_1 : Infinite.{succ u2} (π i)] [_inst_2 : forall (i : ι), Nonempty.{succ u2} (π i)], Infinite.{max (succ u1) (succ u2)} (forall (i : ι), π i)
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} (i : ι) [_inst_1 : Infinite.{succ u1} (π i)] [_inst_2 : forall (i : ι), Nonempty.{succ u1} (π i)], Infinite.{max (succ u2) (succ u1)} (forall (i : ι), π i)
Case conversion may be inaccurate. Consider using '#align pi.infinite_of_exists_right Pi.infinite_of_exists_rightₓ'. -/
/-- If at least one `π i` is infinite and the rest nonempty, the pi type of all `π` is infinite. -/
theorem Pi.infinite_of_exists_right {ι : Type _} {π : ι → Type _} (i : ι) [Infinite <| π i]
    [∀ i, Nonempty <| π i] : Infinite (∀ i : ι, π i) :=
  let ⟨m⟩ := @Pi.nonempty ι π _
  Infinite.of_injective _ (update_injective m i)
#align pi.infinite_of_exists_right Pi.infinite_of_exists_right

#print Pi.infinite_of_right /-
/-- See `pi.infinite_of_exists_right` for the case that only one `π i` is infinite. -/
instance Pi.infinite_of_right {ι : Sort _} {π : ι → Sort _} [∀ i, Infinite <| π i] [Nonempty ι] :
    Infinite (∀ i : ι, π i) :=
  Pi.infinite_of_exists_right (Classical.arbitrary ι)
#align pi.infinite_of_right Pi.infinite_of_right
-/

#print Function.infinite_of_left /-
/-- Non-dependent version of `pi.infinite_of_left`. -/
instance Function.infinite_of_left {ι π : Sort _} [Nontrivial π] [Infinite ι] : Infinite (ι → π) :=
  Pi.infinite_of_left
#align function.infinite_of_left Function.infinite_of_left
-/

#print Function.infinite_of_right /-
/-- Non-dependent version of `pi.infinite_of_exists_right` and `pi.infinite_of_right`. -/
instance Function.infinite_of_right {ι π : Sort _} [Infinite π] [Nonempty ι] : Infinite (ι → π) :=
  Pi.infinite_of_right
#align function.infinite_of_right Function.infinite_of_right
-/

end

