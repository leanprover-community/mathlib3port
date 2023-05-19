/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.skolem
! leanprover-community/mathlib commit dbdf71cee7bb20367cb7e37279c08b0c218cf967
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.ElementaryMaps

/-!
# Skolem Functions and Downward Löwenheim–Skolem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main Definitions
* `first_order.language.skolem₁` is a language consisting of Skolem functions for another language.

## Main Results
* `first_order.language.exists_elementary_substructure_card_eq` is the Downward Löwenheim–Skolem
  theorem: If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.

## TODO
* Use `skolem₁` recursively to construct an actual Skolemization of a language.

-/


universe u v w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

open Cardinal

variable (L : Language.{u, v}) {M : Type w} [Nonempty M] [L.Structure M]

#print FirstOrder.Language.skolem₁ /-
/-- A language consisting of Skolem functions for another language.
Called `skolem₁` because it is the first step in building a Skolemization of a language. -/
@[simps]
def skolem₁ : Language :=
  ⟨fun n => L.BoundedFormula Empty (n + 1), fun _ => Empty⟩
#align first_order.language.skolem₁ FirstOrder.Language.skolem₁
-/

variable {L}

#print FirstOrder.Language.card_functions_sum_skolem₁ /-
theorem card_functions_sum_skolem₁ :
    (#Σn, (L.Sum L.skolem₁).Functions n) = (#Σn, L.BoundedFormula Empty (n + 1)) :=
  by
  simp only [card_functions_sum, skolem₁_functions, lift_id', mk_sigma, sum_add_distrib']
  rw [add_comm, add_eq_max, max_eq_left]
  · refine' sum_le_sum _ _ fun n => _
    rw [← lift_le, lift_lift, lift_mk_le]
    refine' ⟨⟨fun f => (func f default).bdEqual (func f default), fun f g h => _⟩⟩
    rcases h with ⟨rfl, ⟨rfl⟩⟩
    rfl
  · rw [← mk_sigma]
    exact infinite_iff.1 (Infinite.of_injective (fun n => ⟨n, ⊥⟩) fun x y xy => (Sigma.mk.inj xy).1)
#align first_order.language.card_functions_sum_skolem₁ FirstOrder.Language.card_functions_sum_skolem₁
-/

/- warning: first_order.language.card_functions_sum_skolem₁_le -> FirstOrder.Language.card_functions_sum_skolem₁_le is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}}, LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.mk.{max u1 u2} (Sigma.{0, max u1 u2} Nat (fun (n : Nat) => FirstOrder.Language.Functions.{max u1 u2, u2} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) n))) (LinearOrder.max.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.linearOrder.{max u1 u2} Cardinal.aleph0.{max u1 u2} (FirstOrder.Language.card.{u1, u2} L))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}}, LE.le.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instLECardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (Sigma.{0, max u1 u2} Nat (fun (n : Nat) => FirstOrder.Language.Functions.{max u1 u2, u2} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) n))) (Max.max.{succ (max u1 u2)} Cardinal.{max u1 u2} (CanonicallyLinearOrderedAddMonoid.toMax.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) Cardinal.aleph0.{max u1 u2} (FirstOrder.Language.card.{u1, u2} L))
Case conversion may be inaccurate. Consider using '#align first_order.language.card_functions_sum_skolem₁_le FirstOrder.Language.card_functions_sum_skolem₁_leₓ'. -/
theorem card_functions_sum_skolem₁_le : (#Σn, (L.Sum L.skolem₁).Functions n) ≤ max ℵ₀ L.card :=
  by
  rw [card_functions_sum_skolem₁]
  trans #Σn, L.bounded_formula Empty n
  ·
    exact
      ⟨⟨Sigma.map Nat.succ fun _ => id,
          nat.succ_injective.sigma_map fun _ => Function.injective_id⟩⟩
  · refine' trans bounded_formula.card_le (lift_le.1 _)
    simp only [mk_empty, lift_zero, lift_uzero, zero_add]
#align first_order.language.card_functions_sum_skolem₁_le FirstOrder.Language.card_functions_sum_skolem₁_le

#print FirstOrder.Language.skolem₁Structure /-
/-- The structure assigning each function symbol of `L.skolem₁` to a skolem function generated with
choice. -/
noncomputable instance skolem₁Structure : L.skolem₁.Structure M :=
  ⟨fun n φ x => Classical.epsilon fun a => φ.realize default (Fin.snoc x a : _ → M), fun _ r =>
    Empty.elim r⟩
#align first_order.language.skolem₁_Structure FirstOrder.Language.skolem₁Structure
-/

namespace Substructure

/- warning: first_order.language.substructure.skolem₁_reduct_is_elementary -> FirstOrder.Language.Substructure.skolem₁_reduct_isElementary is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : Nonempty.{succ u3} M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u3} L M] (S : FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))), FirstOrder.Language.Substructure.IsElementary.{u1, u2, u3} L M _inst_2 (coeFn.{succ u3, succ u3} (OrderEmbedding.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (Preorder.toHasLe.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (SetLike.partialOrder.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) M (FirstOrder.Language.Substructure.instSetLike.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2)))))) (Preorder.toHasLe.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (SetLike.partialOrder.{u3, u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) M (FirstOrder.Language.Substructure.instSetLike.{u1, u2, u3} L M _inst_2))))) (fun (_x : RelEmbedding.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (LE.le.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (Preorder.toHasLe.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (SetLike.partialOrder.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) M (FirstOrder.Language.Substructure.instSetLike.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))))))) (LE.le.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (Preorder.toHasLe.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (SetLike.partialOrder.{u3, u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) M (FirstOrder.Language.Substructure.instSetLike.{u1, u2, u3} L M _inst_2)))))) => (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) -> (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2)) (RelEmbedding.hasCoeToFun.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (LE.le.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (Preorder.toHasLe.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (SetLike.partialOrder.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) M (FirstOrder.Language.Substructure.instSetLike.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))))))) (LE.le.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (Preorder.toHasLe.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (SetLike.partialOrder.{u3, u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) M (FirstOrder.Language.Substructure.instSetLike.{u1, u2, u3} L M _inst_2)))))) (FirstOrder.Language.LHom.substructureReduct.{u1, u2, u3, max u1 u2, u2} L M _inst_2 (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2)) (FirstOrder.Language.LHom.sumInl.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) (FirstOrder.Language.LHom.sumInl_isExpansionOn.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) S)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : Nonempty.{succ u3} M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u3} L M] (S : FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))), FirstOrder.Language.Substructure.IsElementary.{u1, u2, u3} L M _inst_2 (FunLike.coe.{succ u3, succ u3, succ u3} (OrderEmbedding.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (Preorder.toLE.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (CompleteSemilatticeInf.toPartialOrder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (CompleteLattice.toCompleteSemilatticeInf.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.instCompleteLattice.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))))))) (Preorder.toLE.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (FirstOrder.Language.Substructure.instCompleteLattice.{u1, u2, u3} L M _inst_2)))))) (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (fun (_x : FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) => FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) _x) (RelHomClass.toFunLike.{u3, u3, u3} (OrderEmbedding.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (Preorder.toLE.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (CompleteSemilatticeInf.toPartialOrder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (CompleteLattice.toCompleteSemilatticeInf.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.instCompleteLattice.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))))))) (Preorder.toLE.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (FirstOrder.Language.Substructure.instCompleteLattice.{u1, u2, u3} L M _inst_2)))))) (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) => LE.le.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (Preorder.toLE.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (CompleteSemilatticeInf.toPartialOrder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (CompleteLattice.toCompleteSemilatticeInf.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.instCompleteLattice.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))))))) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) => LE.le.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (Preorder.toLE.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (FirstOrder.Language.Substructure.instCompleteLattice.{u1, u2, u3} L M _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u3, u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) => LE.le.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (Preorder.toLE.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (CompleteSemilatticeInf.toPartialOrder.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (CompleteLattice.toCompleteSemilatticeInf.{u3} (FirstOrder.Language.Substructure.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) (FirstOrder.Language.Substructure.instCompleteLattice.{max u1 u2, u2, u3} (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) M (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))))))) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) => LE.le.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (Preorder.toLE.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (PartialOrder.toPreorder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (FirstOrder.Language.Substructure.{u1, u2, u3} L M _inst_2) (FirstOrder.Language.Substructure.instCompleteLattice.{u1, u2, u3} L M _inst_2))))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (FirstOrder.Language.LHom.substructureReduct.{u1, u2, u3, max u1 u2, u2} L M _inst_2 (FirstOrder.Language.sum.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) (FirstOrder.Language.sumStructure.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2)) (FirstOrder.Language.LHom.sumInl.{u1, u2, max u1 u2, 0} L (FirstOrder.Language.skolem₁.{u1, u2} L)) (FirstOrder.Language.LHom.sumInl_isExpansionOn.{u1, u2, max u1 u2, 0, u3} L (FirstOrder.Language.skolem₁.{u1, u2} L) M _inst_2 (FirstOrder.Language.skolem₁Structure.{u1, u2, u3} L M _inst_1 _inst_2))) S)
Case conversion may be inaccurate. Consider using '#align first_order.language.substructure.skolem₁_reduct_is_elementary FirstOrder.Language.Substructure.skolem₁_reduct_isElementaryₓ'. -/
theorem skolem₁_reduct_isElementary (S : (L.Sum L.skolem₁).Substructure M) :
    (LHom.sumInl.substructureReduct S).IsElementary :=
  by
  apply (Lhom.sum_inl.substructure_reduct S).isElementary_of_exists
  intro n φ x a h
  let φ' : (L.sum L.skolem₁).Functions n := Lhom.sum_inr.on_function φ
  exact
    ⟨⟨fun_map φ' (coe ∘ x), S.fun_mem (Lhom.sum_inr.on_function φ) (coe ∘ x) fun i => (x i).2⟩,
      Classical.epsilon_spec ⟨a, h⟩⟩
#align first_order.language.substructure.skolem₁_reduct_is_elementary FirstOrder.Language.Substructure.skolem₁_reduct_isElementary

#print FirstOrder.Language.Substructure.elementarySkolem₁Reduct /-
/-- Any `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
noncomputable def elementarySkolem₁Reduct (S : (L.Sum L.skolem₁).Substructure M) :
    L.ElementarySubstructure M :=
  ⟨LHom.sumInl.substructureReduct S, S.skolem₁_reduct_isElementary⟩
#align first_order.language.substructure.elementary_skolem₁_reduct FirstOrder.Language.Substructure.elementarySkolem₁Reduct
-/

#print FirstOrder.Language.Substructure.coeSort_elementarySkolem₁Reduct /-
theorem coeSort_elementarySkolem₁Reduct (S : (L.Sum L.skolem₁).Substructure M) :
    (S.elementarySkolem₁Reduct : Type w) = S :=
  rfl
#align first_order.language.substructure.coe_sort_elementary_skolem₁_reduct FirstOrder.Language.Substructure.coeSort_elementarySkolem₁Reduct
-/

end Substructure

open Substructure

variable (L) (M)

instance : Small (⊥ : (L.Sum L.skolem₁).Substructure M).elementarySkolem₁Reduct :=
  by
  rw [coe_sort_elementary_skolem₁_reduct]
  infer_instance

#print FirstOrder.Language.exists_small_elementarySubstructure /-
theorem exists_small_elementarySubstructure : ∃ S : L.ElementarySubstructure M, Small.{max u v} S :=
  ⟨Substructure.elementarySkolem₁Reduct ⊥, inferInstance⟩
#align first_order.language.exists_small_elementary_substructure FirstOrder.Language.exists_small_elementarySubstructure
-/

variable {M}

#print FirstOrder.Language.exists_elementarySubstructure_card_eq /-
/-- The Downward Löwenheim–Skolem theorem :
  If `s` is a set in an `L`-structure `M` and `κ` an infinite cardinal such that
  `max (# s, L.card) ≤ κ` and `κ ≤ # M`, then `M` has an elementary substructure containing `s` of
  cardinality `κ`.  -/
theorem exists_elementarySubstructure_card_eq (s : Set M) (κ : Cardinal.{w'}) (h1 : ℵ₀ ≤ κ)
    (h2 : Cardinal.lift.{w'} (#s) ≤ Cardinal.lift.{w} κ)
    (h3 : Cardinal.lift.{w'} L.card ≤ Cardinal.lift.{max u v} κ)
    (h4 : Cardinal.lift.{w} κ ≤ Cardinal.lift.{w'} (#M)) :
    ∃ S : L.ElementarySubstructure M, s ⊆ S ∧ Cardinal.lift.{w'} (#S) = Cardinal.lift.{w} κ :=
  by
  obtain ⟨s', hs'⟩ := Cardinal.le_mk_iff_exists_set.1 h4
  rw [← aleph_0_le_lift] at h1
  rw [← hs'] at *
  refine'
    ⟨elementary_skolem₁_reduct (closure (L.sum L.skolem₁) (s ∪ Equiv.ulift '' s')),
      (s.subset_union_left _).trans subset_closure, _⟩
  have h := mk_image_eq_lift _ s' equiv.ulift.injective
  rw [lift_umax, lift_id'] at h
  rw [coe_sort_elementary_skolem₁_reduct, ← h, lift_inj]
  refine'
    le_antisymm (lift_le.1 (lift_card_closure_le.trans _))
      (mk_le_mk_of_subset ((Set.subset_union_right _ _).trans subset_closure))
  rw [max_le_iff, aleph_0_le_lift, ← aleph_0_le_lift, h, add_eq_max, max_le_iff, lift_le]
  refine' ⟨h1, (mk_union_le _ _).trans _, (lift_le.2 card_functions_sum_skolem₁_le).trans _⟩
  · rw [← lift_le, lift_add, h, add_comm, add_eq_max h1]
    exact max_le le_rfl h2
  · rw [lift_max, lift_aleph_0, max_le_iff, aleph_0_le_lift, and_comm', ← lift_le.{_, w'},
      lift_lift, lift_lift, ← aleph_0_le_lift, h]
    refine' ⟨_, h1⟩
    simp only [← lift_lift, lift_umax, lift_umax']
    rw [lift_lift, ← lift_lift.{w', w} L.card]
    refine' trans (lift_le.{_, w}.2 h3) _
    rw [lift_lift, ← lift_lift.{w, max u v}, ← hs', ← h, lift_lift, lift_lift, lift_lift]
  · refine' trans _ (lift_le.2 (mk_le_mk_of_subset (Set.subset_union_right _ _)))
    rw [aleph_0_le_lift, ← aleph_0_le_lift, h]
    exact h1
#align first_order.language.exists_elementary_substructure_card_eq FirstOrder.Language.exists_elementarySubstructure_card_eq
-/

end Language

end FirstOrder

