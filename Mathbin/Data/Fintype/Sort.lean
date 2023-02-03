/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.sort
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Sort
import Mathbin.Data.Fintype.Basic

/-!
# Sorting a finite type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides two equivalences for linearly ordered fintypes:
* `mono_equiv_of_fin`: Order isomorphism between `α` and `fin (card α)`.
* `fin_sum_equiv_of_finset`: Equivalence between `α` and `fin m ⊕ fin n` where `m` and `n` are
  respectively the cardinalities of some `finset α` and its complement.
-/


open Finset

#print monoEquivOfFin /-
/-- Given a linearly ordered fintype `α` of cardinal `k`, the order isomorphism
`mono_equiv_of_fin α h` is the increasing bijection between `fin k` and `α`. Here, `h` is a proof
that the cardinality of `α` is `k`. We use this instead of an isomorphism `fin (card α) ≃o α` to
avoid casting issues in further uses of this function. -/
def monoEquivOfFin (α : Type _) [Fintype α] [LinearOrder α] {k : ℕ} (h : Fintype.card α = k) :
    Fin k ≃o α :=
  (univ.orderIsoOfFin h).trans <| (OrderIso.setCongr _ _ coe_univ).trans OrderIso.Set.univ
#align mono_equiv_of_fin monoEquivOfFin
-/

variable {α : Type _} [DecidableEq α] [Fintype α] [LinearOrder α] {m n : ℕ} {s : Finset α}

/- warning: fin_sum_equiv_of_finset -> finSumEquivOfFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : LinearOrder.{u1} α] {m : Nat} {n : Nat} {s : Finset.{u1} α}, (Eq.{1} Nat (Finset.card.{u1} α s) m) -> (Eq.{1} Nat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s)) n) -> (Equiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : LinearOrder.{u1} α] {m : Nat} {n : Nat} {s : Finset.{u1} α}, (Eq.{1} Nat (Finset.card.{u1} α s) m) -> (Eq.{1} Nat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s)) n) -> (Equiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α)
Case conversion may be inaccurate. Consider using '#align fin_sum_equiv_of_finset finSumEquivOfFinsetₓ'. -/
/-- If `α` is a linearly ordered fintype, `s : finset α` has cardinality `m` and its complement has
cardinality `n`, then `fin m ⊕ fin n ≃ α`. The equivalence sends elements of `fin m` to
elements of `s` and elements of `fin n` to elements of `sᶜ` while preserving order on each
"half" of `fin m ⊕ fin n` (using `set.order_iso_of_fin`). -/
def finSumEquivOfFinset (hm : s.card = m) (hn : sᶜ.card = n) : Sum (Fin m) (Fin n) ≃ α :=
  calc
    Sum (Fin m) (Fin n) ≃ Sum (s : Set α) (sᶜ : Set α) :=
      Equiv.sumCongr (s.orderIsoOfFin hm).toEquiv <|
        (sᶜ.orderIsoOfFin hn).toEquiv.trans <| Equiv.Set.ofEq s.coe_compl
    _ ≃ α := Equiv.Set.sumCompl _
    
#align fin_sum_equiv_of_finset finSumEquivOfFinset

/- warning: fin_sum_equiv_of_finset_inl -> finSumEquivOfFinset_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : LinearOrder.{u1} α] {m : Nat} {n : Nat} {s : Finset.{u1} α} (hm : Eq.{1} Nat (Finset.card.{u1} α s) m) (hn : Eq.{1} Nat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s)) n) (i : Fin m), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) (fun (_x : Equiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) => (Sum.{0, 0} (Fin m) (Fin n)) -> α) (Equiv.hasCoeToFun.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) (finSumEquivOfFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 m n s hm hn) (Sum.inl.{0, 0} (Fin m) (Fin n) i)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{0, u1} (Fin m) α (Fin.hasLe m) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_3)))))) (fun (_x : RelEmbedding.{0, u1} (Fin m) α (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_3))))))) => (Fin m) -> α) (RelEmbedding.hasCoeToFun.{0, u1} (Fin m) α (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_3))))))) (Finset.orderEmbOfFin.{u1} α _inst_3 s m hm) i)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : LinearOrder.{u1} α] {m : Nat} {n : Nat} {s : Finset.{u1} α} (hm : Eq.{1} Nat (Finset.card.{u1} α s) m) (hn : Eq.{1} Nat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s)) n) (i : Fin m), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Sum.{0, 0} (Fin m) (Fin n)) => α) (Sum.inl.{0, 0} (Fin m) (Fin n) i)) (FunLike.coe.{succ u1, 1, succ u1} (Equiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) (Sum.{0, 0} (Fin m) (Fin n)) (fun (_x : Sum.{0, 0} (Fin m) (Fin n)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Sum.{0, 0} (Fin m) (Fin n)) => α) _x) (Equiv.instFunLikeEquiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) (finSumEquivOfFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 m n s hm hn) (Sum.inl.{0, 0} (Fin m) (Fin n) i)) (FunLike.coe.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} (Fin m) α) (Fin m) (fun (_x : Fin m) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin m) => α) _x) (EmbeddingLike.toFunLike.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} (Fin m) α) (Fin m) α (Function.instEmbeddingLikeEmbedding.{1, succ u1} (Fin m) α)) (RelEmbedding.toEmbedding.{0, u1} (Fin m) α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_3)))))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.orderEmbOfFin.{u1} α _inst_3 s m hm)) i)
Case conversion may be inaccurate. Consider using '#align fin_sum_equiv_of_finset_inl finSumEquivOfFinset_inlₓ'. -/
@[simp]
theorem finSumEquivOfFinset_inl (hm : s.card = m) (hn : sᶜ.card = n) (i : Fin m) :
    finSumEquivOfFinset hm hn (Sum.inl i) = s.orderEmbOfFin hm i :=
  rfl
#align fin_sum_equiv_of_finset_inl finSumEquivOfFinset_inl

/- warning: fin_sum_equiv_of_finset_inr -> finSumEquivOfFinset_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : LinearOrder.{u1} α] {m : Nat} {n : Nat} {s : Finset.{u1} α} (hm : Eq.{1} Nat (Finset.card.{u1} α s) m) (hn : Eq.{1} Nat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s)) n) (i : Fin n), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) (fun (_x : Equiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) => (Sum.{0, 0} (Fin m) (Fin n)) -> α) (Equiv.hasCoeToFun.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) (finSumEquivOfFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 m n s hm hn) (Sum.inr.{0, 0} (Fin m) (Fin n) i)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{0, u1} (Fin n) α (Fin.hasLe n) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_3)))))) (fun (_x : RelEmbedding.{0, u1} (Fin n) α (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_3))))))) => (Fin n) -> α) (RelEmbedding.hasCoeToFun.{0, u1} (Fin n) α (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_3))))))) (Finset.orderEmbOfFin.{u1} α _inst_3 (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s) n hn) i)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : LinearOrder.{u1} α] {m : Nat} {n : Nat} {s : Finset.{u1} α} (hm : Eq.{1} Nat (Finset.card.{u1} α s) m) (hn : Eq.{1} Nat (Finset.card.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s)) n) (i : Fin n), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Sum.{0, 0} (Fin m) (Fin n)) => α) (Sum.inr.{0, 0} (Fin m) (Fin n) i)) (FunLike.coe.{succ u1, 1, succ u1} (Equiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) (Sum.{0, 0} (Fin m) (Fin n)) (fun (_x : Sum.{0, 0} (Fin m) (Fin n)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Sum.{0, 0} (Fin m) (Fin n)) => α) _x) (Equiv.instFunLikeEquiv.{1, succ u1} (Sum.{0, 0} (Fin m) (Fin n)) α) (finSumEquivOfFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 m n s hm hn) (Sum.inr.{0, 0} (Fin m) (Fin n) i)) (FunLike.coe.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} (Fin n) α) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => α) _x) (EmbeddingLike.toFunLike.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} (Fin n) α) (Fin n) α (Function.instEmbeddingLikeEmbedding.{1, succ u1} (Fin n) α)) (RelEmbedding.toEmbedding.{0, u1} (Fin n) α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_3)))))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.orderEmbOfFin.{u1} α _inst_3 (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) s) n hn)) i)
Case conversion may be inaccurate. Consider using '#align fin_sum_equiv_of_finset_inr finSumEquivOfFinset_inrₓ'. -/
@[simp]
theorem finSumEquivOfFinset_inr (hm : s.card = m) (hn : sᶜ.card = n) (i : Fin n) :
    finSumEquivOfFinset hm hn (Sum.inr i) = sᶜ.orderEmbOfFin hn i :=
  rfl
#align fin_sum_equiv_of_finset_inr finSumEquivOfFinset_inr

