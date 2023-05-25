/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.ultraproducts
! leanprover-community/mathlib commit f1ae620609496a37534c2ab3640b641d5be8b6f0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.Quotients
import Mathbin.Order.Filter.Germ
import Mathbin.Order.Filter.Ultrafilter

/-! # Ultraproducts and Łoś's Theorem

## Main Definitions
* `first_order.language.ultraproduct.Structure` is the ultraproduct structure on `filter.product`.

## Main Results
* Łoś's Theorem: `first_order.language.ultraproduct.sentence_realize`. An ultraproduct models a
sentence `φ` if and only if the set of structures in the product that model `φ` is in the
ultrafilter.

## Tags
ultraproduct, Los's theorem

-/


universe u v

variable {α : Type _} (M : α → Type _) (u : Ultrafilter α)

open FirstOrder Filter

open Filter

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}} [∀ a, L.Structure (M a)]

namespace Ultraproduct

#print FirstOrder.Language.Ultraproduct.setoidPrestructure /-
instance setoidPrestructure : L.Prestructure ((u : Filter α).productSetoid M) :=
  {
    (u : Filter α).productSetoid
      M with
    toStructure :=
      { funMap := fun n f x a => funMap f fun i => x i a
        rel_map := fun n r x => ∀ᶠ a : α in u, RelMap r fun i => x i a }
    fun_equiv := fun n f x y xy =>
      by
      refine' mem_of_superset (Inter_mem.2 xy) fun a ha => _
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at ha
      simp only [Set.mem_setOf_eq, ha]
    rel_equiv := fun n r x y xy => by
      rw [← iff_eq_eq]
      refine' ⟨fun hx => _, fun hy => _⟩
      · refine' mem_of_superset (inter_mem hx (Inter_mem.2 xy)) _
        rintro a ⟨ha1, ha2⟩
        simp only [Set.mem_iInter, Set.mem_setOf_eq] at *
        rw [← funext ha2]
        exact ha1
      · refine' mem_of_superset (inter_mem hy (Inter_mem.2 xy)) _
        rintro a ⟨ha1, ha2⟩
        simp only [Set.mem_iInter, Set.mem_setOf_eq] at *
        rw [funext ha2]
        exact ha1 }
#align first_order.language.ultraproduct.setoid_prestructure FirstOrder.Language.Ultraproduct.setoidPrestructure
-/

variable {M} {u}

#print FirstOrder.Language.Ultraproduct.structure /-
instance structure : L.Structure ((u : Filter α).product M) :=
  Language.quotientStructure
#align first_order.language.ultraproduct.Structure FirstOrder.Language.Ultraproduct.structure
-/

/- warning: first_order.language.ultraproduct.fun_map_cast -> FirstOrder.Language.Ultraproduct.funMap_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u3}} {M : α -> Type.{u4}} {u : Ultrafilter.{u3} α} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u1, u2, u4} L (M a)] {n : Nat} (f : FirstOrder.Language.Functions.{u1, u2} L n) (x : (Fin n) -> (forall (a : α), M a)), Eq.{succ (max u3 u4)} (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (FirstOrder.Language.Structure.funMap.{u1, u2, max u3 u4} L (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (FirstOrder.Language.Ultraproduct.structure.{u1, u2, u3, u4} α M u L (fun (a : α) => _inst_1 a)) n f (fun (i : Fin n) => (fun (a : Sort.{max (succ u3) (succ u4)}) (b : Type.{max u3 u4}) [self : HasLiftT.{max (succ u3) (succ u4), succ (max u3 u4)} a b] => self.0) (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (HasLiftT.mk.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (CoeTCₓ.coe.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (Filter.Product.hasCoeT.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) (fun (a : α) => M a)))) (x i))) ((fun (a : Sort.{max (succ u3) (succ u4)}) (b : Type.{max u3 u4}) [self : HasLiftT.{max (succ u3) (succ u4), succ (max u3 u4)} a b] => self.0) (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (HasLiftT.mk.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (CoeTCₓ.coe.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (Filter.Product.hasCoeT.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) (fun (a : α) => M a)))) (fun (a : α) => FirstOrder.Language.Structure.funMap.{u1, u2, u4} L (M a) (_inst_1 a) n f (fun (i : Fin n) => x i a)))
but is expected to have type
  forall {α : Type.{u2}} {M : α -> Type.{u1}} {u : Ultrafilter.{u2} α} {L : FirstOrder.Language.{u3, u4}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u3, u4, u1} L (M a)] {n : Nat} (f : FirstOrder.Language.Functions.{u3, u4} L n) (x : (Fin n) -> (forall (a : α), M a)), Eq.{max (succ u2) (succ u1)} (Quotient.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a))) (FirstOrder.Language.Structure.funMap.{u3, u4, max u2 u1} L (Quotient.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a))) (FirstOrder.Language.quotientStructure.{u3, u4, max u2 u1} L (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (FirstOrder.Language.Ultraproduct.setoidPrestructure.{u3, u4, u2, u1} α (fun (a : α) => M a) u L (fun (a : α) => _inst_1 a))) n f (fun (i : Fin n) => Quotient.mk'.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (x i))) (Quotient.mk'.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (fun (a : α) => FirstOrder.Language.Structure.funMap.{u3, u4, u1} L (M a) (_inst_1 a) n f (fun (i : Fin n) => x i a)))
Case conversion may be inaccurate. Consider using '#align first_order.language.ultraproduct.fun_map_cast FirstOrder.Language.Ultraproduct.funMap_castₓ'. -/
theorem funMap_cast {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ a, M a) :
    (funMap f fun i => (x i : (u : Filter α).product M)) = fun a => funMap f fun i => x i a := by
  apply fun_map_quotient_mk
#align first_order.language.ultraproduct.fun_map_cast FirstOrder.Language.Ultraproduct.funMap_cast

/- warning: first_order.language.ultraproduct.term_realize_cast -> FirstOrder.Language.Ultraproduct.term_realize_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u3}} {M : α -> Type.{u4}} {u : Ultrafilter.{u3} α} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u1, u2, u4} L (M a)] {β : Type.{u5}} (x : β -> (forall (a : α), M a)) (t : FirstOrder.Language.Term.{u1, u2, u5} L β), Eq.{succ (max u3 u4)} (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (FirstOrder.Language.Term.realize.{u1, u2, max u3 u4, u5} L (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (FirstOrder.Language.Ultraproduct.structure.{u1, u2, u3, u4} α M u L (fun (a : α) => _inst_1 a)) β (fun (i : β) => (fun (a : Sort.{max (succ u3) (succ u4)}) (b : Type.{max u3 u4}) [self : HasLiftT.{max (succ u3) (succ u4), succ (max u3 u4)} a b] => self.0) (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (HasLiftT.mk.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (CoeTCₓ.coe.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (Filter.Product.hasCoeT.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) (fun (a : α) => M a)))) (x i)) t) ((fun (a : Sort.{max (succ u3) (succ u4)}) (b : Type.{max u3 u4}) [self : HasLiftT.{max (succ u3) (succ u4), succ (max u3 u4)} a b] => self.0) (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (HasLiftT.mk.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (CoeTCₓ.coe.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (Filter.Product.hasCoeT.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) (fun (a : α) => M a)))) (fun (a : α) => FirstOrder.Language.Term.realize.{u1, u2, u4, u5} L (M a) (_inst_1 a) β (fun (i : β) => x i a) t))
but is expected to have type
  forall {α : Type.{u2}} {M : α -> Type.{u1}} {u : Ultrafilter.{u2} α} {L : FirstOrder.Language.{u4, u5}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u4, u5, u1} L (M a)] {β : Type.{u3}} (x : β -> (forall (a : α), M a)) (t : FirstOrder.Language.Term.{u4, u5, u3} L β), Eq.{max (succ u2) (succ u1)} (Quotient.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a))) (FirstOrder.Language.Term.realize.{u4, u5, max u2 u1, u3} L (Quotient.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a))) (FirstOrder.Language.quotientStructure.{u4, u5, max u2 u1} L (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (FirstOrder.Language.Ultraproduct.setoidPrestructure.{u4, u5, u2, u1} α (fun (a : α) => M a) u L (fun (a : α) => _inst_1 a))) β (fun (i : β) => Quotient.mk'.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (x i)) t) (Quotient.mk'.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (fun (a : α) => FirstOrder.Language.Term.realize.{u4, u5, u1, u3} L (M a) (_inst_1 a) β (fun (i : β) => x i a) t))
Case conversion may be inaccurate. Consider using '#align first_order.language.ultraproduct.term_realize_cast FirstOrder.Language.Ultraproduct.term_realize_castₓ'. -/
theorem term_realize_cast {β : Type _} (x : β → ∀ a, M a) (t : L.term β) :
    (t.realize fun i => (x i : (u : Filter α).product M)) = fun a => t.realize fun i => x i a :=
  by
  convert@term.realize_quotient_mk L _ ((u : Filter α).productSetoid M)
      (ultraproduct.setoid_prestructure M u) _ t x
  ext a
  induction t
  · rfl
  · simp only [term.realize, t_ih]
    rfl
#align first_order.language.ultraproduct.term_realize_cast FirstOrder.Language.Ultraproduct.term_realize_cast

variable [∀ a : α, Nonempty (M a)]

/- warning: first_order.language.ultraproduct.bounded_formula_realize_cast -> FirstOrder.Language.Ultraproduct.boundedFormula_realize_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u3}} {M : α -> Type.{u4}} {u : Ultrafilter.{u3} α} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u1, u2, u4} L (M a)] [_inst_2 : forall (a : α), Nonempty.{succ u4} (M a)] {β : Type.{u5}} {n : Nat} (φ : FirstOrder.Language.BoundedFormula.{u1, u2, u5} L β n) (x : β -> (forall (a : α), M a)) (v : (Fin n) -> (forall (a : α), M a)), Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, max u3 u4, u5} L (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (FirstOrder.Language.Ultraproduct.structure.{u1, u2, u3, u4} α M u L (fun (a : α) => _inst_1 a)) β n φ (fun (i : β) => (fun (a : Sort.{max (succ u3) (succ u4)}) (b : Type.{max u3 u4}) [self : HasLiftT.{max (succ u3) (succ u4), succ (max u3 u4)} a b] => self.0) (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (HasLiftT.mk.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (CoeTCₓ.coe.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (Filter.Product.hasCoeT.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) (fun (a : α) => M a)))) (x i)) (fun (i : Fin n) => (fun (a : Sort.{max (succ u3) (succ u4)}) (b : Type.{max u3 u4}) [self : HasLiftT.{max (succ u3) (succ u4), succ (max u3 u4)} a b] => self.0) (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (HasLiftT.mk.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (CoeTCₓ.coe.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (Filter.Product.hasCoeT.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) (fun (a : α) => M a)))) (v i))) (Filter.Eventually.{u3} α (fun (a : α) => FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u4, u5} L (M a) (_inst_1 a) β n φ (fun (i : β) => x i a) (fun (i : Fin n) => v i a)) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u))
but is expected to have type
  forall {α : Type.{u2}} {M : α -> Type.{u1}} {u : Ultrafilter.{u2} α} {L : FirstOrder.Language.{u4, u5}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u4, u5, u1} L (M a)] [_inst_2 : forall (a : α), Nonempty.{succ u1} (M a)] {β : Type.{u3}} {n : Nat} (φ : FirstOrder.Language.BoundedFormula.{u4, u5, u3} L β n) (x : β -> (forall (a : α), M a)) (v : (Fin n) -> (forall (a : α), M a)), Iff (FirstOrder.Language.BoundedFormula.Realize.{u4, u5, max u2 u1, u3} L (Quotient.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a))) (FirstOrder.Language.quotientStructure.{u4, u5, max u2 u1} L (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (FirstOrder.Language.Ultraproduct.setoidPrestructure.{u4, u5, u2, u1} α (fun (a : α) => M a) u L (fun (a : α) => _inst_1 a))) β n φ (fun (i : β) => Quotient.mk'.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (x i)) (fun (i : Fin n) => Quotient.mk'.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (v i))) (Filter.Eventually.{u2} α (fun (a : α) => FirstOrder.Language.BoundedFormula.Realize.{u4, u5, u1, u3} L (M a) (_inst_1 a) β n φ (fun (i : β) => x i a) (fun (i : Fin n) => v i a)) (Ultrafilter.toFilter.{u2} α u))
Case conversion may be inaccurate. Consider using '#align first_order.language.ultraproduct.bounded_formula_realize_cast FirstOrder.Language.Ultraproduct.boundedFormula_realize_castₓ'. -/
theorem boundedFormula_realize_cast {β : Type _} {n : ℕ} (φ : L.BoundedFormula β n)
    (x : β → ∀ a, M a) (v : Fin n → ∀ a, M a) :
    (φ.realize (fun i : β => (x i : (u : Filter α).product M)) fun i => v i) ↔
      ∀ᶠ a : α in u, φ.realize (fun i : β => x i a) fun i => v i a :=
  by
  letI := (u : Filter α).productSetoid M
  induction' φ with _ _ _ _ _ _ _ _ m _ _ ih ih' k φ ih
  · simp only [bounded_formula.realize, eventually_const]
  · have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [bounded_formula.realize, (Sum.comp_elim coe x v).symm, h2, term_realize_cast]
    exact Quotient.eq''
  · have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [bounded_formula.realize, (Sum.comp_elim coe x v).symm, term_realize_cast, h2]
    exact rel_map_quotient_mk _ _
  · simp only [bounded_formula.realize, ih v, ih' v]
    rw [Ultrafilter.eventually_imp]
  · simp only [bounded_formula.realize]
    trans
      ∀ m : ∀ a : α, M a,
        φ.realize (fun i : β => (x i : (u : Filter α).product M))
          (Fin.snoc (coe ∘ v) (↑m : (u : Filter α).product M))
    · exact forall_quotient_iff
    have h' :
      ∀ (m : ∀ a, M a) (a : α),
        (fun i : Fin (k + 1) => (Fin.snoc v m : _ → ∀ a, M a) i a) =
          Fin.snoc (fun i : Fin k => v i a) (m a) :=
      by
      refine' fun m a => funext (Fin.reverseInduction _ fun i hi => _)
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    simp only [← Fin.comp_snoc, ih, h']
    refine' ⟨fun h => _, fun h m => _⟩
    · contrapose! h
      simp_rw [← Ultrafilter.eventually_not, not_forall] at h
      refine'
        ⟨fun a : α =>
          Classical.epsilon fun m : M a =>
            ¬φ.realize (fun i => x i a) (Fin.snoc (fun i => v i a) m),
          _⟩
      rw [← Ultrafilter.eventually_not]
      exact Filter.mem_of_superset h fun a ha => Classical.epsilon_spec ha
    · rw [Filter.eventually_iff] at *
      exact Filter.mem_of_superset h fun a ha => ha (m a)
#align first_order.language.ultraproduct.bounded_formula_realize_cast FirstOrder.Language.Ultraproduct.boundedFormula_realize_cast

/- warning: first_order.language.ultraproduct.realize_formula_cast -> FirstOrder.Language.Ultraproduct.realize_formula_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u3}} {M : α -> Type.{u4}} {u : Ultrafilter.{u3} α} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u1, u2, u4} L (M a)] [_inst_2 : forall (a : α), Nonempty.{succ u4} (M a)] {β : Type.{u5}} (φ : FirstOrder.Language.Formula.{u1, u2, u5} L β) (x : β -> (forall (a : α), M a)), Iff (FirstOrder.Language.Formula.Realize.{u1, u2, max u3 u4, u5} L (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (FirstOrder.Language.Ultraproduct.structure.{u1, u2, u3, u4} α M u L (fun (a : α) => _inst_1 a)) β φ (fun (i : β) => (fun (a : Sort.{max (succ u3) (succ u4)}) (b : Type.{max u3 u4}) [self : HasLiftT.{max (succ u3) (succ u4), succ (max u3 u4)} a b] => self.0) (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (HasLiftT.mk.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (CoeTCₓ.coe.{max (succ u3) (succ u4), succ (max u3 u4)} (forall (a : α), M a) (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (Filter.Product.hasCoeT.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) (fun (a : α) => M a)))) (x i))) (Filter.Eventually.{u3} α (fun (a : α) => FirstOrder.Language.Formula.Realize.{u1, u2, u4, u5} L (M a) (_inst_1 a) β φ (fun (i : β) => x i a)) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u))
but is expected to have type
  forall {α : Type.{u2}} {M : α -> Type.{u1}} {u : Ultrafilter.{u2} α} {L : FirstOrder.Language.{u4, u5}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u4, u5, u1} L (M a)] [_inst_2 : forall (a : α), Nonempty.{succ u1} (M a)] {β : Type.{u3}} (φ : FirstOrder.Language.Formula.{u4, u5, u3} L β) (x : β -> (forall (a : α), M a)), Iff (FirstOrder.Language.Formula.Realize.{u4, u5, max u2 u1, u3} L (Quotient.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a))) (FirstOrder.Language.quotientStructure.{u4, u5, max u2 u1} L (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (FirstOrder.Language.Ultraproduct.setoidPrestructure.{u4, u5, u2, u1} α (fun (a : α) => M a) u L (fun (a : α) => _inst_1 a))) β φ (fun (i : β) => Quotient.mk'.{max (succ u2) (succ u1)} (forall (a : α), (fun (a : α) => M a) a) (Filter.productSetoid.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) (fun (a : α) => M a)) (x i))) (Filter.Eventually.{u2} α (fun (a : α) => FirstOrder.Language.Formula.Realize.{u4, u5, u1, u3} L (M a) (_inst_1 a) β φ (fun (i : β) => x i a)) (Ultrafilter.toFilter.{u2} α u))
Case conversion may be inaccurate. Consider using '#align first_order.language.ultraproduct.realize_formula_cast FirstOrder.Language.Ultraproduct.realize_formula_castₓ'. -/
theorem realize_formula_cast {β : Type _} (φ : L.Formula β) (x : β → ∀ a, M a) :
    (φ.realize fun i => (x i : (u : Filter α).product M)) ↔
      ∀ᶠ a : α in u, φ.realize fun i => x i a :=
  by
  simp_rw [formula.realize, ← bounded_formula_realize_cast φ x, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)
#align first_order.language.ultraproduct.realize_formula_cast FirstOrder.Language.Ultraproduct.realize_formula_cast

/- warning: first_order.language.ultraproduct.sentence_realize -> FirstOrder.Language.Ultraproduct.sentence_realize is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u3}} {M : α -> Type.{u4}} {u : Ultrafilter.{u3} α} {L : FirstOrder.Language.{u1, u2}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u1, u2, u4} L (M a)] [_inst_2 : forall (a : α), Nonempty.{succ u4} (M a)] (φ : FirstOrder.Language.Sentence.{u1, u2} L), Iff (FirstOrder.Language.Sentence.Realize.{u1, u2, max u3 u4} L (Filter.Product.{u3, u4} α ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u) M) (FirstOrder.Language.Ultraproduct.structure.{u1, u2, u3, u4} α M u L (fun (a : α) => _inst_1 a)) φ) (Filter.Eventually.{u3} α (fun (a : α) => FirstOrder.Language.Sentence.Realize.{u1, u2, u4} L (M a) (_inst_1 a) φ) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Ultrafilter.{u3} α) (Filter.{u3} α) (HasLiftT.mk.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (CoeTCₓ.coe.{succ u3, succ u3} (Ultrafilter.{u3} α) (Filter.{u3} α) (Ultrafilter.Filter.hasCoeT.{u3} α))) u))
but is expected to have type
  forall {α : Type.{u2}} {M : α -> Type.{u1}} {u : Ultrafilter.{u2} α} {L : FirstOrder.Language.{u3, u4}} [_inst_1 : forall (a : α), FirstOrder.Language.Structure.{u3, u4, u1} L (M a)] [_inst_2 : forall (a : α), Nonempty.{succ u1} (M a)] (φ : FirstOrder.Language.Sentence.{u3, u4} L), Iff (FirstOrder.Language.Sentence.Realize.{u3, u4, max u2 u1} L (Filter.Product.{u2, u1} α (Ultrafilter.toFilter.{u2} α u) M) (FirstOrder.Language.Ultraproduct.structure.{u3, u4, u2, u1} α M u L (fun (a : α) => _inst_1 a)) φ) (Filter.Eventually.{u2} α (fun (a : α) => FirstOrder.Language.Sentence.Realize.{u3, u4, u1} L (M a) (_inst_1 a) φ) (Ultrafilter.toFilter.{u2} α u))
Case conversion may be inaccurate. Consider using '#align first_order.language.ultraproduct.sentence_realize FirstOrder.Language.Ultraproduct.sentence_realizeₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Łoś's Theorem : A sentence is true in an ultraproduct if and only if the set of structures it is
  true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.Sentence) : (u : Filter α).product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ :=
  by
  simp_rw [sentence.realize, ← realize_formula_cast φ, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)
#align first_order.language.ultraproduct.sentence_realize FirstOrder.Language.Ultraproduct.sentence_realize

instance : Nonempty ((u : Filter α).product M) :=
  letI : ∀ a, Inhabited (M a) := fun _ => Classical.inhabited_of_nonempty'
  instNonempty

end Ultraproduct

end Language

end FirstOrder

