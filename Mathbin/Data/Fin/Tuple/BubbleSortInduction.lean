/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

! This file was ported from Lean 3 source module data.fin.tuple.bubble_sort_induction
! leanprover-community/mathlib commit 50832daea47b195a48b5b33b1c8b2162c48c3afc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Tuple.Sort
import Mathbin.Data.Fintype.Perm
import Mathbin.Order.WellFounded

/-!
# "Bubble sort" induction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We implement the following induction principle `tuple.bubble_sort_induction`
on tuples with values in a linear order `α`.

Let `f : fin n → α` and let `P` be a predicate on `fin n → α`. Then we can show that
`f ∘ sort f` satisfies `P` if `f` satisfies `P`, and whenever some `g : fin n → α`
satisfies `P` and `g i > g j` for some `i < j`, then `g ∘ swap i j` also satisfies `P`.

We deduce it from a stronger variant `tuple.bubble_sort_induction'`, which
requires the assumption only for `g` that are permutations of `f`.

The latter is proved by well-founded induction via `well_founded.induction_bot'`
with respect to the lexicographic ordering on the finite set of all permutations of `f`.
-/


namespace Tuple

/- warning: tuple.bubble_sort_induction' -> Tuple.bubble_sort_induction' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {f : (Fin n) -> α} {P : ((Fin n) -> α) -> Prop}, (P f) -> (forall (σ : Equiv.Perm.{1} (Fin n)) (i : Fin n) (j : Fin n), (LT.lt.{0} (Fin n) (Fin.hasLt n) i j) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) σ) j) (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) σ) i)) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) σ))) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (Function.comp.{1, 1, 1} (Fin n) (Fin n) (Fin n) (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) σ) (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) (Equiv.swap.{1} (Fin n) (fun (a : Fin n) (b : Fin n) => Fin.decidableEq n a b) i j)))))) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) (Tuple.sort.{u1} n α _inst_1 f))))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {f : (Fin n) -> α} {P : ((Fin n) -> α) -> Prop}, (P f) -> (forall (σ : Equiv.Perm.{1} (Fin n)) (i : Fin n) (j : Fin n), (LT.lt.{0} (Fin n) (instLTFin n) i j) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) σ) j) (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) σ) i)) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) σ))) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (Function.comp.{1, 1, 1} (Fin n) (Fin n) (Fin n) (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) σ) (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) (Equiv.swap.{1} (Fin n) (fun (a : Fin n) (b : Fin n) => instDecidableEqFin n a b) i j)))))) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) (Tuple.sort.{u1} n α _inst_1 f))))
Case conversion may be inaccurate. Consider using '#align tuple.bubble_sort_induction' Tuple.bubble_sort_induction'ₓ'. -/
/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satsifies `P` and `P` is preserved on permutations of `f` when swapping two
antitone values. -/
theorem bubble_sort_induction' {n : ℕ} {α : Type _} [LinearOrder α] {f : Fin n → α}
    {P : (Fin n → α) → Prop} (hf : P f)
    (h :
      ∀ (σ : Equiv.Perm (Fin n)) (i j : Fin n),
        i < j → (f ∘ σ) j < (f ∘ σ) i → P (f ∘ σ) → P (f ∘ σ ∘ Equiv.swap i j)) :
    P (f ∘ sort f) :=
  by
  letI := @Preorder.lift _ (Lex (Fin n → α)) _ fun σ : Equiv.Perm (Fin n) => toLex (f ∘ σ)
  refine'
    @WellFounded.induction_bot' _ _ _ (@Finite.Preorder.wellFounded_lt (Equiv.Perm (Fin n)) _ _)
      (Equiv.refl _) (sort f) P (fun σ => f ∘ σ) (fun σ hσ hfσ => _) hf
  obtain ⟨i, j, hij₁, hij₂⟩ := antitone_pair_of_not_sorted' hσ
  exact ⟨σ * Equiv.swap i j, Pi.lex_desc hij₁ hij₂, h σ i j hij₁ hij₂ hfσ⟩
#align tuple.bubble_sort_induction' Tuple.bubble_sort_induction'

/- warning: tuple.bubble_sort_induction -> Tuple.bubble_sort_induction is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {f : (Fin n) -> α} {P : ((Fin n) -> α) -> Prop}, (P f) -> (forall (g : (Fin n) -> α) (i : Fin n) (j : Fin n), (LT.lt.{0} (Fin n) (Fin.hasLt n) i j) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (g j) (g i)) -> (P g) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α g (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) (Equiv.swap.{1} (Fin n) (fun (a : Fin n) (b : Fin n) => Fin.decidableEq n a b) i j))))) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) (Tuple.sort.{u1} n α _inst_1 f))))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {f : (Fin n) -> α} {P : ((Fin n) -> α) -> Prop}, (P f) -> (forall (g : (Fin n) -> α) (i : Fin n) (j : Fin n), (LT.lt.{0} (Fin n) (instLTFin n) i j) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (g j) (g i)) -> (P g) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α g (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) (Equiv.swap.{1} (Fin n) (fun (a : Fin n) (b : Fin n) => instDecidableEqFin n a b) i j))))) -> (P (Function.comp.{1, 1, succ u1} (Fin n) (Fin n) α f (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) (Tuple.sort.{u1} n α _inst_1 f))))
Case conversion may be inaccurate. Consider using '#align tuple.bubble_sort_induction Tuple.bubble_sort_inductionₓ'. -/
/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satsifies `P` and `P` is preserved when swapping two antitone values. -/
theorem bubble_sort_induction {n : ℕ} {α : Type _} [LinearOrder α] {f : Fin n → α}
    {P : (Fin n → α) → Prop} (hf : P f)
    (h : ∀ (g : Fin n → α) (i j : Fin n), i < j → g j < g i → P g → P (g ∘ Equiv.swap i j)) :
    P (f ∘ sort f) :=
  bubble_sort_induction' hf fun σ => h _
#align tuple.bubble_sort_induction Tuple.bubble_sort_induction

end Tuple

