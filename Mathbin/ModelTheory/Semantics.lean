/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn

! This file was ported from Lean 3 source module model_theory.semantics
! leanprover-community/mathlib commit 6cf5900728239efa287df7761ec2a1ac9cf39b29
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Basic
import Mathbin.ModelTheory.Syntax

/-!
# Basics on First-Order Semantics

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions
* `first_order.language.term.realize` is defined so that `t.realize v` is the term `t` evaluated at
variables `v`.
* `first_order.language.bounded_formula.realize` is defined so that `φ.realize v xs` is the bounded
formula `φ` evaluated at tuples of variables `v` and `xs`.
* `first_order.language.formula.realize` is defined so that `φ.realize v` is the formula `φ`
evaluated at variables `v`.
* `first_order.language.sentence.realize` is defined so that `φ.realize M` is the sentence `φ`
evaluated in the structure `M`. Also denoted `M ⊨ φ`.
* `first_order.language.Theory.model` is defined so that `T.model M` is true if and only if every
sentence of `T` is realized in `M`. Also denoted `T ⊨ φ`.

## Main Results
* `first_order.language.bounded_formula.realize_to_prenex` shows that the prenex normal form of a
formula has the same realization as the original formula.
* Several results in this file show that syntactic constructions such as `relabel`, `cast_le`,
`lift_at`, `subst`, and the actions of language maps commute with realization of terms, formulas,
sentences, and theories.

## Implementation Notes
* Formulas use a modified version of de Bruijn variables. Specifically, a `L.bounded_formula α n`
is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
indexed by `fin n`, which can. For any `φ : L.bounded_formula α (n + 1)`, we define the formula
`∀' φ : L.bounded_formula α n` by universally quantifying over the variable indexed by
`n : fin (n + 1)`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}

variable {M : Type w} {N P : Type _} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'}

open FirstOrder Cardinal

open Structure Cardinal Fin

namespace Term

#print FirstOrder.Language.Term.realize /-
/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
@[simp]
def realize (v : α → M) : ∀ t : L.term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize
#align first_order.language.term.realize FirstOrder.Language.Term.realize
-/

#print FirstOrder.Language.Term.realize_relabel /-
@[simp]
theorem realize_relabel {t : L.term α} {g : α → β} {v : β → M} :
    (t.relabel g).realize v = t.realize (v ∘ g) :=
  by
  induction' t with _ n f ts ih
  · rfl
  · simp [ih]
#align first_order.language.term.realize_relabel FirstOrder.Language.Term.realize_relabel
-/

/- warning: first_order.language.term.realize_lift_at -> FirstOrder.Language.Term.realize_liftAt is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} {n' : Nat} {m : Nat} {t : FirstOrder.Language.Term.{u1, u2, u4} L (Sum.{u4, 0} α (Fin n))} {v : (Sum.{u4, 0} α (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 (Sum.{u4, 0} α (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) v (FirstOrder.Language.Term.liftAt.{u1, u2, u4} L α n n' m t)) (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 (Sum.{u4, 0} α (Fin n)) (Function.comp.{succ u4, succ u4, succ u3} (Sum.{u4, 0} α (Fin n)) (Sum.{u4, 0} α (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) M v (Sum.map.{u4, 0, u4, 0} α α (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (id.{succ u4} α) (fun (i : Fin n) => ite.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LT.lt.{0} Nat Nat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) m) (Nat.decidableLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) m) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')))) (Fin.castAdd n n') i) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')))) (Fin.addNat n n') i)))) t)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} {n' : Nat} {m : Nat} {t : FirstOrder.Language.Term.{u1, u2, u4} L (Sum.{u4, 0} α (Fin n))} {v : (Sum.{u4, 0} α (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 (Sum.{u4, 0} α (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) v (FirstOrder.Language.Term.liftAt.{u1, u2, u4} L α n n' m t)) (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 (Sum.{u4, 0} α (Fin n)) (Function.comp.{succ u4, succ u4, succ u3} (Sum.{u4, 0} α (Fin n)) (Sum.{u4, 0} α (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) M v (Sum.map.{u4, 0, u4, 0} α α (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (id.{succ u4} α) (fun (i : Fin n) => ite.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (LT.lt.{0} Nat instLTNat (Fin.val n i) m) (Nat.decLt (Fin.val n i) m) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))))) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')))) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin n) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')))) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))))) (Fin.castAdd n n') i) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))))) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')))) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin n) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')))) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))))) (Fin.addNat n n') i)))) t)
Case conversion may be inaccurate. Consider using '#align first_order.language.term.realize_lift_at FirstOrder.Language.Term.realize_liftAtₓ'. -/
@[simp]
theorem realize_liftAt {n n' m : ℕ} {t : L.term (Sum α (Fin n))} {v : Sum α (Fin (n + n')) → M} :
    (t.liftAt n' m).realize v =
      t.realize (v ∘ Sum.map id fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat n' i) :=
  realize_relabel
#align first_order.language.term.realize_lift_at FirstOrder.Language.Term.realize_liftAt

/- warning: first_order.language.term.realize_constants -> FirstOrder.Language.Term.realize_constants is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {c : FirstOrder.Language.Constants.{u1, u2} L} {v : α -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 α v (FirstOrder.Language.Constants.term.{u1, u2, u4} L α c)) ((fun (a : Type.{u1}) (b : Type.{u3}) [self : HasLiftT.{succ u1, succ u3} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) M (HasLiftT.mk.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (CoeTCₓ.coe.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (FirstOrder.Language.hasCoeT.{u1, u2, u3} L M _inst_1))) c)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {c : FirstOrder.Language.Constants.{u1, u2} L} {v : α -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 α v (FirstOrder.Language.Constants.term.{u1, u2, u4} L α c)) (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)
Case conversion may be inaccurate. Consider using '#align first_order.language.term.realize_constants FirstOrder.Language.Term.realize_constantsₓ'. -/
@[simp]
theorem realize_constants {c : L.Constants} {v : α → M} : c.term.realize v = c :=
  funMap_eq_coe_constants
#align first_order.language.term.realize_constants FirstOrder.Language.Term.realize_constants

#print FirstOrder.Language.Term.realize_functions_apply₁ /-
@[simp]
theorem realize_functions_apply₁ {f : L.Functions 1} {t : L.term α} {v : α → M} :
    (f.apply₁ t).realize v = funMap f ![t.realize v] :=
  by
  rw [functions.apply₁, term.realize]
  refine' congr rfl (funext fun i => _)
  simp only [Matrix.cons_val_fin_one]
#align first_order.language.term.realize_functions_apply₁ FirstOrder.Language.Term.realize_functions_apply₁
-/

#print FirstOrder.Language.Term.realize_functions_apply₂ /-
@[simp]
theorem realize_functions_apply₂ {f : L.Functions 2} {t₁ t₂ : L.term α} {v : α → M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ![t₁.realize v, t₂.realize v] :=
  by
  rw [functions.apply₂, term.realize]
  refine' congr rfl (funext (Fin.cases _ _))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
#align first_order.language.term.realize_functions_apply₂ FirstOrder.Language.Term.realize_functions_apply₂
-/

#print FirstOrder.Language.Term.realize_con /-
theorem realize_con {A : Set M} {a : A} {v : α → M} : (L.con a).term.realize v = a :=
  rfl
#align first_order.language.term.realize_con FirstOrder.Language.Term.realize_con
-/

#print FirstOrder.Language.Term.realize_subst /-
@[simp]
theorem realize_subst {t : L.term α} {tf : α → L.term β} {v : β → M} :
    (t.subst tf).realize v = t.realize fun a => (tf a).realize v :=
  by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]
#align first_order.language.term.realize_subst FirstOrder.Language.Term.realize_subst
-/

#print FirstOrder.Language.Term.realize_restrictVar /-
@[simp]
theorem realize_restrictVar [DecidableEq α] {t : L.term α} {s : Set α} (h : ↑t.varFinset ⊆ s)
    {v : α → M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ coe) = t.realize v :=
  by
  induction' t with _ _ _ _ ih
  · rfl
  · simp_rw [var_finset, Finset.coe_bunionᵢ, Set.unionᵢ_subset_iff] at h
    exact congr rfl (funext fun i => ih i (h i (Finset.mem_univ i)))
#align first_order.language.term.realize_restrict_var FirstOrder.Language.Term.realize_restrictVar
-/

/- warning: first_order.language.term.realize_restrict_var_left -> FirstOrder.Language.Term.realize_restrictVarLeft is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} [_inst_4 : DecidableEq.{succ u4} α] {γ : Type.{u5}} {t : FirstOrder.Language.Term.{u1, u2, max u4 u5} L (Sum.{u4, u5} α γ)} {s : Set.{u4} α} (h : HasSubset.Subset.{u4} (Set.{u4} α) (Set.hasSubset.{u4} α) ((fun (a : Type.{u4}) (b : Type.{u4}) [self : HasLiftT.{succ u4, succ u4} a b] => self.0) (Finset.{u4} α) (Set.{u4} α) (HasLiftT.mk.{succ u4, succ u4} (Finset.{u4} α) (Set.{u4} α) (CoeTCₓ.coe.{succ u4, succ u4} (Finset.{u4} α) (Set.{u4} α) (Finset.Set.hasCoeT.{u4} α))) (FirstOrder.Language.Term.varFinsetLeft.{u1, u2, u4, u5} L α γ (fun (a : α) (b : α) => _inst_4 a b) t)) s) {v : α -> M} {xs : γ -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u1, u2, u3, max u4 u5} L M _inst_1 (Sum.{u4, u5} (coeSort.{succ u4, succ (succ u4)} (Set.{u4} α) Type.{u4} (Set.hasCoeToSort.{u4} α) s) γ) (Sum.elim.{u4, u5, succ u3} (coeSort.{succ u4, succ (succ u4)} (Set.{u4} α) Type.{u4} (Set.hasCoeToSort.{u4} α) s) γ M (Function.comp.{succ u4, succ u4, succ u3} (coeSort.{succ u4, succ (succ u4)} (Set.{u4} α) Type.{u4} (Set.hasCoeToSort.{u4} α) s) α M v ((fun (a : Type.{u4}) (b : Type.{u4}) [self : HasLiftT.{succ u4, succ u4} a b] => self.0) (coeSort.{succ u4, succ (succ u4)} (Set.{u4} α) Type.{u4} (Set.hasCoeToSort.{u4} α) s) α (HasLiftT.mk.{succ u4, succ u4} (coeSort.{succ u4, succ (succ u4)} (Set.{u4} α) Type.{u4} (Set.hasCoeToSort.{u4} α) s) α (CoeTCₓ.coe.{succ u4, succ u4} (coeSort.{succ u4, succ (succ u4)} (Set.{u4} α) Type.{u4} (Set.hasCoeToSort.{u4} α) s) α (coeBase.{succ u4, succ u4} (coeSort.{succ u4, succ (succ u4)} (Set.{u4} α) Type.{u4} (Set.hasCoeToSort.{u4} α) s) α (coeSubtype.{succ u4} α (fun (x : α) => Membership.Mem.{u4, u4} α (Set.{u4} α) (Set.hasMem.{u4} α) x s))))))) xs) (FirstOrder.Language.Term.restrictVarLeft.{u1, u2, u4, u4, u5} L α (coeSort.{succ u4, succ (succ u4)} (Set.{u4} α) Type.{u4} (Set.hasCoeToSort.{u4} α) s) (fun (a : α) (b : α) => _inst_4 a b) γ t (Set.inclusion.{u4} α (fun (x : α) => Membership.Mem.{u4, u4} α (Multiset.{u4} α) (Multiset.hasMem.{u4} α) x (Finset.val.{u4} α (FirstOrder.Language.Term.varFinsetLeft.{u1, u2, u4, u5} L α γ (fun (a : α) (b : α) => _inst_4 a b) t))) s h))) (FirstOrder.Language.Term.realize.{u1, u2, u3, max u4 u5} L M _inst_1 (Sum.{u4, u5} α γ) (Sum.elim.{u4, u5, succ u3} α γ M v xs) t)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] {α : Type.{u5}} [_inst_4 : DecidableEq.{succ u5} α] {γ : Type.{u1}} {t : FirstOrder.Language.Term.{u2, u3, max u1 u5} L (Sum.{u5, u1} α γ)} {s : Set.{u5} α} (h : HasSubset.Subset.{u5} (Set.{u5} α) (Set.instHasSubsetSet.{u5} α) (Finset.toSet.{u5} α (FirstOrder.Language.Term.varFinsetLeft.{u2, u3, u5, u1} L α γ (fun (a : α) (b : α) => _inst_4 a b) t)) s) {v : α -> M} {xs : γ -> M}, Eq.{succ u4} M (FirstOrder.Language.Term.realize.{u2, u3, u4, max u1 u5} L M _inst_1 (Sum.{u5, u1} (Set.Elem.{u5} α s) γ) (Sum.elim.{u5, u1, succ u4} (Set.Elem.{u5} α s) γ M (Function.comp.{succ u5, succ u5, succ u4} (Set.Elem.{u5} α s) α M v (Subtype.val.{succ u5} α (fun (x : α) => Membership.mem.{u5, u5} α (Set.{u5} α) (Set.instMembershipSet.{u5} α) x s))) xs) (FirstOrder.Language.Term.restrictVarLeft.{u2, u3, u5, u5, u1} L α (Set.Elem.{u5} α s) (fun (a : α) (b : α) => _inst_4 a b) γ t (Set.inclusion.{u5} α (fun (x : α) => Membership.mem.{u5, u5} α (Multiset.{u5} α) (Multiset.instMembershipMultiset.{u5} α) x (Finset.val.{u5} α (FirstOrder.Language.Term.varFinsetLeft.{u2, u3, u5, u1} L α γ (fun (a : α) (b : α) => _inst_4 a b) t))) s h))) (FirstOrder.Language.Term.realize.{u2, u3, u4, max u1 u5} L M _inst_1 (Sum.{u5, u1} α γ) (Sum.elim.{u5, u1, succ u4} α γ M v xs) t)
Case conversion may be inaccurate. Consider using '#align first_order.language.term.realize_restrict_var_left FirstOrder.Language.Term.realize_restrictVarLeftₓ'. -/
@[simp]
theorem realize_restrictVarLeft [DecidableEq α] {γ : Type _} {t : L.term (Sum α γ)} {s : Set α}
    (h : ↑t.varFinsetLeft ⊆ s) {v : α → M} {xs : γ → M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ coe) xs) =
      t.realize (Sum.elim v xs) :=
  by
  induction' t with a _ _ _ ih
  · cases a <;> rfl
  · simp_rw [var_finset_left, Finset.coe_bunionᵢ, Set.unionᵢ_subset_iff] at h
    exact congr rfl (funext fun i => ih i (h i (Finset.mem_univ i)))
#align first_order.language.term.realize_restrict_var_left FirstOrder.Language.Term.realize_restrictVarLeft

/- warning: first_order.language.term.realize_constants_to_vars -> FirstOrder.Language.Term.realize_constantsToVars is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} [_inst_4 : FirstOrder.Language.Structure.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M] [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, max u1 u4, u2, u3} L (FirstOrder.Language.withConstants.{u1, u2, u4} L α) (FirstOrder.Language.lhomWithConstants.{u1, u2, u4} L α) M _inst_1 _inst_4] {t : FirstOrder.Language.Term.{max u1 u4, u2, u5} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) β} {v : β -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u1, u2, u3, max u4 u5} L M _inst_1 (Sum.{u4, u5} α β) (Sum.elim.{u4, u5, succ u3} α β M (fun (a : α) => (fun (a : Type.{max u1 u4}) (b : Type.{u3}) [self : HasLiftT.{succ (max u1 u4), succ u3} a b] => self.0) (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (HasLiftT.mk.{succ (max u1 u4), succ u3} (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (CoeTCₓ.coe.{succ (max u1 u4), succ u3} (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (FirstOrder.Language.hasCoeT.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4))) (FirstOrder.Language.con.{u1, u2, u4} L α a)) v) (FirstOrder.Language.Term.constantsToVars.{u1, u2, u5, u4} L β α t)) (FirstOrder.Language.Term.realize.{max u1 u4, u2, u3, u5} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 β v t)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} [_inst_4 : FirstOrder.Language.Structure.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M] [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, max u1 u4, u2, u3} L (FirstOrder.Language.withConstants.{u1, u2, u4} L α) (FirstOrder.Language.lhomWithConstants.{u1, u2, u4} L α) M _inst_1 _inst_4] {t : FirstOrder.Language.Term.{max u1 u4, u2, u5} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) β} {v : β -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u1, u2, u3, max u5 u4} L M _inst_1 (Sum.{u4, u5} α β) (Sum.elim.{u4, u5, succ u3} α β M (fun (a : α) => FirstOrder.Language.constantMap.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 (FirstOrder.Language.con.{u1, u2, u4} L α a)) v) (FirstOrder.Language.Term.constantsToVars.{u1, u2, u5, u4} L β α t)) (FirstOrder.Language.Term.realize.{max u1 u4, u2, u3, u5} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 β v t)
Case conversion may be inaccurate. Consider using '#align first_order.language.term.realize_constants_to_vars FirstOrder.Language.Term.realize_constantsToVarsₓ'. -/
@[simp]
theorem realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].term β} {v : β → M} :
    t.constantsToVars.realize (Sum.elim (fun a => ↑(L.con a)) v) = t.realize v :=
  by
  induction' t with _ n f _ ih
  · simp
  · cases n
    · cases f
      · simp [ih]
      · simp only [realize, constants_to_vars, Sum.elim_inl, fun_map_eq_coe_constants]
        rfl
    · cases f
      · simp [ih]
      · exact isEmptyElim f
#align first_order.language.term.realize_constants_to_vars FirstOrder.Language.Term.realize_constantsToVars

/- warning: first_order.language.term.realize_vars_to_constants -> FirstOrder.Language.Term.realize_varsToConstants is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} [_inst_4 : FirstOrder.Language.Structure.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M] [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, max u1 u4, u2, u3} L (FirstOrder.Language.withConstants.{u1, u2, u4} L α) (FirstOrder.Language.lhomWithConstants.{u1, u2, u4} L α) M _inst_1 _inst_4] {t : FirstOrder.Language.Term.{u1, u2, max u4 u5} L (Sum.{u4, u5} α β)} {v : β -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{max u1 u4, u2, u3, u5} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 β v (FirstOrder.Language.Term.varsToConstants.{u1, u2, u5, u4} L β α t)) (FirstOrder.Language.Term.realize.{u1, u2, u3, max u4 u5} L M _inst_1 (Sum.{u4, u5} α β) (Sum.elim.{u4, u5, succ u3} α β M (fun (a : α) => (fun (a : Type.{max u1 u4}) (b : Type.{u3}) [self : HasLiftT.{succ (max u1 u4), succ u3} a b] => self.0) (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (HasLiftT.mk.{succ (max u1 u4), succ u3} (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (CoeTCₓ.coe.{succ (max u1 u4), succ u3} (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (FirstOrder.Language.hasCoeT.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4))) (FirstOrder.Language.con.{u1, u2, u4} L α a)) v) t)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} [_inst_4 : FirstOrder.Language.Structure.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M] [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, max u1 u4, u2, u3} L (FirstOrder.Language.withConstants.{u1, u2, u4} L α) (FirstOrder.Language.lhomWithConstants.{u1, u2, u4} L α) M _inst_1 _inst_4] {t : FirstOrder.Language.Term.{u1, u2, max u5 u4} L (Sum.{u4, u5} α β)} {v : β -> M}, Eq.{succ u3} M (FirstOrder.Language.Term.realize.{max u1 u4, u2, u3, u5} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 β v (FirstOrder.Language.Term.varsToConstants.{u1, u2, u5, u4} L β α t)) (FirstOrder.Language.Term.realize.{u1, u2, u3, max u5 u4} L M _inst_1 (Sum.{u4, u5} α β) (Sum.elim.{u4, u5, succ u3} α β M (fun (a : α) => FirstOrder.Language.constantMap.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 (FirstOrder.Language.con.{u1, u2, u4} L α a)) v) t)
Case conversion may be inaccurate. Consider using '#align first_order.language.term.realize_vars_to_constants FirstOrder.Language.Term.realize_varsToConstantsₓ'. -/
@[simp]
theorem realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.term (Sum α β)} {v : β → M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) :=
  by
  induction' t with ab n f ts ih
  · cases ab <;> simp [language.con]
  · simp [ih]
#align first_order.language.term.realize_vars_to_constants FirstOrder.Language.Term.realize_varsToConstants

#print FirstOrder.Language.Term.realize_constantsVarsEquivLeft /-
theorem realize_constantsVarsEquivLeft [L[[α]].Structure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].term (Sum β (Fin n))} {v : β → M}
    {xs : Fin n → M} :
    (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(L.con a)) v) xs) =
      t.realize (Sum.elim v xs) :=
  by
  simp only [constants_vars_equiv_left, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constants_vars_equiv_apply, relabel_equiv_symm_apply]
  refine' trans _ realize_constants_to_vars
  rcongr
  rcases x with (a | (b | i)) <;> simp
#align first_order.language.term.realize_constants_vars_equiv_left FirstOrder.Language.Term.realize_constantsVarsEquivLeft
-/

end Term

namespace Lhom

/- warning: first_order.language.Lhom.realize_on_term -> FirstOrder.Language.LHom.realize_onTerm is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u5, u6}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} [_inst_4 : FirstOrder.Language.Structure.{u5, u6, u3} L' M] (φ : FirstOrder.Language.LHom.{u1, u2, u5, u6} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u5, u6, u3} L L' φ M _inst_1 _inst_4] (t : FirstOrder.Language.Term.{u1, u2, u4} L α) (v : α -> M), Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u5, u6, u3, u4} L' M _inst_4 α v (FirstOrder.Language.LHom.onTerm.{u1, u2, u4, u5, u6} L L' α φ t)) (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 α v t)
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u2, u1}} {M : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] {α : Type.{u6}} [_inst_4 : FirstOrder.Language.Structure.{u2, u1, u5} L' M] (φ : FirstOrder.Language.LHom.{u3, u4, u2, u1} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u3, u4, u2, u1, u5} L L' φ M _inst_1 _inst_4] (t : FirstOrder.Language.Term.{u3, u4, u6} L α) (v : α -> M), Eq.{succ u5} M (FirstOrder.Language.Term.realize.{u2, u1, u5, u6} L' M _inst_4 α v (FirstOrder.Language.LHom.onTerm.{u3, u4, u6, u2, u1} L L' α φ t)) (FirstOrder.Language.Term.realize.{u3, u4, u5, u6} L M _inst_1 α v t)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.realize_on_term FirstOrder.Language.LHom.realize_onTermₓ'. -/
@[simp]
theorem realize_onTerm [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.term α)
    (v : α → M) : (φ.onTerm t).realize v = t.realize v :=
  by
  induction' t with _ n f ts ih
  · rfl
  · simp only [term.realize, Lhom.on_term, Lhom.map_on_function, ih]
#align first_order.language.Lhom.realize_on_term FirstOrder.Language.LHom.realize_onTerm

end Lhom

/- warning: first_order.language.hom.realize_term -> FirstOrder.Language.Hom.realize_term is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u5} L N] {α : Type.{u4}} (g : FirstOrder.Language.Hom.{u1, u2, u3, u5} L M N _inst_1 _inst_2) {t : FirstOrder.Language.Term.{u1, u2, u4} L α} {v : α -> M}, Eq.{succ u5} N (FirstOrder.Language.Term.realize.{u1, u2, u5, u4} L N _inst_2 α (Function.comp.{succ u4, succ u3, succ u5} α M N (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Hom.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Hom.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Hom.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g) v) t) (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Hom.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Hom.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Hom.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 α v t))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] {α : Type.{u5}} (g : FirstOrder.Language.Hom.{u2, u3, u4, u1} L M N _inst_1 _inst_2) {t : FirstOrder.Language.Term.{u2, u3, u5} L α} {v : α -> M}, Eq.{succ u1} N (FirstOrder.Language.Term.realize.{u2, u3, u1, u5} L N _inst_2 α (Function.comp.{succ u5, succ u4, succ u1} α M N (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Hom.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : M) => N) _x) (FirstOrder.Language.Hom.funLike.{u2, u3, u4, u1} L M N _inst_1 _inst_2) g) v) t) (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Hom.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : M) => N) _x) (FirstOrder.Language.Hom.funLike.{u2, u3, u4, u1} L M N _inst_1 _inst_2) g (FirstOrder.Language.Term.realize.{u2, u3, u4, u5} L M _inst_1 α v t))
Case conversion may be inaccurate. Consider using '#align first_order.language.hom.realize_term FirstOrder.Language.Hom.realize_termₓ'. -/
@[simp]
theorem Hom.realize_term (g : M →[L] N) {t : L.term α} {v : α → M} :
    t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  · rfl
  · rw [term.realize, term.realize, g.map_fun]
    refine' congr rfl _
    ext x
    simp [t_ih x]
#align first_order.language.hom.realize_term FirstOrder.Language.Hom.realize_term

/- warning: first_order.language.embedding.realize_term -> FirstOrder.Language.Embedding.realize_term is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u5} L N] {α : Type.{u4}} {v : α -> M} (t : FirstOrder.Language.Term.{u1, u2, u4} L α) (g : FirstOrder.Language.Embedding.{u1, u2, u3, u5} L M N _inst_1 _inst_2), Eq.{succ u5} N (FirstOrder.Language.Term.realize.{u1, u2, u5, u4} L N _inst_2 α (Function.comp.{succ u4, succ u3, succ u5} α M N (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Embedding.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Embedding.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Embedding.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g) v) t) (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Embedding.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Embedding.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Embedding.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 α v t))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] {α : Type.{u5}} {v : α -> M} (t : FirstOrder.Language.Term.{u2, u3, u5} L α) (g : FirstOrder.Language.Embedding.{u2, u3, u4, u1} L M N _inst_1 _inst_2), Eq.{succ u1} N (FirstOrder.Language.Term.realize.{u2, u3, u1, u5} L N _inst_2 α (Function.comp.{succ u5, succ u4, succ u1} α M N (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Embedding.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Embedding.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Embedding.embeddingLike.{u2, u3, u4, u1} L M N _inst_1 _inst_2)) g) v) t) (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Embedding.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Embedding.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Embedding.embeddingLike.{u2, u3, u4, u1} L M N _inst_1 _inst_2)) g (FirstOrder.Language.Term.realize.{u2, u3, u4, u5} L M _inst_1 α v t))
Case conversion may be inaccurate. Consider using '#align first_order.language.embedding.realize_term FirstOrder.Language.Embedding.realize_termₓ'. -/
@[simp]
theorem Embedding.realize_term {v : α → M} (t : L.term α) (g : M ↪[L] N) :
    t.realize (g ∘ v) = g (t.realize v) :=
  g.toHom.realize_term
#align first_order.language.embedding.realize_term FirstOrder.Language.Embedding.realize_term

/- warning: first_order.language.equiv.realize_term -> FirstOrder.Language.Equiv.realize_term is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u5} L N] {α : Type.{u4}} {v : α -> M} (t : FirstOrder.Language.Term.{u1, u2, u4} L α) (g : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2), Eq.{succ u5} N (FirstOrder.Language.Term.realize.{u1, u2, u5, u4} L N _inst_2 α (Function.comp.{succ u4, succ u3, succ u5} α M N (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g) v) t) (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 α v t))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] {α : Type.{u5}} {v : α -> M} (t : FirstOrder.Language.Term.{u2, u3, u5} L α) (g : FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2), Eq.{succ u1} N (FirstOrder.Language.Term.realize.{u2, u3, u1, u5} L N _inst_2 α (Function.comp.{succ u5, succ u4, succ u1} α M N (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2))) g) v) t) (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2))) g (FirstOrder.Language.Term.realize.{u2, u3, u4, u5} L M _inst_1 α v t))
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.realize_term FirstOrder.Language.Equiv.realize_termₓ'. -/
@[simp]
theorem Equiv.realize_term {v : α → M} (t : L.term α) (g : M ≃[L] N) :
    t.realize (g ∘ v) = g (t.realize v) :=
  g.toHom.realize_term
#align first_order.language.equiv.realize_term FirstOrder.Language.Equiv.realize_term

variable {L} {α} {n : ℕ}

namespace BoundedFormula

open Term

#print FirstOrder.Language.BoundedFormula.Realize /-
/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def Realize : ∀ {l} (f : L.BoundedFormula α l) (v : α → M) (xs : Fin l → M), Prop
  | _, falsum, v, xs => False
  | _, bounded_formula.equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, bounded_formula.rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, bounded_formula.imp f₁ f₂, v, xs => realize f₁ v xs → realize f₂ v xs
  | _, bounded_formula.all f, v, xs => ∀ x : M, realize f v (snoc xs x)
#align first_order.language.bounded_formula.realize FirstOrder.Language.BoundedFormula.Realize
-/

variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}

variable {v : α → M} {xs : Fin l → M}

#print FirstOrder.Language.BoundedFormula.realize_bot /-
@[simp]
theorem realize_bot : (⊥ : L.BoundedFormula α l).realize v xs ↔ False :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_bot FirstOrder.Language.BoundedFormula.realize_bot
-/

#print FirstOrder.Language.BoundedFormula.realize_not /-
@[simp]
theorem realize_not : φ.Not.realize v xs ↔ ¬φ.realize v xs :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_not FirstOrder.Language.BoundedFormula.realize_not
-/

#print FirstOrder.Language.BoundedFormula.realize_bdEqual /-
@[simp]
theorem realize_bdEqual (t₁ t₂ : L.term (Sum α (Fin l))) :
    (t₁.bdEqual t₂).realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_bd_equal FirstOrder.Language.BoundedFormula.realize_bdEqual
-/

#print FirstOrder.Language.BoundedFormula.realize_top /-
@[simp]
theorem realize_top : (⊤ : L.BoundedFormula α l).realize v xs ↔ True := by simp [Top.top]
#align first_order.language.bounded_formula.realize_top FirstOrder.Language.BoundedFormula.realize_top
-/

#print FirstOrder.Language.BoundedFormula.realize_inf /-
@[simp]
theorem realize_inf : (φ ⊓ ψ).realize v xs ↔ φ.realize v xs ∧ ψ.realize v xs := by
  simp [Inf.inf, realize]
#align first_order.language.bounded_formula.realize_inf FirstOrder.Language.BoundedFormula.realize_inf
-/

#print FirstOrder.Language.BoundedFormula.realize_foldr_inf /-
@[simp]
theorem realize_foldr_inf (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊓ ·) ⊤).realize v xs ↔ ∀ φ ∈ l, BoundedFormula.Realize φ v xs :=
  by
  induction' l with φ l ih
  · simp
  · simp [ih]
#align first_order.language.bounded_formula.realize_foldr_inf FirstOrder.Language.BoundedFormula.realize_foldr_inf
-/

#print FirstOrder.Language.BoundedFormula.realize_imp /-
@[simp]
theorem realize_imp : (φ.imp ψ).realize v xs ↔ φ.realize v xs → ψ.realize v xs := by
  simp only [realize]
#align first_order.language.bounded_formula.realize_imp FirstOrder.Language.BoundedFormula.realize_imp
-/

#print FirstOrder.Language.BoundedFormula.realize_rel /-
@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.term _} :
    (R.BoundedFormula ts).realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_rel FirstOrder.Language.BoundedFormula.realize_rel
-/

#print FirstOrder.Language.BoundedFormula.realize_rel₁ /-
@[simp]
theorem realize_rel₁ {R : L.Relations 1} {t : L.term _} :
    (R.boundedFormula₁ t).realize v xs ↔ RelMap R ![t.realize (Sum.elim v xs)] :=
  by
  rw [relations.bounded_formula₁, realize_rel, iff_eq_eq]
  refine' congr rfl (funext fun _ => _)
  simp only [Matrix.cons_val_fin_one]
#align first_order.language.bounded_formula.realize_rel₁ FirstOrder.Language.BoundedFormula.realize_rel₁
-/

#print FirstOrder.Language.BoundedFormula.realize_rel₂ /-
@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.term _} :
    (R.boundedFormula₂ t₁ t₂).realize v xs ↔
      RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] :=
  by
  rw [relations.bounded_formula₂, realize_rel, iff_eq_eq]
  refine' congr rfl (funext (Fin.cases _ _))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
#align first_order.language.bounded_formula.realize_rel₂ FirstOrder.Language.BoundedFormula.realize_rel₂
-/

#print FirstOrder.Language.BoundedFormula.realize_sup /-
@[simp]
theorem realize_sup : (φ ⊔ ψ).realize v xs ↔ φ.realize v xs ∨ ψ.realize v xs :=
  by
  simp only [realize, Sup.sup, realize_not, eq_iff_iff]
  tauto
#align first_order.language.bounded_formula.realize_sup FirstOrder.Language.BoundedFormula.realize_sup
-/

/- warning: first_order.language.bounded_formula.realize_foldr_sup -> FirstOrder.Language.BoundedFormula.realize_foldr_sup is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} (l : List.{max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n)) (v : α -> M) (xs : (Fin n) -> M), Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n (List.foldr.{max u1 u2 u4, max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (Sup.sup.{max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (FirstOrder.Language.BoundedFormula.hasSup.{u1, u2, u4} L α n)) (Bot.bot.{max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (FirstOrder.Language.BoundedFormula.hasBot.{u1, u2, u4} L α n)) l) v xs) (Exists.{succ (max u1 u2 u4)} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (fun (φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) => Exists.{0} (Membership.Mem.{max u1 u2 u4, max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (List.{max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n)) (List.hasMem.{max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n)) φ l) (fun (H : Membership.Mem.{max u1 u2 u4, max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (List.{max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n)) (List.hasMem.{max u1 u2 u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n)) φ l) => FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v xs)))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} (l : List.{max (max u1 u2) u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n)) (v : α -> M) (xs : (Fin n) -> M), Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n (List.foldr.{max (max u1 u4) u2, max (max u1 u4) u2} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (fun (x._@.Mathlib.ModelTheory.Semantics._hyg.4548 : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (x._@.Mathlib.ModelTheory.Semantics._hyg.4550 : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) => Sup.sup.{max (max u1 u4) u2} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (FirstOrder.Language.BoundedFormula.instSupBoundedFormula.{u1, u2, u4} L α n) x._@.Mathlib.ModelTheory.Semantics._hyg.4548 x._@.Mathlib.ModelTheory.Semantics._hyg.4550) (Bot.bot.{max (max u1 u4) u2} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (FirstOrder.Language.BoundedFormula.instBotBoundedFormula.{u1, u2, u4} L α n)) l) v xs) (Exists.{succ (max (max u1 u4) u2)} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (fun (φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) => And (Membership.mem.{max (max u1 u4) u2, max (max u1 u4) u2} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) (List.{max (max u1 u2) u4} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n)) (List.instMembershipList.{max (max u1 u4) u2} (FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n)) φ l) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v xs)))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.realize_foldr_sup FirstOrder.Language.BoundedFormula.realize_foldr_supₓ'. -/
@[simp]
theorem realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊔ ·) ⊥).realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs :=
  by
  induction' l with φ l ih
  · simp
  ·
    simp_rw [List.foldr_cons, realize_sup, ih, exists_prop, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]
#align first_order.language.bounded_formula.realize_foldr_sup FirstOrder.Language.BoundedFormula.realize_foldr_sup

#print FirstOrder.Language.BoundedFormula.realize_all /-
@[simp]
theorem realize_all : (all θ).realize v xs ↔ ∀ a : M, θ.realize v (Fin.snoc xs a) :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_all FirstOrder.Language.BoundedFormula.realize_all
-/

#print FirstOrder.Language.BoundedFormula.realize_ex /-
@[simp]
theorem realize_ex : θ.ex.realize v xs ↔ ∃ a : M, θ.realize v (Fin.snoc xs a) :=
  by
  rw [bounded_formula.ex, realize_not, realize_all, not_forall]
  simp_rw [realize_not, Classical.not_not]
#align first_order.language.bounded_formula.realize_ex FirstOrder.Language.BoundedFormula.realize_ex
-/

#print FirstOrder.Language.BoundedFormula.realize_iff /-
@[simp]
theorem realize_iff : (φ.Iff ψ).realize v xs ↔ (φ.realize v xs ↔ ψ.realize v xs) := by
  simp only [bounded_formula.iff, realize_inf, realize_imp, and_imp, ← iff_def]
#align first_order.language.bounded_formula.realize_iff FirstOrder.Language.BoundedFormula.realize_iff
-/

/- warning: first_order.language.bounded_formula.realize_cast_le_of_eq -> FirstOrder.Language.BoundedFormula.realize_castLe_of_eq is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {m : Nat} {n : Nat} (h : Eq.{1} Nat m n) {h' : LE.le.{0} Nat Nat.hasLe m n} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α m} {v : α -> M} {xs : (Fin n) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n (FirstOrder.Language.BoundedFormula.castLE.{u1, u2, u4} L α m n h' φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α m φ v (Function.comp.{1, 1, succ u3} (Fin m) (Fin n) M xs (coeFn.{1, 1} (OrderIso.{0, 0} (Fin m) (Fin n) (Fin.hasLe m) (Fin.hasLe n)) (fun (_x : RelIso.{0, 0} (Fin m) (Fin n) (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{0} (Fin n) (Fin.hasLe n))) => (Fin m) -> (Fin n)) (RelIso.hasCoeToFun.{0, 0} (Fin m) (Fin n) (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{0} (Fin n) (Fin.hasLe n))) (Fin.cast m n h))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {m : Nat} {n : Nat} (h : Eq.{1} Nat m n) {h' : LE.le.{0} Nat instLENat m n} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α m} {v : α -> M} {xs : (Fin n) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n (FirstOrder.Language.BoundedFormula.castLE.{u1, u2, u4} L α m n h' φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α m φ v (Function.comp.{1, 1, succ u3} (Fin m) (Fin n) M xs (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} (Fin m) (Fin n) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Fin m) (fun (_x : Fin m) => Fin n) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} (Fin m) (Fin n) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Fin m) (Fin n) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{0, 0} (Fin m) (Fin n) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) (Fin.cast m n h))))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.realize_cast_le_of_eq FirstOrder.Language.BoundedFormula.realize_castLe_of_eqₓ'. -/
theorem realize_castLe_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} {φ : L.BoundedFormula α m}
    {v : α → M} {xs : Fin n → M} : (φ.castLE h').realize v xs ↔ φ.realize v (xs ∘ Fin.cast h) :=
  by
  subst h
  simp only [cast_le_rfl, cast_refl, OrderIso.coe_refl, Function.comp.right_id]
#align first_order.language.bounded_formula.realize_cast_le_of_eq FirstOrder.Language.BoundedFormula.realize_castLe_of_eq

/- warning: first_order.language.bounded_formula.realize_map_term_rel_id -> FirstOrder.Language.BoundedFormula.realize_mapTermRel_id is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u6, u7}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} [_inst_4 : FirstOrder.Language.Structure.{u6, u7, u3} L' M] {ft : forall (n : Nat), (FirstOrder.Language.Term.{u1, u2, u4} L (Sum.{u4, 0} α (Fin n))) -> (FirstOrder.Language.Term.{u6, u7, u5} L' (Sum.{u5, 0} β (Fin n)))} {fr : forall (n : Nat), (FirstOrder.Language.Relations.{u1, u2} L n) -> (FirstOrder.Language.Relations.{u6, u7} L' n)} {n : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {v : α -> M} {v' : β -> M} {xs : (Fin n) -> M}, (forall (n : Nat) (t : FirstOrder.Language.Term.{u1, u2, u4} L (Sum.{u4, 0} α (Fin n))) (xs : (Fin n) -> M), Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u6, u7, u3, u5} L' M _inst_4 (Sum.{u5, 0} β (Fin n)) (Sum.elim.{u5, 0, succ u3} β (Fin n) M v' xs) (ft n t)) (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 (Sum.{u4, 0} α (Fin n)) (Sum.elim.{u4, 0, succ u3} α (Fin n) M v xs) t)) -> (forall (n : Nat) (R : FirstOrder.Language.Relations.{u1, u2} L n) (x : (Fin n) -> M), Eq.{1} Prop (FirstOrder.Language.Structure.RelMap.{u6, u7, u3} L' M _inst_4 n (fr n R) x) (FirstOrder.Language.Structure.RelMap.{u1, u2, u3} L M _inst_1 n R x)) -> (Iff (FirstOrder.Language.BoundedFormula.Realize.{u6, u7, u3, u5} L' M _inst_4 β n (FirstOrder.Language.BoundedFormula.mapTermRel.{u1, u2, u4, u5, u6, u7} L L' α β (fun (n : Nat) => n) ft fr (fun (_x : Nat) => id.{succ (max u6 u7 u5)} (FirstOrder.Language.BoundedFormula.{u6, u7, u5} L' β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) _x (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) n φ) v' xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v xs))
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u2, u1}} {M : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] {α : Type.{u6}} {β : Type.{u7}} [_inst_4 : FirstOrder.Language.Structure.{u2, u1, u5} L' M] {ft : forall (n : Nat), (FirstOrder.Language.Term.{u3, u4, u6} L (Sum.{u6, 0} α (Fin n))) -> (FirstOrder.Language.Term.{u2, u1, u7} L' (Sum.{u7, 0} β (Fin n)))} {fr : forall (n : Nat), (FirstOrder.Language.Relations.{u3, u4} L n) -> (FirstOrder.Language.Relations.{u2, u1} L' n)} {n : Nat} {φ : FirstOrder.Language.BoundedFormula.{u3, u4, u6} L α n} {v : α -> M} {v' : β -> M} {xs : (Fin n) -> M}, (forall (n : Nat) (t : FirstOrder.Language.Term.{u3, u4, u6} L (Sum.{u6, 0} α (Fin n))) (xs : (Fin n) -> M), Eq.{succ u5} M (FirstOrder.Language.Term.realize.{u2, u1, u5, u7} L' M _inst_4 (Sum.{u7, 0} β (Fin n)) (Sum.elim.{u7, 0, succ u5} β (Fin n) M v' xs) (ft n t)) (FirstOrder.Language.Term.realize.{u3, u4, u5, u6} L M _inst_1 (Sum.{u6, 0} α (Fin n)) (Sum.elim.{u6, 0, succ u5} α (Fin n) M v xs) t)) -> (forall (n : Nat) (R : FirstOrder.Language.Relations.{u3, u4} L n) (x : (Fin n) -> M), Eq.{1} Prop (FirstOrder.Language.Structure.RelMap.{u2, u1, u5} L' M _inst_4 n (fr n R) x) (FirstOrder.Language.Structure.RelMap.{u3, u4, u5} L M _inst_1 n R x)) -> (Iff (FirstOrder.Language.BoundedFormula.Realize.{u2, u1, u5, u7} L' M _inst_4 β n (FirstOrder.Language.BoundedFormula.mapTermRel.{u3, u4, u6, u7, u2, u1} L L' α β (fun (n : Nat) => n) ft fr (fun (_x : Nat) => id.{max (max (succ u7) (succ u1)) (succ u2)} (FirstOrder.Language.BoundedFormula.{u2, u1, u7} L' β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) _x (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) n φ) v' xs) (FirstOrder.Language.BoundedFormula.Realize.{u3, u4, u5, u6} L M _inst_1 α n φ v xs))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.realize_map_term_rel_id FirstOrder.Language.BoundedFormula.realize_mapTermRel_idₓ'. -/
theorem realize_mapTermRel_id [L'.Structure M]
    {ft : ∀ n, L.term (Sum α (Fin n)) → L'.term (Sum β (Fin n))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n} {v : α → M}
    {v' : β → M} {xs : Fin n → M}
    (h1 :
      ∀ (n) (t : L.term (Sum α (Fin n))) (xs : Fin n → M),
        (ft n t).realize (Sum.elim v' xs) = t.realize (Sum.elim v xs))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x) :
    (φ.mapTermRel ft fr fun _ => id).realize v' xs ↔ φ.realize v xs :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih
  · rfl
  · simp [map_term_rel, realize, h1]
  · simp [map_term_rel, realize, h1, h2]
  · simp [map_term_rel, realize, ih1, ih2]
  · simp only [map_term_rel, realize, ih, id.def]
#align first_order.language.bounded_formula.realize_map_term_rel_id FirstOrder.Language.BoundedFormula.realize_mapTermRel_id

/- warning: first_order.language.bounded_formula.realize_map_term_rel_add_cast_le -> FirstOrder.Language.BoundedFormula.realize_mapTermRel_add_castLe is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u6, u7}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} [_inst_4 : FirstOrder.Language.Structure.{u6, u7, u3} L' M] {k : Nat} {ft : forall (n : Nat), (FirstOrder.Language.Term.{u1, u2, u4} L (Sum.{u4, 0} α (Fin n))) -> (FirstOrder.Language.Term.{u6, u7, u5} L' (Sum.{u5, 0} β (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n))))} {fr : forall (n : Nat), (FirstOrder.Language.Relations.{u1, u2} L n) -> (FirstOrder.Language.Relations.{u6, u7} L' n)} {n : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} (v : forall {n : Nat}, ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) -> M) -> α -> M) {v' : β -> M} (xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) -> M), (forall (n : Nat) (t : FirstOrder.Language.Term.{u1, u2, u4} L (Sum.{u4, 0} α (Fin n))) (xs' : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) -> M), Eq.{succ u3} M (FirstOrder.Language.Term.realize.{u6, u7, u3, u5} L' M _inst_4 (Sum.{u5, 0} β (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n))) (Sum.elim.{u5, 0, succ u3} β (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) M v' xs') (ft n t)) (FirstOrder.Language.Term.realize.{u1, u2, u3, u4} L M _inst_1 (Sum.{u4, 0} α (Fin n)) (Sum.elim.{u4, 0, succ u3} α (Fin n) M (v n xs') (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) M xs' (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)))) (Fin.natAdd k n)))) t)) -> (forall (n : Nat) (R : FirstOrder.Language.Relations.{u1, u2} L n) (x : (Fin n) -> M), Eq.{1} Prop (FirstOrder.Language.Structure.RelMap.{u6, u7, u3} L' M _inst_4 n (fr n R) x) (FirstOrder.Language.Structure.RelMap.{u1, u2, u3} L M _inst_1 n R x)) -> (forall (n : Nat) (xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) -> M) (x : M), Eq.{max (succ u4) (succ u3)} (α -> M) (v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Fin.snoc.{u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n) (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => M) xs x)) (v n xs)) -> (Iff (FirstOrder.Language.BoundedFormula.Realize.{u6, u7, u3, u5} L' M _inst_4 β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n) (FirstOrder.Language.BoundedFormula.mapTermRel.{u1, u2, u4, u5, u6, u7} L L' α β (fun (n : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n) ft fr (fun (n : Nat) => FirstOrder.Language.BoundedFormula.castLE.{u6, u7, u5} L' β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.le.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat Nat.addSemigroup)) k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat Nat.addSemigroup)) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat Nat.addSemigroup)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat Nat.addSemigroup)) k n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.symm.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat Nat.addSemigroup)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat Nat.addSemigroup)) k n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat Nat.addSemigroup)) k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat Nat.addSemigroup)) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (add_assoc.{0} Nat Nat.addSemigroup k n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) n φ) v' xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ (v n xs) (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) M xs (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k n)))) (Fin.natAdd k n)))))
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u2, u1}} {M : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] {α : Type.{u6}} {β : Type.{u7}} [_inst_4 : FirstOrder.Language.Structure.{u2, u1, u5} L' M] {k : Nat} {ft : forall (n : Nat), (FirstOrder.Language.Term.{u3, u4, u6} L (Sum.{u6, 0} α (Fin n))) -> (FirstOrder.Language.Term.{u2, u1, u7} L' (Sum.{u7, 0} β (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n))))} {fr : forall (n : Nat), (FirstOrder.Language.Relations.{u3, u4} L n) -> (FirstOrder.Language.Relations.{u2, u1} L' n)} {n : Nat} {φ : FirstOrder.Language.BoundedFormula.{u3, u4, u6} L α n} (v : forall {n : Nat}, ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) -> M) -> α -> M) {v' : β -> M} (xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) -> M), (forall (n : Nat) (t : FirstOrder.Language.Term.{u3, u4, u6} L (Sum.{u6, 0} α (Fin n))) (xs' : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) -> M), Eq.{succ u5} M (FirstOrder.Language.Term.realize.{u2, u1, u5, u7} L' M _inst_4 (Sum.{u7, 0} β (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n))) (Sum.elim.{u7, 0, succ u5} β (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) M v' xs') (ft n t)) (FirstOrder.Language.Term.realize.{u3, u4, u5, u6} L M _inst_1 (Sum.{u6, 0} α (Fin n)) (Sum.elim.{u6, 0, succ u5} α (Fin n) M (v n xs') (Function.comp.{1, 1, succ u5} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) M xs' (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (Fin.natAdd k n)))) t)) -> (forall (n : Nat) (R : FirstOrder.Language.Relations.{u3, u4} L n) (x : (Fin n) -> M), Eq.{1} Prop (FirstOrder.Language.Structure.RelMap.{u2, u1, u5} L' M _inst_4 n (fr n R) x) (FirstOrder.Language.Structure.RelMap.{u3, u4, u5} L M _inst_1 n R x)) -> (forall (n : Nat) (xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) -> M) (x : M), Eq.{max (succ u6) (succ u5)} (α -> M) (v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fin.snoc.{u5} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n) (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => M) xs x)) (v n xs)) -> (Iff (FirstOrder.Language.BoundedFormula.Realize.{u2, u1, u5, u7} L' M _inst_4 β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n) (FirstOrder.Language.BoundedFormula.mapTermRel.{u3, u4, u6, u7, u2, u1} L L' α β (fun (n : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n) ft fr (fun (n : Nat) => FirstOrder.Language.BoundedFormula.castLE.{u2, u1, u7} L' β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.le.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat Nat.addSemigroup)) k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat Nat.addSemigroup)) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat Nat.addSemigroup)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat Nat.addSemigroup)) k n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.symm.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat Nat.addSemigroup)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat Nat.addSemigroup)) k n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat Nat.addSemigroup)) k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat Nat.addSemigroup)) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (add_assoc.{0} Nat Nat.addSemigroup k n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) n φ) v' xs) (FirstOrder.Language.BoundedFormula.Realize.{u3, u4, u5, u6} L M _inst_1 α n φ (v n xs) (Function.comp.{1, 1, succ u5} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) M xs (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k n)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (Fin.natAdd k n)))))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.realize_map_term_rel_add_cast_le FirstOrder.Language.BoundedFormula.realize_mapTermRel_add_castLeₓ'. -/
theorem realize_mapTermRel_add_castLe [L'.Structure M] {k : ℕ}
    {ft : ∀ n, L.term (Sum α (Fin n)) → L'.term (Sum β (Fin (k + n)))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n}
    (v : ∀ {n}, (Fin (k + n) → M) → α → M) {v' : β → M} (xs : Fin (k + n) → M)
    (h1 :
      ∀ (n) (t : L.term (Sum α (Fin n))) (xs' : Fin (k + n) → M),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x)
    (hv : ∀ (n) (xs : Fin (k + n) → M) (x : M), @v (n + 1) (snoc xs x : Fin _ → M) = v xs) :
    (φ.mapTermRel ft fr fun n => castLE (add_assoc _ _ _).symm.le).realize v' xs ↔
      φ.realize (v xs) (xs ∘ Fin.natAdd _) :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih
  · rfl
  · simp [map_term_rel, realize, h1]
  · simp [map_term_rel, realize, h1, h2]
  · simp [map_term_rel, realize, ih1, ih2]
  · simp [map_term_rel, realize, ih, hv]
#align first_order.language.bounded_formula.realize_map_term_rel_add_cast_le FirstOrder.Language.BoundedFormula.realize_mapTermRel_add_castLe

/- warning: first_order.language.bounded_formula.realize_relabel -> FirstOrder.Language.BoundedFormula.realize_relabel is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} {m : Nat} {n : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {g : α -> (Sum.{u5, 0} β (Fin m))} {v : β -> M} {xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u5} L M _inst_1 β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n) (FirstOrder.Language.BoundedFormula.relabel.{u1, u2, u4, u5} L α β m g n φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ (Function.comp.{succ u4, succ u5, succ u3} α (Sum.{u5, 0} β (Fin m)) M (Sum.elim.{u5, 0, succ u3} β (Fin m) M v (Function.comp.{1, 1, succ u3} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) M xs (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe m) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (fun (_x : RelEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) => (Fin m) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) (Fin.castAdd m n)))) g) (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) M xs (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) (Fin.natAdd m n))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {β : Type.{u5}} {m : Nat} {n : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {g : α -> (Sum.{u5, 0} β (Fin m))} {v : β -> M} {xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u5} L M _inst_1 β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n) (FirstOrder.Language.BoundedFormula.relabel.{u1, u2, u4, u5} L α β m g n φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ (Function.comp.{succ u4, succ u5, succ u3} α (Sum.{u5, 0} β (Fin m)) M (Sum.elim.{u5, 0, succ u3} β (Fin m) M v (Function.comp.{1, 1, succ u3} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) M xs (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin m) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin m) (fun (_x : Fin m) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin m) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin m) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (Lattice.toInf.{0} (Fin m) (DistribLattice.toLattice.{0} (Fin m) (instDistribLattice.{0} (Fin m) (Fin.instLinearOrderFin m)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))))) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin m) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (DistribLattice.toLattice.{0} (Fin m) (instDistribLattice.{0} (Fin m) (Fin.instLinearOrderFin m))) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)))) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin m) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (Fin.instLinearOrderFin m) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)))) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))))) (Fin.castAdd m n)))) g) (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) M xs (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (Fin.natAdd m n))))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.realize_relabel FirstOrder.Language.BoundedFormula.realize_relabelₓ'. -/
theorem realize_relabel {m n : ℕ} {φ : L.BoundedFormula α n} {g : α → Sum β (Fin m)} {v : β → M}
    {xs : Fin (m + n) → M} :
    (φ.relabel g).realize v xs ↔
      φ.realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) :=
  by rw [relabel, realize_map_term_rel_add_cast_le] <;> intros <;> simp
#align first_order.language.bounded_formula.realize_relabel FirstOrder.Language.BoundedFormula.realize_relabel

/- warning: first_order.language.bounded_formula.realize_lift_at -> FirstOrder.Language.BoundedFormula.realize_liftAt is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} {n' : Nat} {m : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {v : α -> M} {xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) -> M}, (LE.le.{0} Nat Nat.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n') (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n') (FirstOrder.Language.BoundedFormula.liftAt.{u1, u2, u4} L α n n' m φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) M xs (fun (i : Fin n) => ite.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LT.lt.{0} Nat Nat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) m) (Nat.decidableLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) m) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')))) (Fin.castAdd n n') i) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n'))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n n')))) (Fin.addNat n n') i)))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} {n' : Nat} {m : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {v : α -> M} {xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) -> M}, (LE.le.{0} Nat instLENat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n') (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n') (FirstOrder.Language.BoundedFormula.liftAt.{u1, u2, u4} L α n n' m φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) M xs (fun (i : Fin n) => ite.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (LT.lt.{0} Nat instLTNat (Fin.val n i) m) (Nat.decLt (Fin.val n i) m) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))))) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')))) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin n) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')))) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))))) (Fin.castAdd n n') i) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))))) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')))) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n'))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin n) (DistribLattice.toLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instDistribLattice.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (Fin.instLinearOrderFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')))) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n n')) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))))) (Fin.addNat n n') i)))))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.realize_lift_at FirstOrder.Language.BoundedFormula.realize_liftAtₓ'. -/
theorem realize_liftAt {n n' m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + n') → M}
    (hmn : m + n' ≤ n + 1) :
    (φ.liftAt n' m).realize v xs ↔
      φ.realize v (xs ∘ fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat n' i) :=
  by
  rw [lift_at]
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 k _ ih3
  · simp [realize, map_term_rel]
  · simp [realize, map_term_rel, realize_rel, realize_lift_at, Sum.elim_comp_map]
  · simp [realize, map_term_rel, realize_rel, realize_lift_at, Sum.elim_comp_map]
  · simp only [map_term_rel, realize, ih1 hmn, ih2 hmn]
  · have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
    simp only [map_term_rel, realize, realize_cast_le_of_eq h, ih3 (hmn.trans k.succ.le_succ)]
    refine' forall_congr' fun x => iff_eq_eq.mpr (congr rfl (funext (Fin.lastCases _ fun i => _)))
    · simp only [Function.comp_apply, coe_last, snoc_last]
      by_cases k < m
      · rw [if_pos h]
        refine' (congr rfl (ext _)).trans (snoc_last _ _)
        simp only [coe_cast, coe_cast_add, coe_last, self_eq_add_right]
        refine'
          le_antisymm (le_of_add_le_add_left ((hmn.trans (Nat.succ_le_of_lt h)).trans _)) n'.zero_le
        rw [add_zero]
      · rw [if_neg h]
        refine' (congr rfl (ext _)).trans (snoc_last _ _)
        simp
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      refine' (congr rfl (ext _)).trans (snoc_cast_succ _ _ _)
      simp only [cast_refl, coe_cast_succ, OrderIso.coe_refl, id.def]
      split_ifs <;> simp
#align first_order.language.bounded_formula.realize_lift_at FirstOrder.Language.BoundedFormula.realize_liftAt

/- warning: first_order.language.bounded_formula.realize_lift_at_one -> FirstOrder.Language.BoundedFormula.realize_liftAt_one is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} {m : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {v : α -> M} {xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> M}, (LE.le.{0} Nat Nat.hasLe m n) -> (Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (FirstOrder.Language.BoundedFormula.liftAt.{u1, u2, u4} L α n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) m φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) M xs (fun (i : Fin n) => ite.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LT.lt.{0} Nat Nat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) m) (Nat.decidableLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) m) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i) (Fin.succ n i)))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} {m : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {v : α -> M} {xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> M}, (LE.le.{0} Nat instLENat m n) -> (Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (FirstOrder.Language.BoundedFormula.liftAt.{u1, u2, u4} L α n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) m φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) M xs (fun (i : Fin n) => ite.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (LT.lt.{0} Nat instLTNat (Fin.val n i) m) (Nat.decLt (Fin.val n i) m) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))))) (Fin.castSucc n) i) (Fin.succ n i)))))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.realize_lift_at_one FirstOrder.Language.BoundedFormula.realize_liftAt_oneₓ'. -/
theorem realize_liftAt_one {n m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + 1) → M}
    (hmn : m ≤ n) :
    (φ.liftAt 1 m).realize v xs ↔
      φ.realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) :=
  by simp_rw [realize_lift_at (add_le_add_right hmn 1), cast_succ, add_nat_one]
#align first_order.language.bounded_formula.realize_lift_at_one FirstOrder.Language.BoundedFormula.realize_liftAt_one

/- warning: first_order.language.bounded_formula.realize_lift_at_one_self -> FirstOrder.Language.BoundedFormula.realize_liftAt_one_self is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {v : α -> M} {xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (FirstOrder.Language.BoundedFormula.liftAt.{u1, u2, u4} L α n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) n φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) M xs (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} {n : Nat} {φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n} {v : α -> M} {xs : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (FirstOrder.Language.BoundedFormula.liftAt.{u1, u2, u4} L α n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) n φ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v (Function.comp.{1, 1, succ u3} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) M xs (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))))) (Fin.castSucc n))))
Case conversion may be inaccurate. Consider using '#align first_order.language.bounded_formula.realize_lift_at_one_self FirstOrder.Language.BoundedFormula.realize_liftAt_one_selfₓ'. -/
@[simp]
theorem realize_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin (n + 1) → M} : (φ.liftAt 1 n).realize v xs ↔ φ.realize v (xs ∘ castSucc) :=
  by
  rw [realize_lift_at_one (refl n), iff_eq_eq]
  refine' congr rfl (congr rfl (funext fun i => _))
  rw [if_pos i.is_lt]
#align first_order.language.bounded_formula.realize_lift_at_one_self FirstOrder.Language.BoundedFormula.realize_liftAt_one_self

#print FirstOrder.Language.BoundedFormula.realize_subst /-
theorem realize_subst {φ : L.BoundedFormula α n} {tf : α → L.term β} {v : β → M} {xs : Fin n → M} :
    (φ.subst tf).realize v xs ↔ φ.realize (fun a => (tf a).realize v) xs :=
  realize_mapTermRel_id
    (fun n t x => by
      rw [term.realize_subst]
      rcongr a
      · cases a
        · simp only [Sum.elim_inl, term.realize_relabel, Sum.elim_comp_inl]
        · rfl)
    (by simp)
#align first_order.language.bounded_formula.realize_subst FirstOrder.Language.BoundedFormula.realize_subst
-/

#print FirstOrder.Language.BoundedFormula.realize_restrictFreeVar /-
@[simp]
theorem realize_restrictFreeVar [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n} {s : Set α}
    (h : ↑φ.freeVarFinset ⊆ s) {v : α → M} {xs : Fin n → M} :
    (φ.restrictFreeVar (Set.inclusion h)).realize (v ∘ coe) xs ↔ φ.realize v xs :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [restrict_free_var, realize]
  · simp [restrict_free_var, realize]
  · simp [restrict_free_var, realize, ih1, ih2]
  · simp [restrict_free_var, realize, ih3]
#align first_order.language.bounded_formula.realize_restrict_free_var FirstOrder.Language.BoundedFormula.realize_restrictFreeVar
-/

#print FirstOrder.Language.BoundedFormula.realize_constantsVarsEquiv /-
theorem realize_constantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {φ : L[[α]].BoundedFormula β n} {v : β → M} {xs : Fin n → M} :
    (constantsVarsEquiv φ).realize (Sum.elim (fun a => ↑(L.con a)) v) xs ↔ φ.realize v xs :=
  by
  refine' realize_map_term_rel_id (fun n t xs => realize_constants_vars_equiv_left) fun n R xs => _
  rw [←
    (Lhom_with_constants L α).map_onRelation
      (Equiv.sumEmpty (L.relations n) ((constants_on α).Relations n) R) xs]
  rcongr
  cases R
  · simp
  · exact isEmptyElim R
#align first_order.language.bounded_formula.realize_constants_vars_equiv FirstOrder.Language.BoundedFormula.realize_constantsVarsEquiv
-/

#print FirstOrder.Language.BoundedFormula.realize_relabelEquiv /-
@[simp]
theorem realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β → M}
    {xs : Fin k → M} : (relabelEquiv g φ).realize v xs ↔ φ.realize (v ∘ g) xs :=
  by
  simp only [relabel_equiv, map_term_rel_equiv_apply, Equiv.coe_refl]
  refine' realize_map_term_rel_id (fun n t xs => _) fun _ _ _ => rfl
  simp only [relabel_equiv_apply, term.realize_relabel]
  refine' congr (congr rfl _) rfl
  ext (i | i) <;> rfl
#align first_order.language.bounded_formula.realize_relabel_equiv FirstOrder.Language.BoundedFormula.realize_relabelEquiv
-/

variable [Nonempty M]

#print FirstOrder.Language.BoundedFormula.realize_all_liftAt_one_self /-
theorem realize_all_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin n → M} : (φ.liftAt 1 n).all.realize v xs ↔ φ.realize v xs :=
  by
  inhabit M
  simp only [realize_all, realize_lift_at_one_self]
  refine' ⟨fun h => _, fun h a => _⟩
  · refine' (congr rfl (funext fun i => _)).mp (h default)
    simp
  · refine' (congr rfl (funext fun i => _)).mp h
    simp
#align first_order.language.bounded_formula.realize_all_lift_at_one_self FirstOrder.Language.BoundedFormula.realize_all_liftAt_one_self
-/

#print FirstOrder.Language.BoundedFormula.realize_toPrenexImpRight /-
theorem realize_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} : (φ.toPrenexImpRight ψ).realize v xs ↔ (φ.imp ψ).realize v xs :=
  by
  revert φ
  induction' hψ with _ _ hψ _ _ hψ ih _ _ hψ ih <;> intro φ hφ
  · rw [hψ.to_prenex_imp_right]
  · refine' trans (forall_congr' fun _ => ih hφ.lift_at) _
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
  · rw [to_prenex_imp_right, realize_ex]
    refine' trans (exists_congr fun _ => ih hφ.lift_at) _
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_ex]
    refine' ⟨_, fun h' => _⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
    · by_cases φ.realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩
#align first_order.language.bounded_formula.realize_to_prenex_imp_right FirstOrder.Language.BoundedFormula.realize_toPrenexImpRight
-/

#print FirstOrder.Language.BoundedFormula.realize_toPrenexImp /-
theorem realize_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} : (φ.toPrenexImp ψ).realize v xs ↔ (φ.imp ψ).realize v xs :=
  by
  revert ψ
  induction' hφ with _ _ hφ _ _ hφ ih _ _ hφ ih <;> intro ψ hψ
  · rw [hφ.to_prenex_imp]
    exact realize_to_prenex_imp_right hφ hψ
  · rw [to_prenex_imp, realize_ex]
    refine' trans (exists_congr fun _ => ih hψ.lift_at) _
    simp only [realize_imp, realize_lift_at_one_self, snoc_comp_cast_succ, realize_all]
    refine' ⟨_, fun h' => _⟩
    · rintro ⟨a, ha⟩ h
      exact ha (h a)
    · by_cases ψ.realize v xs
      · inhabit M
        exact ⟨default, fun h'' => h⟩
      · obtain ⟨a, ha⟩ := not_forall.1 (h ∘ h')
        exact ⟨a, fun h => (ha h).elim⟩
  · refine' trans (forall_congr' fun _ => ih hψ.lift_at) _
    simp
#align first_order.language.bounded_formula.realize_to_prenex_imp FirstOrder.Language.BoundedFormula.realize_toPrenexImp
-/

#print FirstOrder.Language.BoundedFormula.realize_toPrenex /-
@[simp]
theorem realize_toPrenex (φ : L.BoundedFormula α n) {v : α → M} :
    ∀ {xs : Fin n → M}, φ.toPrenex.realize v xs ↔ φ.realize v xs :=
  by
  refine'
    bounded_formula.rec_on φ (fun _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
      (fun _ _ _ _ _ => Iff.rfl) (fun _ f1 f2 h1 h2 _ => _) fun _ f h xs => _
  · rw [to_prenex, realize_to_prenex_imp f1.to_prenex_is_prenex f2.to_prenex_is_prenex, realize_imp,
      realize_imp, h1, h2]
    infer_instance
  · rw [realize_all, to_prenex, realize_all]
    exact forall_congr' fun a => h
#align first_order.language.bounded_formula.realize_to_prenex FirstOrder.Language.BoundedFormula.realize_toPrenex
-/

end BoundedFormula

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel

attribute [protected] bounded_formula.imp bounded_formula.all

namespace Lhom

open BoundedFormula

/- warning: first_order.language.Lhom.realize_on_bounded_formula -> FirstOrder.Language.LHom.realize_onBoundedFormula is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u5, u6}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} [_inst_4 : FirstOrder.Language.Structure.{u5, u6, u3} L' M] (φ : FirstOrder.Language.LHom.{u1, u2, u5, u6} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u5, u6, u3} L L' φ M _inst_1 _inst_4] {n : Nat} (ψ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) {v : α -> M} {xs : (Fin n) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u5, u6, u3, u4} L' M _inst_4 α n (FirstOrder.Language.LHom.onBoundedFormula.{u1, u2, u4, u5, u6} L L' α φ n ψ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n ψ v xs)
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u2, u1}} {M : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] {α : Type.{u6}} [_inst_4 : FirstOrder.Language.Structure.{u2, u1, u5} L' M] (φ : FirstOrder.Language.LHom.{u3, u4, u2, u1} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u3, u4, u2, u1, u5} L L' φ M _inst_1 _inst_4] {n : Nat} (ψ : FirstOrder.Language.BoundedFormula.{u3, u4, u6} L α n) {v : α -> M} {xs : (Fin n) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u2, u1, u5, u6} L' M _inst_4 α n (FirstOrder.Language.LHom.onBoundedFormula.{u3, u4, u6, u2, u1} L L' α φ n ψ) v xs) (FirstOrder.Language.BoundedFormula.Realize.{u3, u4, u5, u6} L M _inst_1 α n ψ v xs)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.realize_on_bounded_formula FirstOrder.Language.LHom.realize_onBoundedFormulaₓ'. -/
@[simp]
theorem realize_onBoundedFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] {n : ℕ}
    (ψ : L.BoundedFormula α n) {v : α → M} {xs : Fin n → M} :
    (φ.onBoundedFormula ψ).realize v xs ↔ ψ.realize v xs :=
  by
  induction' ψ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp only [on_bounded_formula, realize_bd_equal, realize_on_term]
    rfl
  · simp only [on_bounded_formula, realize_rel, realize_on_term, Lhom.map_on_relation]
    rfl
  · simp only [on_bounded_formula, ih1, ih2, realize_imp]
  · simp only [on_bounded_formula, ih3, realize_all]
#align first_order.language.Lhom.realize_on_bounded_formula FirstOrder.Language.LHom.realize_onBoundedFormula

end Lhom

attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel

attribute [protected] bounded_formula.imp bounded_formula.all

namespace Formula

#print FirstOrder.Language.Formula.Realize /-
/-- A formula can be evaluated as true or false by giving values to each free variable. -/
def Realize (φ : L.Formula α) (v : α → M) : Prop :=
  φ.realize v default
#align first_order.language.formula.realize FirstOrder.Language.Formula.Realize
-/

variable {M} {φ ψ : L.Formula α} {v : α → M}

#print FirstOrder.Language.Formula.realize_not /-
@[simp]
theorem realize_not : φ.Not.realize v ↔ ¬φ.realize v :=
  Iff.rfl
#align first_order.language.formula.realize_not FirstOrder.Language.Formula.realize_not
-/

#print FirstOrder.Language.Formula.realize_bot /-
@[simp]
theorem realize_bot : (⊥ : L.Formula α).realize v ↔ False :=
  Iff.rfl
#align first_order.language.formula.realize_bot FirstOrder.Language.Formula.realize_bot
-/

#print FirstOrder.Language.Formula.realize_top /-
@[simp]
theorem realize_top : (⊤ : L.Formula α).realize v ↔ True :=
  BoundedFormula.realize_top
#align first_order.language.formula.realize_top FirstOrder.Language.Formula.realize_top
-/

#print FirstOrder.Language.Formula.realize_inf /-
@[simp]
theorem realize_inf : (φ ⊓ ψ).realize v ↔ φ.realize v ∧ ψ.realize v :=
  BoundedFormula.realize_inf
#align first_order.language.formula.realize_inf FirstOrder.Language.Formula.realize_inf
-/

#print FirstOrder.Language.Formula.realize_imp /-
@[simp]
theorem realize_imp : (φ.imp ψ).realize v ↔ φ.realize v → ψ.realize v :=
  BoundedFormula.realize_imp
#align first_order.language.formula.realize_imp FirstOrder.Language.Formula.realize_imp
-/

#print FirstOrder.Language.Formula.realize_rel /-
@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.term α} :
    (R.Formula ts).realize v ↔ RelMap R fun i => (ts i).realize v :=
  BoundedFormula.realize_rel.trans (by simp)
#align first_order.language.formula.realize_rel FirstOrder.Language.Formula.realize_rel
-/

#print FirstOrder.Language.Formula.realize_rel₁ /-
@[simp]
theorem realize_rel₁ {R : L.Relations 1} {t : L.term _} :
    (R.formula₁ t).realize v ↔ RelMap R ![t.realize v] :=
  by
  rw [relations.formula₁, realize_rel, iff_eq_eq]
  refine' congr rfl (funext fun _ => _)
  simp only [Matrix.cons_val_fin_one]
#align first_order.language.formula.realize_rel₁ FirstOrder.Language.Formula.realize_rel₁
-/

#print FirstOrder.Language.Formula.realize_rel₂ /-
@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.term _} :
    (R.formula₂ t₁ t₂).realize v ↔ RelMap R ![t₁.realize v, t₂.realize v] :=
  by
  rw [relations.formula₂, realize_rel, iff_eq_eq]
  refine' congr rfl (funext (Fin.cases _ _))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
#align first_order.language.formula.realize_rel₂ FirstOrder.Language.Formula.realize_rel₂
-/

#print FirstOrder.Language.Formula.realize_sup /-
@[simp]
theorem realize_sup : (φ ⊔ ψ).realize v ↔ φ.realize v ∨ ψ.realize v :=
  BoundedFormula.realize_sup
#align first_order.language.formula.realize_sup FirstOrder.Language.Formula.realize_sup
-/

#print FirstOrder.Language.Formula.realize_iff /-
@[simp]
theorem realize_iff : (φ.Iff ψ).realize v ↔ (φ.realize v ↔ ψ.realize v) :=
  BoundedFormula.realize_iff
#align first_order.language.formula.realize_iff FirstOrder.Language.Formula.realize_iff
-/

#print FirstOrder.Language.Formula.realize_relabel /-
@[simp]
theorem realize_relabel {φ : L.Formula α} {g : α → β} {v : β → M} :
    (φ.relabel g).realize v ↔ φ.realize (v ∘ g) :=
  by
  rw [realize, realize, relabel, bounded_formula.realize_relabel, iff_eq_eq, Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)
#align first_order.language.formula.realize_relabel FirstOrder.Language.Formula.realize_relabel
-/

#print FirstOrder.Language.Formula.realize_relabel_sum_inr /-
theorem realize_relabel_sum_inr (φ : L.Formula (Fin n)) {v : Empty → M} {x : Fin n → M} :
    (BoundedFormula.relabel Sum.inr φ).realize v x ↔ φ.realize x := by
  rw [bounded_formula.realize_relabel, formula.realize, Sum.elim_comp_inr, Fin.castAdd_zero,
    cast_refl, OrderIso.coe_refl, Function.comp.right_id,
    Subsingleton.elim (x ∘ (nat_add n : Fin 0 → Fin n)) default]
#align first_order.language.formula.realize_relabel_sum_inr FirstOrder.Language.Formula.realize_relabel_sum_inr
-/

#print FirstOrder.Language.Formula.realize_equal /-
@[simp]
theorem realize_equal {t₁ t₂ : L.term α} {x : α → M} :
    (t₁.equal t₂).realize x ↔ t₁.realize x = t₂.realize x := by simp [term.equal, realize]
#align first_order.language.formula.realize_equal FirstOrder.Language.Formula.realize_equal
-/

#print FirstOrder.Language.Formula.realize_graph /-
@[simp]
theorem realize_graph {f : L.Functions n} {x : Fin n → M} {y : M} :
    (Formula.graph f).realize (Fin.cons y x : _ → M) ↔ funMap f x = y :=
  by
  simp only [formula.graph, term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]
#align first_order.language.formula.realize_graph FirstOrder.Language.Formula.realize_graph
-/

end Formula

/- warning: first_order.language.Lhom.realize_on_formula -> FirstOrder.Language.LHom.realize_onFormula is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u5, u6}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} [_inst_4 : FirstOrder.Language.Structure.{u5, u6, u3} L' M] (φ : FirstOrder.Language.LHom.{u1, u2, u5, u6} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u5, u6, u3} L L' φ M _inst_1 _inst_4] (ψ : FirstOrder.Language.Formula.{u1, u2, u4} L α) {v : α -> M}, Iff (FirstOrder.Language.Formula.Realize.{u5, u6, u3, u4} L' M _inst_4 α (FirstOrder.Language.LHom.onFormula.{u1, u2, u4, u5, u6} L L' α φ ψ) v) (FirstOrder.Language.Formula.Realize.{u1, u2, u3, u4} L M _inst_1 α ψ v)
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u2, u1}} {M : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] {α : Type.{u6}} [_inst_4 : FirstOrder.Language.Structure.{u2, u1, u5} L' M] (φ : FirstOrder.Language.LHom.{u3, u4, u2, u1} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u3, u4, u2, u1, u5} L L' φ M _inst_1 _inst_4] (ψ : FirstOrder.Language.Formula.{u3, u4, u6} L α) {v : α -> M}, Iff (FirstOrder.Language.Formula.Realize.{u2, u1, u5, u6} L' M _inst_4 α (FirstOrder.Language.LHom.onFormula.{u3, u4, u6, u2, u1} L L' α φ ψ) v) (FirstOrder.Language.Formula.Realize.{u3, u4, u5, u6} L M _inst_1 α ψ v)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.realize_on_formula FirstOrder.Language.LHom.realize_onFormulaₓ'. -/
@[simp]
theorem LHom.realize_onFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α)
    {v : α → M} : (φ.onFormula ψ).realize v ↔ ψ.realize v :=
  φ.realize_onBoundedFormula ψ
#align first_order.language.Lhom.realize_on_formula FirstOrder.Language.LHom.realize_onFormula

/- warning: first_order.language.Lhom.set_of_realize_on_formula -> FirstOrder.Language.LHom.setOf_realize_onFormula is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u5, u6}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {α : Type.{u4}} [_inst_4 : FirstOrder.Language.Structure.{u5, u6, u3} L' M] (φ : FirstOrder.Language.LHom.{u1, u2, u5, u6} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u5, u6, u3} L L' φ M _inst_1 _inst_4] (ψ : FirstOrder.Language.Formula.{u1, u2, u4} L α), Eq.{succ (max u4 u3)} (Set.{max u4 u3} (α -> M)) (setOf.{max u4 u3} (α -> M) (FirstOrder.Language.Formula.Realize.{u5, u6, u3, u4} L' M _inst_4 α (FirstOrder.Language.LHom.onFormula.{u1, u2, u4, u5, u6} L L' α φ ψ))) (setOf.{max u4 u3} (α -> M) (FirstOrder.Language.Formula.Realize.{u1, u2, u3, u4} L M _inst_1 α ψ))
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u2, u1}} {M : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] {α : Type.{u6}} [_inst_4 : FirstOrder.Language.Structure.{u2, u1, u5} L' M] (φ : FirstOrder.Language.LHom.{u3, u4, u2, u1} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u3, u4, u2, u1, u5} L L' φ M _inst_1 _inst_4] (ψ : FirstOrder.Language.Formula.{u3, u4, u6} L α), Eq.{max (succ u6) (succ u5)} (Set.{max u6 u5} (α -> M)) (setOf.{max u6 u5} (α -> M) (FirstOrder.Language.Formula.Realize.{u2, u1, u5, u6} L' M _inst_4 α (FirstOrder.Language.LHom.onFormula.{u3, u4, u6, u2, u1} L L' α φ ψ))) (setOf.{max u6 u5} (α -> M) (FirstOrder.Language.Formula.Realize.{u3, u4, u5, u6} L M _inst_1 α ψ))
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.set_of_realize_on_formula FirstOrder.Language.LHom.setOf_realize_onFormulaₓ'. -/
@[simp]
theorem LHom.setOf_realize_onFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Formula α) : (setOf (φ.onFormula ψ).realize : Set (α → M)) = setOf ψ.realize :=
  by
  ext
  simp
#align first_order.language.Lhom.set_of_realize_on_formula FirstOrder.Language.LHom.setOf_realize_onFormula

variable (M)

#print FirstOrder.Language.Sentence.Realize /-
/-- A sentence can be evaluated as true or false in a structure. -/
def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.realize (default : _ → M)
#align first_order.language.sentence.realize FirstOrder.Language.Sentence.Realize
-/

-- mathport name: sentence.realize
infixl:51
  " ⊨ " =>-- input using \|= or \vDash, but not using \models
  Sentence.Realize

#print FirstOrder.Language.Sentence.realize_not /-
@[simp]
theorem Sentence.realize_not {φ : L.Sentence} : M ⊨ φ.Not ↔ ¬M ⊨ φ :=
  Iff.rfl
#align first_order.language.sentence.realize_not FirstOrder.Language.Sentence.realize_not
-/

namespace Formula

#print FirstOrder.Language.Formula.realize_equivSentence_symm_con /-
@[simp]
theorem realize_equivSentence_symm_con [L[[α]].Structure M]
    [(L.lhomWithConstants α).IsExpansionOn M] (φ : L[[α]].Sentence) :
    ((equivSentence.symm φ).realize fun a => (L.con a : M)) ↔ φ.realize M :=
  by
  simp only [equiv_sentence, Equiv.symm_symm, Equiv.coe_trans, realize,
    bounded_formula.realize_relabel_equiv]
  refine' trans _ bounded_formula.realize_constants_vars_equiv
  congr with (i | i)
  · rfl
  · exact i.elim
#align first_order.language.formula.realize_equiv_sentence_symm_con FirstOrder.Language.Formula.realize_equivSentence_symm_con
-/

#print FirstOrder.Language.Formula.realize_equivSentence /-
@[simp]
theorem realize_equivSentence [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).realize M ↔ φ.realize fun a => (L.con a : M) := by
  rw [← realize_equiv_sentence_symm_con M (equiv_sentence φ), _root_.equiv.symm_apply_apply]
#align first_order.language.formula.realize_equiv_sentence FirstOrder.Language.Formula.realize_equivSentence
-/

#print FirstOrder.Language.Formula.realize_equivSentence_symm /-
theorem realize_equivSentence_symm (φ : L[[α]].Sentence) (v : α → M) :
    (equivSentence.symm φ).realize v ↔
      @Sentence.Realize _ M (@Language.withConstantsStructure L M _ α (constantsOn.structure v))
        φ :=
  letI := constants_on.Structure v
  realize_equiv_sentence_symm_con M φ
#align first_order.language.formula.realize_equiv_sentence_symm FirstOrder.Language.Formula.realize_equivSentence_symm
-/

end Formula

/- warning: first_order.language.Lhom.realize_on_sentence -> FirstOrder.Language.LHom.realize_onSentence is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u4, u5}} (M : Type.{u3}) [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_4 : FirstOrder.Language.Structure.{u4, u5, u3} L' M] (φ : FirstOrder.Language.LHom.{u1, u2, u4, u5} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u4, u5, u3} L L' φ M _inst_1 _inst_4] (ψ : FirstOrder.Language.Sentence.{u1, u2} L), Iff (FirstOrder.Language.Sentence.Realize.{u4, u5, u3} L' M _inst_4 (FirstOrder.Language.LHom.onSentence.{u1, u2, u4, u5} L L' φ ψ)) (FirstOrder.Language.Sentence.Realize.{u1, u2, u3} L M _inst_1 ψ)
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u2, u1}} (M : Type.{u5}) [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] [_inst_4 : FirstOrder.Language.Structure.{u2, u1, u5} L' M] (φ : FirstOrder.Language.LHom.{u3, u4, u2, u1} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u3, u4, u2, u1, u5} L L' φ M _inst_1 _inst_4] (ψ : FirstOrder.Language.Sentence.{u3, u4} L), Iff (FirstOrder.Language.Sentence.Realize.{u2, u1, u5} L' M _inst_4 (FirstOrder.Language.LHom.onSentence.{u3, u4, u2, u1} L L' φ ψ)) (FirstOrder.Language.Sentence.Realize.{u3, u4, u5} L M _inst_1 ψ)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.realize_on_sentence FirstOrder.Language.LHom.realize_onSentenceₓ'. -/
@[simp]
theorem LHom.realize_onSentence [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Sentence) : M ⊨ φ.onSentence ψ ↔ M ⊨ ψ :=
  φ.realize_onFormula ψ
#align first_order.language.Lhom.realize_on_sentence FirstOrder.Language.LHom.realize_onSentence

variable (L)

#print FirstOrder.Language.completeTheory /-
/-- The complete theory of a structure `M` is the set of all sentences `M` satisfies. -/
def completeTheory : L.Theory :=
  { φ | M ⊨ φ }
#align first_order.language.complete_theory FirstOrder.Language.completeTheory
-/

variable (N)

#print FirstOrder.Language.ElementarilyEquivalent /-
/-- Two structures are elementarily equivalent when they satisfy the same sentences. -/
def ElementarilyEquivalent : Prop :=
  L.completeTheory M = L.completeTheory N
#align first_order.language.elementarily_equivalent FirstOrder.Language.ElementarilyEquivalent
-/

-- mathport name: elementarily_equivalent
scoped[FirstOrder]
  notation:25 A " ≅[" L "] " B:50 => FirstOrder.Language.ElementarilyEquivalent L A B

variable {L} {M} {N}

#print FirstOrder.Language.mem_completeTheory /-
@[simp]
theorem mem_completeTheory {φ : Sentence L} : φ ∈ L.completeTheory M ↔ M ⊨ φ :=
  Iff.rfl
#align first_order.language.mem_complete_theory FirstOrder.Language.mem_completeTheory
-/

/- warning: first_order.language.elementarily_equivalent_iff -> FirstOrder.Language.elementarilyEquivalent_iff is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], Iff (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (forall (φ : FirstOrder.Language.Sentence.{u1, u2} L), Iff (FirstOrder.Language.Sentence.Realize.{u1, u2, u3} L M _inst_1 φ) (FirstOrder.Language.Sentence.Realize.{u1, u2, u4} L N _inst_2 φ))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N], Iff (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) (forall (φ : FirstOrder.Language.Sentence.{u2, u3} L), Iff (FirstOrder.Language.Sentence.Realize.{u2, u3, u4} L M _inst_1 φ) (FirstOrder.Language.Sentence.Realize.{u2, u3, u1} L N _inst_2 φ))
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent_iff FirstOrder.Language.elementarilyEquivalent_iffₓ'. -/
theorem elementarilyEquivalent_iff : M ≅[L] N ↔ ∀ φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ := by
  simp only [elementarily_equivalent, Set.ext_iff, complete_theory, Set.mem_setOf_eq]
#align first_order.language.elementarily_equivalent_iff FirstOrder.Language.elementarilyEquivalent_iff

variable (M)

#print FirstOrder.Language.Theory.Model /-
/-- A model of a theory is a structure in which every sentence is realized as true. -/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : ∀ φ ∈ T, M ⊨ φ
#align first_order.language.Theory.model FirstOrder.Language.Theory.Model
-/

-- mathport name: Theory.model
infixl:51
  " ⊨ " =>-- input using \|= or \vDash, but not using \models
  Theory.Model

variable {M} (T : L.Theory)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Theory.model_iff /-
@[simp]
theorem Theory.model_iff : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ :=
  ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩
#align first_order.language.Theory.model_iff FirstOrder.Language.Theory.model_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Theory.realize_sentence_of_mem /-
theorem Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ ∈ T) : M ⊨ φ :=
  Theory.Model.realize_of_mem φ h
#align first_order.language.Theory.realize_sentence_of_mem FirstOrder.Language.Theory.realize_sentence_of_mem
-/

/- warning: first_order.language.Lhom.on_Theory_model -> FirstOrder.Language.LHom.onTheory_model is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u4, u5}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_4 : FirstOrder.Language.Structure.{u4, u5, u3} L' M] (φ : FirstOrder.Language.LHom.{u1, u2, u4, u5} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u1, u2, u4, u5, u3} L L' φ M _inst_1 _inst_4] (T : FirstOrder.Language.Theory.{u1, u2} L), Iff (FirstOrder.Language.Theory.Model.{u4, u5, u3} L' M _inst_4 (FirstOrder.Language.LHom.onTheory.{u1, u2, u4, u5} L L' φ T)) (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T)
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {L' : FirstOrder.Language.{u2, u1}} {M : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] [_inst_4 : FirstOrder.Language.Structure.{u2, u1, u5} L' M] (φ : FirstOrder.Language.LHom.{u3, u4, u2, u1} L L') [_inst_5 : FirstOrder.Language.LHom.IsExpansionOn.{u3, u4, u2, u1, u5} L L' φ M _inst_1 _inst_4] (T : FirstOrder.Language.Theory.{u3, u4} L), Iff (FirstOrder.Language.Theory.Model.{u2, u1, u5} L' M _inst_4 (FirstOrder.Language.LHom.onTheory.{u3, u4, u2, u1} L L' φ T)) (FirstOrder.Language.Theory.Model.{u3, u4, u5} L M _inst_1 T)
Case conversion may be inaccurate. Consider using '#align first_order.language.Lhom.on_Theory_model FirstOrder.Language.LHom.onTheory_modelₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem LHom.onTheory_model [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (T : L.Theory) :
    M ⊨ φ.onTheory T ↔ M ⊨ T := by simp [Theory.model_iff, Lhom.on_Theory]
#align first_order.language.Lhom.on_Theory_model FirstOrder.Language.LHom.onTheory_model

variable {M} {T}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.model_empty /-
instance model_empty : M ⊨ (∅ : L.Theory) :=
  ⟨fun φ hφ => (Set.not_mem_empty φ hφ).elim⟩
#align first_order.language.model_empty FirstOrder.Language.model_empty
-/

namespace Theory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Theory.Model.mono /-
theorem Model.mono {T' : L.Theory} (h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T :=
  ⟨fun φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩
#align first_order.language.Theory.model.mono FirstOrder.Language.Theory.Model.mono
-/

/- warning: first_order.language.Theory.model.union -> FirstOrder.Language.Theory.Model.union is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {T : FirstOrder.Language.Theory.{u1, u2} L} {T' : FirstOrder.Language.Theory.{u1, u2} L}, (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T) -> (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T') -> (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 (Union.union.{max u1 u2} (FirstOrder.Language.Theory.{u1, u2} L) (Set.hasUnion.{max u1 u2} (FirstOrder.Language.Sentence.{u1, u2} L)) T T'))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {T : FirstOrder.Language.Theory.{u1, u2} L} {T' : FirstOrder.Language.Theory.{u1, u2} L}, (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T) -> (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T') -> (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 (Union.union.{max u2 u1} (FirstOrder.Language.Theory.{u1, u2} L) (Set.instUnionSet.{max u1 u2} (FirstOrder.Language.Sentence.{u1, u2} L)) T T'))
Case conversion may be inaccurate. Consider using '#align first_order.language.Theory.model.union FirstOrder.Language.Theory.Model.unionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Model.union {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T') : M ⊨ T ∪ T' :=
  by
  simp only [model_iff, Set.mem_union] at *
  exact fun φ hφ => hφ.elim (h _) (h' _)
#align first_order.language.Theory.model.union FirstOrder.Language.Theory.Model.union

/- warning: first_order.language.Theory.model_union_iff -> FirstOrder.Language.Theory.model_union_iff is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {T : FirstOrder.Language.Theory.{u1, u2} L} {T' : FirstOrder.Language.Theory.{u1, u2} L}, Iff (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 (Union.union.{max u1 u2} (FirstOrder.Language.Theory.{u1, u2} L) (Set.hasUnion.{max u1 u2} (FirstOrder.Language.Sentence.{u1, u2} L)) T T')) (And (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T) (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T'))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {T : FirstOrder.Language.Theory.{u1, u2} L} {T' : FirstOrder.Language.Theory.{u1, u2} L}, Iff (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 (Union.union.{max u2 u1} (FirstOrder.Language.Theory.{u1, u2} L) (Set.instUnionSet.{max u1 u2} (FirstOrder.Language.Sentence.{u1, u2} L)) T T')) (And (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T) (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T'))
Case conversion may be inaccurate. Consider using '#align first_order.language.Theory.model_union_iff FirstOrder.Language.Theory.model_union_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem model_union_iff {T' : L.Theory} : M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono (T.subset_union_left T'), h.mono (T.subset_union_right T')⟩, fun h =>
    h.1.union h.2⟩
#align first_order.language.Theory.model_union_iff FirstOrder.Language.Theory.model_union_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Theory.model_singleton_iff /-
theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by simp
#align first_order.language.Theory.model_singleton_iff FirstOrder.Language.Theory.model_singleton_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Theory.model_iff_subset_completeTheory /-
theorem model_iff_subset_completeTheory : M ⊨ T ↔ T ⊆ L.completeTheory M :=
  T.model_iff
#align first_order.language.Theory.model_iff_subset_complete_theory FirstOrder.Language.Theory.model_iff_subset_completeTheory
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Theory.CompleteTheory.subset /-
theorem CompleteTheory.subset [MT : M ⊨ T] : T ⊆ L.completeTheory M :=
  model_iff_subset_completeTheory.1 MT
#align first_order.language.Theory.complete_theory.subset FirstOrder.Language.Theory.CompleteTheory.subset
-/

end Theory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.model_completeTheory /-
instance model_completeTheory : M ⊨ L.completeTheory M :=
  Theory.model_iff_subset_completeTheory.2 (subset_refl _)
#align first_order.language.model_complete_theory FirstOrder.Language.model_completeTheory
-/

variable (M N)

/- warning: first_order.language.realize_iff_of_model_complete_theory -> FirstOrder.Language.realize_iff_of_model_completeTheory is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} (M : Type.{u3}) (N : Type.{u4}) [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] [_inst_4 : FirstOrder.Language.Theory.Model.{u1, u2, u4} L N _inst_2 (FirstOrder.Language.completeTheory.{u1, u2, u3} L M _inst_1)] (φ : FirstOrder.Language.Sentence.{u1, u2} L), Iff (FirstOrder.Language.Sentence.Realize.{u1, u2, u4} L N _inst_2 φ) (FirstOrder.Language.Sentence.Realize.{u1, u2, u3} L M _inst_1 φ)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} (M : Type.{u4}) (N : Type.{u1}) [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] [_inst_4 : FirstOrder.Language.Theory.Model.{u2, u3, u1} L N _inst_2 (FirstOrder.Language.completeTheory.{u2, u3, u4} L M _inst_1)] (φ : FirstOrder.Language.Sentence.{u2, u3} L), Iff (FirstOrder.Language.Sentence.Realize.{u2, u3, u1} L N _inst_2 φ) (FirstOrder.Language.Sentence.Realize.{u2, u3, u4} L M _inst_1 φ)
Case conversion may be inaccurate. Consider using '#align first_order.language.realize_iff_of_model_complete_theory FirstOrder.Language.realize_iff_of_model_completeTheoryₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem realize_iff_of_model_completeTheory [N ⊨ L.completeTheory M] (φ : L.Sentence) :
    N ⊨ φ ↔ M ⊨ φ :=
  by
  refine' ⟨fun h => _, (L.complete_theory M).realize_sentence_of_mem⟩
  contrapose! h
  rw [← sentence.realize_not] at *
  exact (L.complete_theory M).realize_sentence_of_mem (mem_complete_theory.2 h)
#align first_order.language.realize_iff_of_model_complete_theory FirstOrder.Language.realize_iff_of_model_completeTheory

variable {M N}

namespace BoundedFormula

#print FirstOrder.Language.BoundedFormula.realize_alls /-
@[simp]
theorem realize_alls {φ : L.BoundedFormula α n} {v : α → M} :
    φ.alls.realize v ↔ ∀ xs : Fin n → M, φ.realize v xs :=
  by
  induction' n with n ih
  · exact unique.forall_iff.symm
  · simp only [alls, ih, realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩
#align first_order.language.bounded_formula.realize_alls FirstOrder.Language.BoundedFormula.realize_alls
-/

#print FirstOrder.Language.BoundedFormula.realize_exs /-
@[simp]
theorem realize_exs {φ : L.BoundedFormula α n} {v : α → M} :
    φ.exs.realize v ↔ ∃ xs : Fin n → M, φ.realize v xs :=
  by
  induction' n with n ih
  · exact unique.exists_iff.symm
  · simp only [bounded_formula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      rw [← Fin.snoc_init_self xs] at h
      exact ⟨_, _, h⟩
#align first_order.language.bounded_formula.realize_exs FirstOrder.Language.BoundedFormula.realize_exs
-/

#print FirstOrder.Language.BoundedFormula.realize_toFormula /-
@[simp]
theorem realize_toFormula (φ : L.BoundedFormula α n) (v : Sum α (Fin n) → M) :
    φ.toFormula.realize v ↔ φ.realize (v ∘ Sum.inl) (v ∘ Sum.inr) :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3 a8 a9 a0
  · rfl
  · simp [bounded_formula.realize]
  · simp [bounded_formula.realize]
  ·
    rw [to_formula, formula.realize, realize_imp, ← formula.realize, ih1, ← formula.realize, ih2,
      realize_imp]
  · rw [to_formula, formula.realize, realize_all, realize_all]
    refine' forall_congr' fun a => _
    have h := ih3 (Sum.elim (v ∘ Sum.inl) (snoc (v ∘ Sum.inr) a))
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    rw [← h, realize_relabel, formula.realize]
    rcongr
    · cases x
      · simp
      · refine' Fin.lastCases _ (fun i => _) x
        · rw [Sum.elim_inr, snoc_last, Function.comp_apply, Sum.elim_inr, Function.comp_apply,
            finSumFinEquiv_symm_last, Sum.map_inr, Sum.elim_inr, Function.comp_apply]
          exact (congr rfl (Subsingleton.elim _ _)).trans (snoc_last _ _)
        · simp only [cast_succ, Function.comp_apply, Sum.elim_inr,
            finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, Sum.elim_inl]
          rw [← cast_succ, snoc_cast_succ]
    · exact Subsingleton.elim _ _
#align first_order.language.bounded_formula.realize_to_formula FirstOrder.Language.BoundedFormula.realize_toFormula
-/

end BoundedFormula

namespace Equiv

/- warning: first_order.language.equiv.realize_bounded_formula -> FirstOrder.Language.Equiv.realize_boundedFormula is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u5} L N] {α : Type.{u4}} {n : Nat} (g : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (φ : FirstOrder.Language.BoundedFormula.{u1, u2, u4} L α n) {v : α -> M} {xs : (Fin n) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u5, u4} L N _inst_2 α n φ (Function.comp.{succ u4, succ u3, succ u5} α M N (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g) v) (Function.comp.{1, succ u3, succ u5} (Fin n) M N (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g) xs)) (FirstOrder.Language.BoundedFormula.Realize.{u1, u2, u3, u4} L M _inst_1 α n φ v xs)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] {α : Type.{u5}} {n : Nat} (g : FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) (φ : FirstOrder.Language.BoundedFormula.{u2, u3, u5} L α n) {v : α -> M} {xs : (Fin n) -> M}, Iff (FirstOrder.Language.BoundedFormula.Realize.{u2, u3, u1, u5} L N _inst_2 α n φ (Function.comp.{succ u5, succ u4, succ u1} α M N (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2))) g) v) (Function.comp.{1, succ u4, succ u1} (Fin n) M N (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2))) g) xs)) (FirstOrder.Language.BoundedFormula.Realize.{u2, u3, u4, u5} L M _inst_1 α n φ v xs)
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.realize_bounded_formula FirstOrder.Language.Equiv.realize_boundedFormulaₓ'. -/
@[simp]
theorem realize_boundedFormula (g : M ≃[L] N) (φ : L.BoundedFormula α n) {v : α → M}
    {xs : Fin n → M} : φ.realize (g ∘ v) (g ∘ xs) ↔ φ.realize v xs :=
  by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp only [bounded_formula.realize, ← Sum.comp_elim, equiv.realize_term, g.injective.eq_iff]
  · simp only [bounded_formula.realize, ← Sum.comp_elim, equiv.realize_term, g.map_rel]
  · rw [bounded_formula.realize, ih1, ih2, bounded_formula.realize]
  · rw [bounded_formula.realize, bounded_formula.realize]
    constructor
    · intro h a
      have h' := h (g a)
      rw [← Fin.comp_snoc, ih3] at h'
      exact h'
    · intro h a
      have h' := h (g.symm a)
      rw [← ih3, Fin.comp_snoc, g.apply_symm_apply] at h'
      exact h'
#align first_order.language.equiv.realize_bounded_formula FirstOrder.Language.Equiv.realize_boundedFormula

/- warning: first_order.language.equiv.realize_formula -> FirstOrder.Language.Equiv.realize_formula is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u5} L N] {α : Type.{u4}} (g : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (φ : FirstOrder.Language.Formula.{u1, u2, u4} L α) {v : α -> M}, Iff (FirstOrder.Language.Formula.Realize.{u1, u2, u5, u4} L N _inst_2 α φ (Function.comp.{succ u4, succ u3, succ u5} α M N (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u3, u5} L M N _inst_1 _inst_2) g) v)) (FirstOrder.Language.Formula.Realize.{u1, u2, u3, u4} L M _inst_1 α φ v)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] {α : Type.{u5}} (g : FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) (φ : FirstOrder.Language.Formula.{u2, u3, u5} L α) {v : α -> M}, Iff (FirstOrder.Language.Formula.Realize.{u2, u3, u1, u5} L N _inst_2 α φ (Function.comp.{succ u5, succ u4, succ u1} α M N (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2))) g) v)) (FirstOrder.Language.Formula.Realize.{u2, u3, u4, u5} L M _inst_1 α φ v)
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.realize_formula FirstOrder.Language.Equiv.realize_formulaₓ'. -/
@[simp]
theorem realize_formula (g : M ≃[L] N) (φ : L.Formula α) {v : α → M} :
    φ.realize (g ∘ v) ↔ φ.realize v := by
  rw [formula.realize, formula.realize, ← g.realize_bounded_formula φ, iff_eq_eq,
    Unique.eq_default (g ∘ default)]
#align first_order.language.equiv.realize_formula FirstOrder.Language.Equiv.realize_formula

/- warning: first_order.language.equiv.realize_sentence -> FirstOrder.Language.Equiv.realize_sentence is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], (FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (forall (φ : FirstOrder.Language.Sentence.{u1, u2} L), Iff (FirstOrder.Language.Sentence.Realize.{u1, u2, u3} L M _inst_1 φ) (FirstOrder.Language.Sentence.Realize.{u1, u2, u4} L N _inst_2 φ))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N], (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (forall (φ : FirstOrder.Language.Sentence.{u2, u3} L), Iff (FirstOrder.Language.Sentence.Realize.{u2, u3, u4} L M _inst_1 φ) (FirstOrder.Language.Sentence.Realize.{u2, u3, u1} L N _inst_2 φ))
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.realize_sentence FirstOrder.Language.Equiv.realize_sentenceₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem realize_sentence (g : M ≃[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [sentence.realize, sentence.realize, ← g.realize_formula, Unique.eq_default (g ∘ default)]
#align first_order.language.equiv.realize_sentence FirstOrder.Language.Equiv.realize_sentence

/- warning: first_order.language.equiv.Theory_model -> FirstOrder.Language.Equiv.theory_model is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {T : FirstOrder.Language.Theory.{u1, u2} L}, (FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (forall [_inst_4 : FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T], FirstOrder.Language.Theory.Model.{u1, u2, u4} L N _inst_2 T)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] {T : FirstOrder.Language.Theory.{u2, u3} L}, (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (forall [_inst_4 : FirstOrder.Language.Theory.Model.{u2, u3, u4} L M _inst_1 T], FirstOrder.Language.Theory.Model.{u2, u3, u1} L N _inst_2 T)
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.Theory_model FirstOrder.Language.Equiv.theory_modelₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem theory_model (g : M ≃[L] N) [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (g.realize_sentence φ).1 (Theory.realize_sentence_of_mem T hφ)⟩
#align first_order.language.equiv.Theory_model FirstOrder.Language.Equiv.theory_model

/- warning: first_order.language.equiv.elementarily_equivalent -> FirstOrder.Language.Equiv.elementarilyEquivalent is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], (FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N], (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.elementarily_equivalent FirstOrder.Language.Equiv.elementarilyEquivalentₓ'. -/
theorem elementarilyEquivalent (g : M ≃[L] N) : M ≅[L] N :=
  elementarilyEquivalent_iff.2 g.realize_sentence
#align first_order.language.equiv.elementarily_equivalent FirstOrder.Language.Equiv.elementarilyEquivalent

end Equiv

namespace Relations

open BoundedFormula

variable {r : L.Relations 2}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Relations.realize_reflexive /-
@[simp]
theorem realize_reflexive : M ⊨ r.Reflexive ↔ Reflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => realize_rel₂
#align first_order.language.relations.realize_reflexive FirstOrder.Language.Relations.realize_reflexive
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Relations.realize_irreflexive /-
@[simp]
theorem realize_irreflexive : M ⊨ r.Irreflexive ↔ Irreflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => not_congr realize_rel₂
#align first_order.language.relations.realize_irreflexive FirstOrder.Language.Relations.realize_irreflexive
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Relations.realize_symmetric /-
@[simp]
theorem realize_symmetric : M ⊨ r.Symmetric ↔ Symmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr realize_rel₂ realize_rel₂
#align first_order.language.relations.realize_symmetric FirstOrder.Language.Relations.realize_symmetric
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Relations.realize_antisymmetric /-
@[simp]
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ AntiSymmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ Iff.rfl)
#align first_order.language.relations.realize_antisymmetric FirstOrder.Language.Relations.realize_antisymmetric
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Relations.realize_transitive /-
@[simp]
theorem realize_transitive : M ⊨ r.Transitive ↔ Transitive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ =>
      forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ realize_rel₂)
#align first_order.language.relations.realize_transitive FirstOrder.Language.Relations.realize_transitive
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.Relations.realize_total /-
@[simp]
theorem realize_total : M ⊨ r.Total ↔ Total fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => realize_sup.trans (or_congr realize_rel₂ realize_rel₂)
#align first_order.language.relations.realize_total FirstOrder.Language.Relations.realize_total
-/

end Relations

section Cardinality

variable (L)

/- warning: first_order.language.sentence.realize_card_ge -> FirstOrder.Language.Sentence.realize_cardGe is a dubious translation:
lean 3 declaration is
  forall (L : FirstOrder.Language.{u1, u2}) {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] (n : Nat), Iff (FirstOrder.Language.Sentence.Realize.{u1, u2, u3} L M _inst_1 (FirstOrder.Language.Sentence.cardGe.{u1, u2} L n)) (LE.le.{succ u3} Cardinal.{u3} Cardinal.hasLe.{u3} ((fun (a : Type) (b : Type.{succ u3}) [self : HasLiftT.{1, succ (succ u3)} a b] => self.0) Nat Cardinal.{u3} (HasLiftT.mk.{1, succ (succ u3)} Nat Cardinal.{u3} (CoeTCₓ.coe.{1, succ (succ u3)} Nat Cardinal.{u3} (Nat.castCoe.{succ u3} Cardinal.{u3} Cardinal.hasNatCast.{u3}))) n) (Cardinal.mk.{u3} M))
but is expected to have type
  forall (L : FirstOrder.Language.{u1, u2}) {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] (n : Nat), Iff (FirstOrder.Language.Sentence.Realize.{u1, u2, u3} L M _inst_1 (FirstOrder.Language.Sentence.cardGe.{u1, u2} L n)) (LE.le.{succ u3} Cardinal.{u3} Cardinal.instLECardinal.{u3} (Nat.cast.{succ u3} Cardinal.{u3} Cardinal.instNatCastCardinal.{u3} n) (Cardinal.mk.{u3} M))
Case conversion may be inaccurate. Consider using '#align first_order.language.sentence.realize_card_ge FirstOrder.Language.Sentence.realize_cardGeₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Sentence.realize_cardGe (n) : M ⊨ Sentence.cardGe L n ↔ ↑n ≤ (#M) :=
  by
  rw [← lift_mk_fin, ← lift_le, lift_lift, lift_mk_le, sentence.card_ge, sentence.realize,
    bounded_formula.realize_exs]
  simp_rw [bounded_formula.realize_foldr_inf]
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne.def, List.mem_product,
    List.mem_finRange, forall_exists_index, and_imp, List.mem_filter, true_and_iff]
  refine' ⟨_, fun xs => ⟨xs.some, _⟩⟩
  · rintro ⟨xs, h⟩
    refine' ⟨⟨xs, fun i j ij => _⟩⟩
    contrapose! ij
    have hij := h _ i j ij rfl
    simp only [bounded_formula.realize_not, term.realize, bounded_formula.realize_bd_equal,
      Sum.elim_inr] at hij
    exact hij
  · rintro _ i j ij rfl
    simp [ij]
#align first_order.language.sentence.realize_card_ge FirstOrder.Language.Sentence.realize_cardGe

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.model_infiniteTheory_iff /-
@[simp]
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M := by
  simp [infinite_theory, infinite_iff, aleph_0_le]
#align first_order.language.model_infinite_theory_iff FirstOrder.Language.model_infiniteTheory_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.model_infiniteTheory /-
instance model_infiniteTheory [h : Infinite M] : M ⊨ L.infiniteTheory :=
  L.model_infiniteTheory_iff.2 h
#align first_order.language.model_infinite_theory FirstOrder.Language.model_infiniteTheory
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.model_nonemptyTheory_iff /-
@[simp]
theorem model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory ↔ Nonempty M := by
  simp only [nonempty_theory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    sentence.realize_card_ge, Nat.cast_one, one_le_iff_ne_zero, mk_ne_zero_iff]
#align first_order.language.model_nonempty_theory_iff FirstOrder.Language.model_nonemptyTheory_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.model_nonempty /-
instance model_nonempty [h : Nonempty M] : M ⊨ L.nonemptyTheory :=
  L.model_nonemptyTheory_iff.2 h
#align first_order.language.model_nonempty FirstOrder.Language.model_nonempty
-/

/- warning: first_order.language.model_distinct_constants_theory -> FirstOrder.Language.model_distinctConstantsTheory is a dubious translation:
lean 3 declaration is
  forall (L : FirstOrder.Language.{u1, u2}) {α : Type.{u4}} {M : Type.{u3}} [_inst_4 : FirstOrder.Language.Structure.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M] (s : Set.{u4} α), Iff (FirstOrder.Language.Theory.Model.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 (FirstOrder.Language.distinctConstantsTheory.{u1, u2, u4} L α s)) (Set.InjOn.{u4, u3} α M (fun (i : α) => (fun (a : Type.{max u1 u4}) (b : Type.{u3}) [self : HasLiftT.{succ (max u1 u4), succ u3} a b] => self.0) (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (HasLiftT.mk.{succ (max u1 u4), succ u3} (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (CoeTCₓ.coe.{succ (max u1 u4), succ u3} (FirstOrder.Language.Constants.{max u1 u4, u2} (FirstOrder.Language.withConstants.{u1, u2, u4} L α)) M (FirstOrder.Language.hasCoeT.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4))) (FirstOrder.Language.con.{u1, u2, u4} L α i)) s)
but is expected to have type
  forall (L : FirstOrder.Language.{u1, u2}) {α : Type.{u4}} {M : Type.{u3}} [_inst_4 : FirstOrder.Language.Structure.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M] (s : Set.{u4} α), Iff (FirstOrder.Language.Theory.Model.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 (FirstOrder.Language.distinctConstantsTheory.{u1, u2, u4} L α s)) (Set.InjOn.{u4, u3} α M (fun (i : α) => FirstOrder.Language.constantMap.{max u1 u4, u2, u3} (FirstOrder.Language.withConstants.{u1, u2, u4} L α) M _inst_4 (FirstOrder.Language.con.{u1, u2, u4} L α i)) s)
Case conversion may be inaccurate. Consider using '#align first_order.language.model_distinct_constants_theory FirstOrder.Language.model_distinctConstantsTheoryₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem model_distinctConstantsTheory {M : Type w} [L[[α]].Structure M] (s : Set α) :
    M ⊨ L.distinctConstantsTheory s ↔ Set.InjOn (fun i : α => (L.con i : M)) s :=
  by
  simp only [distinct_constants_theory, Theory.model_iff, Set.mem_image, Set.mem_inter,
    Set.mem_prod, Set.mem_compl, Prod.exists, forall_exists_index, and_imp]
  refine' ⟨fun h a as b bs ab => _, _⟩
  · contrapose! ab
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [sentence.realize, formula.realize_not, formula.realize_equal,
      term.realize_constants] at h'
    exact h'
  · rintro h φ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [sentence.realize, formula.realize_not, formula.realize_equal, term.realize_constants]
    exact fun contra => ab (h as bs contra)
#align first_order.language.model_distinct_constants_theory FirstOrder.Language.model_distinctConstantsTheory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.card_le_of_model_distinctConstantsTheory /-
theorem card_le_of_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].Structure M]
    [h : M ⊨ L.distinctConstantsTheory s] : Cardinal.lift.{w} (#s) ≤ Cardinal.lift.{u'} (#M) :=
  lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩
#align first_order.language.card_le_of_model_distinct_constants_theory FirstOrder.Language.card_le_of_model_distinctConstantsTheory
-/

end Cardinality

namespace ElementarilyEquivalent

/- warning: first_order.language.elementarily_equivalent.symm -> FirstOrder.Language.ElementarilyEquivalent.symm is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u4, u3} L N M _inst_2 _inst_1)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N], (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u1, u4} L N M _inst_2 _inst_1)
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.symm FirstOrder.Language.ElementarilyEquivalent.symmₓ'. -/
@[symm]
theorem symm (h : M ≅[L] N) : N ≅[L] M :=
  h.symm
#align first_order.language.elementarily_equivalent.symm FirstOrder.Language.ElementarilyEquivalent.symm

/- warning: first_order.language.elementarily_equivalent.trans -> FirstOrder.Language.ElementarilyEquivalent.trans is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} {P : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] [_inst_3 : FirstOrder.Language.Structure.{u1, u2, u5} L P], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u4, u5} L N P _inst_2 _inst_3) -> (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u5} L M P _inst_1 _inst_3)
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {M : Type.{u5}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] [_inst_2 : FirstOrder.Language.Structure.{u3, u4, u2} L N] [_inst_3 : FirstOrder.Language.Structure.{u3, u4, u1} L P], (FirstOrder.Language.ElementarilyEquivalent.{u3, u4, u5, u2} L M N _inst_1 _inst_2) -> (FirstOrder.Language.ElementarilyEquivalent.{u3, u4, u2, u1} L N P _inst_2 _inst_3) -> (FirstOrder.Language.ElementarilyEquivalent.{u3, u4, u5, u1} L M P _inst_1 _inst_3)
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.trans FirstOrder.Language.ElementarilyEquivalent.transₓ'. -/
@[trans]
theorem trans (MN : M ≅[L] N) (NP : N ≅[L] P) : M ≅[L] P :=
  MN.trans NP
#align first_order.language.elementarily_equivalent.trans FirstOrder.Language.ElementarilyEquivalent.trans

/- warning: first_order.language.elementarily_equivalent.complete_theory_eq -> FirstOrder.Language.ElementarilyEquivalent.completeTheory_eq is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (Eq.{succ (max u1 u2)} (FirstOrder.Language.Theory.{u1, u2} L) (FirstOrder.Language.completeTheory.{u1, u2, u3} L M _inst_1) (FirstOrder.Language.completeTheory.{u1, u2, u4} L N _inst_2))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N], (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (Eq.{max (succ u2) (succ u3)} (FirstOrder.Language.Theory.{u2, u3} L) (FirstOrder.Language.completeTheory.{u2, u3, u4} L M _inst_1) (FirstOrder.Language.completeTheory.{u2, u3, u1} L N _inst_2))
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.complete_theory_eq FirstOrder.Language.ElementarilyEquivalent.completeTheory_eqₓ'. -/
theorem completeTheory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N :=
  h
#align first_order.language.elementarily_equivalent.complete_theory_eq FirstOrder.Language.ElementarilyEquivalent.completeTheory_eq

/- warning: first_order.language.elementarily_equivalent.realize_sentence -> FirstOrder.Language.ElementarilyEquivalent.realize_sentence is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (forall (φ : FirstOrder.Language.Sentence.{u1, u2} L), Iff (FirstOrder.Language.Sentence.Realize.{u1, u2, u3} L M _inst_1 φ) (FirstOrder.Language.Sentence.Realize.{u1, u2, u4} L N _inst_2 φ))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N], (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (forall (φ : FirstOrder.Language.Sentence.{u2, u3} L), Iff (FirstOrder.Language.Sentence.Realize.{u2, u3, u4} L M _inst_1 φ) (FirstOrder.Language.Sentence.Realize.{u2, u3, u1} L N _inst_2 φ))
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.realize_sentence FirstOrder.Language.ElementarilyEquivalent.realize_sentenceₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem realize_sentence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (elementarilyEquivalent_iff.1 h) φ
#align first_order.language.elementarily_equivalent.realize_sentence FirstOrder.Language.ElementarilyEquivalent.realize_sentence

/- warning: first_order.language.elementarily_equivalent.Theory_model_iff -> FirstOrder.Language.ElementarilyEquivalent.theory_model_iff is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {T : FirstOrder.Language.Theory.{u1, u2} L}, (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (Iff (FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T) (FirstOrder.Language.Theory.Model.{u1, u2, u4} L N _inst_2 T))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] {T : FirstOrder.Language.Theory.{u2, u3} L}, (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (Iff (FirstOrder.Language.Theory.Model.{u2, u3, u4} L M _inst_1 T) (FirstOrder.Language.Theory.Model.{u2, u3, u1} L N _inst_2 T))
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.Theory_model_iff FirstOrder.Language.ElementarilyEquivalent.theory_model_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem theory_model_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T := by
  rw [Theory.model_iff_subset_complete_theory, Theory.model_iff_subset_complete_theory,
    h.complete_theory_eq]
#align first_order.language.elementarily_equivalent.Theory_model_iff FirstOrder.Language.ElementarilyEquivalent.theory_model_iff

/- warning: first_order.language.elementarily_equivalent.Theory_model -> FirstOrder.Language.ElementarilyEquivalent.theory_model is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {T : FirstOrder.Language.Theory.{u1, u2} L} [MT : FirstOrder.Language.Theory.Model.{u1, u2, u3} L M _inst_1 T], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (FirstOrder.Language.Theory.Model.{u1, u2, u4} L N _inst_2 T)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] {T : FirstOrder.Language.Theory.{u2, u3} L} [MT : FirstOrder.Language.Theory.Model.{u2, u3, u4} L M _inst_1 T], (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (FirstOrder.Language.Theory.Model.{u2, u3, u1} L N _inst_2 T)
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.Theory_model FirstOrder.Language.ElementarilyEquivalent.theory_modelₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem theory_model [MT : M ⊨ T] (h : M ≅[L] N) : N ⊨ T :=
  h.theory_model_iff.1 MT
#align first_order.language.elementarily_equivalent.Theory_model FirstOrder.Language.ElementarilyEquivalent.theory_model

/- warning: first_order.language.elementarily_equivalent.nonempty_iff -> FirstOrder.Language.ElementarilyEquivalent.nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (Iff (Nonempty.{succ u3} M) (Nonempty.{succ u4} N))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N], (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (Iff (Nonempty.{succ u4} M) (Nonempty.{succ u1} N))
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.nonempty_iff FirstOrder.Language.ElementarilyEquivalent.nonempty_iffₓ'. -/
theorem nonempty_iff (h : M ≅[L] N) : Nonempty M ↔ Nonempty N :=
  (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))
#align first_order.language.elementarily_equivalent.nonempty_iff FirstOrder.Language.ElementarilyEquivalent.nonempty_iff

/- warning: first_order.language.elementarily_equivalent.nonempty -> FirstOrder.Language.ElementarilyEquivalent.nonempty is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] [Mn : Nonempty.{succ u3} M], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (Nonempty.{succ u4} N)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] [Mn : Nonempty.{succ u4} M], (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (Nonempty.{succ u1} N)
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.nonempty FirstOrder.Language.ElementarilyEquivalent.nonemptyₓ'. -/
theorem nonempty [Mn : Nonempty M] (h : M ≅[L] N) : Nonempty N :=
  h.nonempty_iff.1 Mn
#align first_order.language.elementarily_equivalent.nonempty FirstOrder.Language.ElementarilyEquivalent.nonempty

/- warning: first_order.language.elementarily_equivalent.infinite_iff -> FirstOrder.Language.ElementarilyEquivalent.infinite_iff is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (Iff (Infinite.{succ u3} M) (Infinite.{succ u4} N))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N], (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (Iff (Infinite.{succ u4} M) (Infinite.{succ u1} N))
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.infinite_iff FirstOrder.Language.ElementarilyEquivalent.infinite_iffₓ'. -/
theorem infinite_iff (h : M ≅[L] N) : Infinite M ↔ Infinite N :=
  (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))
#align first_order.language.elementarily_equivalent.infinite_iff FirstOrder.Language.ElementarilyEquivalent.infinite_iff

/- warning: first_order.language.elementarily_equivalent.infinite -> FirstOrder.Language.ElementarilyEquivalent.infinite is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] [Mi : Infinite.{succ u3} M], (FirstOrder.Language.ElementarilyEquivalent.{u1, u2, u3, u4} L M N _inst_1 _inst_2) -> (Infinite.{succ u4} N)
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u1}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u1} L N] [Mi : Infinite.{succ u4} M], (FirstOrder.Language.ElementarilyEquivalent.{u2, u3, u4, u1} L M N _inst_1 _inst_2) -> (Infinite.{succ u1} N)
Case conversion may be inaccurate. Consider using '#align first_order.language.elementarily_equivalent.infinite FirstOrder.Language.ElementarilyEquivalent.infiniteₓ'. -/
theorem infinite [Mi : Infinite M] (h : M ≅[L] N) : Infinite N :=
  h.infinite_iff.1 Mi
#align first_order.language.elementarily_equivalent.infinite FirstOrder.Language.ElementarilyEquivalent.infinite

end ElementarilyEquivalent

end Language

end FirstOrder

