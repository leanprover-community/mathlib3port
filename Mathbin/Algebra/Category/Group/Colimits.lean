/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Group.colimits
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.Preadditive
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The category of additive commutative groups has all colimits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file uses a "pre-automated" approach, just as for `Mon/colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `add_comm_group` and `monoid_hom`.

TODO:
In fact, in `AddCommGroup` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well (or instead).
-/


universe u v

open CategoryTheory

open CategoryTheory.Limits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
namespace AddCommGroupCat.Colimits

/-!
We build the colimit of a diagram in `AddCommGroup` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ AddCommGroupCat.{v})

#print AddCommGroupCat.Colimits.Prequotient /-
/-- An inductive type representing all group expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient-- There's always `of`

  | of : ∀ (j : J) (x : F.obj j), prequotient-- Then one generator for each operation

  | zero : prequotient
  | neg : prequotient → prequotient
  | add : prequotient → prequotient → prequotient
#align AddCommGroup.colimits.prequotient AddCommGroupCat.Colimits.Prequotient
-/

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

#print AddCommGroupCat.Colimits.Relation /-
/-- The relation on `prequotient` saying when two expressions are equal
because of the abelian group laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop-- Make it an equivalence relation:

  | refl : ∀ x, relation x x
  | symm : ∀ (x y) (h : relation x y), relation y x
  |
  trans :
    ∀ (x y z) (h : relation x y) (k : relation y z), relation x z-- There's always a `map` relation

  |
  map :
    ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      relation (of j' (F.map f x))
        (of j x)-- Then one relation per operation, describing the interaction with `of`

  | zero : ∀ j, relation (of j 0) zero
  | neg : ∀ (j) (x : F.obj j), relation (of j (-x)) (neg (of j x))
  |
  add :
    ∀ (j) (x y : F.obj j),
      relation (of j (x + y))
        (add (of j x) (of j y))-- Then one relation per argument of each operation

  | neg_1 : ∀ (x x') (r : relation x x'), relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (r : relation x x'), relation (add x y) (add x' y)
  |
  add_2 : ∀ (x y y') (r : relation y y'), relation (add x y) (add x y')-- And one relation per axiom

  | zero_add : ∀ x, relation (add zero x) x
  | add_zero : ∀ x, relation (add x zero) x
  | add_left_neg : ∀ x, relation (add (neg x) x) zero
  | add_comm : ∀ x y, relation (add x y) (add y x)
  | add_assoc : ∀ x y z, relation (add (add x y) z) (add x (add y z))
#align AddCommGroup.colimits.relation AddCommGroupCat.Colimits.Relation
-/

#print AddCommGroupCat.Colimits.colimitSetoid /-
/--
The setoid corresponding to group expressions modulo abelian group relations and identifications.
-/
def colimitSetoid : Setoid (Prequotient F)
    where
  R := Relation F
  iseqv := ⟨Relation.refl, Relation.symm, Relation.trans⟩
#align AddCommGroup.colimits.colimit_setoid AddCommGroupCat.Colimits.colimitSetoid
-/

attribute [instance] colimit_setoid

#print AddCommGroupCat.Colimits.ColimitType /-
/-- The underlying type of the colimit of a diagram in `AddCommGroup`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)deriving Inhabited
#align AddCommGroup.colimits.colimit_type AddCommGroupCat.Colimits.ColimitType
-/

instance : AddCommGroup (ColimitType F)
    where
  zero := Quot.mk _ zero
  neg := by
    fapply @Quot.lift
    · intro x
      exact Quot.mk _ (neg x)
    · intro x x' r
      apply Quot.sound
      exact relation.neg_1 _ _ r
  add := by
    fapply @Quot.lift _ _ (colimit_type F → colimit_type F)
    · intro x
      fapply @Quot.lift
      · intro y
        exact Quot.mk _ (add x y)
      · intro y y' r
        apply Quot.sound
        exact relation.add_2 _ _ _ r
    · intro x x' r
      funext y
      induction y
      dsimp
      apply Quot.sound
      · exact relation.add_1 _ _ _ r
      · rfl
  zero_add x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.zero_add
    rfl
  add_zero x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.add_zero
    rfl
  add_left_neg x := by
    induction x
    dsimp
    apply Quot.sound
    apply relation.add_left_neg
    rfl
  add_comm x y := by
    induction x
    induction y
    dsimp
    apply Quot.sound
    apply relation.add_comm
    rfl
    rfl
  add_assoc x y z := by
    induction x
    induction y
    induction z
    dsimp
    apply Quot.sound
    apply relation.add_assoc
    rfl
    rfl
    rfl

/- warning: AddCommGroup.colimits.quot_zero -> AddCommGroupCat.Colimits.quot_zero is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}), Eq.{succ u1} (Quot.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) (AddCommGroupCat.Colimits.Prequotient.zero.{u1} J _inst_1 F)) (OfNat.ofNat.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) 0 (OfNat.mk.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) 0 (Zero.zero.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddZeroClass.toHasZero.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddMonoid.toAddZeroClass.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubNegMonoid.toAddMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddGroup.toSubNegMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroup.toAddGroup.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.ColimitType.addCommGroup.{u1} J _inst_1 F)))))))))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}), Eq.{succ u1} (Quot.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) (AddCommGroupCat.Colimits.Prequotient.zero.{u1} J _inst_1 F)) (OfNat.ofNat.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) 0 (Zero.toOfNat0.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (NegZeroClass.toZero.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubNegZeroMonoid.toNegZeroClass.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubtractionMonoid.toSubNegZeroMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubtractionCommMonoid.toSubtractionMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroup.toDivisionAddCommMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.instAddCommGroupColimitType.{u1} J _inst_1 F))))))))
Case conversion may be inaccurate. Consider using '#align AddCommGroup.colimits.quot_zero AddCommGroupCat.Colimits.quot_zeroₓ'. -/
@[simp]
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl
#align AddCommGroup.colimits.quot_zero AddCommGroupCat.Colimits.quot_zero

/- warning: AddCommGroup.colimits.quot_neg -> AddCommGroupCat.Colimits.quot_neg is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (x : AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F), Eq.{succ u1} (Quot.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) (AddCommGroupCat.Colimits.Prequotient.neg.{u1} J _inst_1 F x)) (Neg.neg.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubNegMonoid.toHasNeg.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddGroup.toSubNegMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroup.toAddGroup.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.ColimitType.addCommGroup.{u1} J _inst_1 F)))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) x))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (x : AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F), Eq.{succ u1} (Quot.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) (AddCommGroupCat.Colimits.Prequotient.neg.{u1} J _inst_1 F x)) (Neg.neg.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (NegZeroClass.toNeg.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubNegZeroMonoid.toNegZeroClass.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubtractionMonoid.toSubNegZeroMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubtractionCommMonoid.toSubtractionMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroup.toDivisionAddCommMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.instAddCommGroupColimitType.{u1} J _inst_1 F)))))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) x))
Case conversion may be inaccurate. Consider using '#align AddCommGroup.colimits.quot_neg AddCommGroupCat.Colimits.quot_negₓ'. -/
@[simp]
theorem quot_neg (x) : Quot.mk Setoid.r (neg x) = (-Quot.mk Setoid.r x : ColimitType F) :=
  rfl
#align AddCommGroup.colimits.quot_neg AddCommGroupCat.Colimits.quot_neg

/- warning: AddCommGroup.colimits.quot_add -> AddCommGroupCat.Colimits.quot_add is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (x : AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (y : AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F), Eq.{succ u1} (Quot.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) (AddCommGroupCat.Colimits.Prequotient.add.{u1} J _inst_1 F x y)) (HAdd.hAdd.{u1, u1, u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (instHAdd.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddZeroClass.toHasAdd.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddMonoid.toAddZeroClass.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubNegMonoid.toAddMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddGroup.toSubNegMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroup.toAddGroup.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.ColimitType.addCommGroup.{u1} J _inst_1 F))))))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) x) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) y))
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (x : AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (y : AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F), Eq.{succ u1} (Quot.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) (AddCommGroupCat.Colimits.Prequotient.add.{u1} J _inst_1 F x y)) (Add.add.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddZeroClass.toAdd.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddMonoid.toAddZeroClass.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (SubNegMonoid.toAddMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddGroup.toSubNegMonoid.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroup.toAddGroup.{u1} (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.instAddCommGroupColimitType.{u1} J _inst_1 F)))))) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) x) (Quot.mk.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (Setoid.r.{succ u1} (AddCommGroupCat.Colimits.Prequotient.{u1} J _inst_1 F) (AddCommGroupCat.Colimits.colimitSetoid.{u1} J _inst_1 F)) y))
Case conversion may be inaccurate. Consider using '#align AddCommGroup.colimits.quot_add AddCommGroupCat.Colimits.quot_addₓ'. -/
@[simp]
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) = (Quot.mk Setoid.r x + Quot.mk Setoid.r y : ColimitType F) :=
  rfl
#align AddCommGroup.colimits.quot_add AddCommGroupCat.Colimits.quot_add

#print AddCommGroupCat.Colimits.colimit /-
/-- The bundled abelian group giving the colimit of a diagram. -/
def colimit : AddCommGroupCat :=
  AddCommGroupCat.of (ColimitType F)
#align AddCommGroup.colimits.colimit AddCommGroupCat.Colimits.colimit
-/

/- warning: AddCommGroup.colimits.cocone_fun -> AddCommGroupCat.Colimits.coconeFun is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (j : J), (coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} F j)) -> (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (j : J), (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} F) j)) -> (AddCommGroupCat.Colimits.ColimitType.{u1} J _inst_1 F)
Case conversion may be inaccurate. Consider using '#align AddCommGroup.colimits.cocone_fun AddCommGroupCat.Colimits.coconeFunₓ'. -/
/-- The function from a given abelian group in the diagram to the colimit abelian group. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (of j x)
#align AddCommGroup.colimits.cocone_fun AddCommGroupCat.Colimits.coconeFun

/- warning: AddCommGroup.colimits.cocone_morphism -> AddCommGroupCat.Colimits.coconeMorphism is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (j : J), Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1})) (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} F j) (AddCommGroupCat.Colimits.colimit.{u1} J _inst_1 F)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (j : J), Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} F) j) (AddCommGroupCat.Colimits.colimit.{u1} J _inst_1 F)
Case conversion may be inaccurate. Consider using '#align AddCommGroup.colimits.cocone_morphism AddCommGroupCat.Colimits.coconeMorphismₓ'. -/
/-- The group homomorphism from a given abelian group in the diagram to the colimit abelian
group. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F
    where
  toFun := coconeFun F j
  map_zero' := by apply Quot.sound <;> apply relation.zero
  map_add' := by intros <;> apply Quot.sound <;> apply relation.add
#align AddCommGroup.colimits.cocone_morphism AddCommGroupCat.Colimits.coconeMorphism

/- warning: AddCommGroup.colimits.cocone_naturality -> AddCommGroupCat.Colimits.cocone_naturality is a dubious translation:
lean 3 declaration is
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) {j : J} {j' : J} (f : Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) j j'), Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1})) (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} F j) (AddCommGroupCat.Colimits.colimit.{u1} J _inst_1 F)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1}) (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} F j) (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} F j') (AddCommGroupCat.Colimits.colimit.{u1} J _inst_1 F) (CategoryTheory.Functor.map.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} F j j' f) (AddCommGroupCat.Colimits.coconeMorphism.{u1} J _inst_1 F j')) (AddCommGroupCat.Colimits.coconeMorphism.{u1} J _inst_1 F j)
but is expected to have type
  forall {J : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} J] (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) {j : J} {j' : J} (f : Quiver.Hom.{succ u1, u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) j j'), Eq.{succ u1} (Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} F) j) (AddCommGroupCat.Colimits.colimit.{u1} J _inst_1 F)) (CategoryTheory.CategoryStruct.comp.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1}) (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} F) j) (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} F) j') (AddCommGroupCat.Colimits.colimit.{u1} J _inst_1 F) (Prefunctor.map.{succ u1, succ u1, u1, succ u1} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_1)) AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} J _inst_1 AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} F) j j' f) (AddCommGroupCat.Colimits.coconeMorphism.{u1} J _inst_1 F j')) (AddCommGroupCat.Colimits.coconeMorphism.{u1} J _inst_1 F j)
Case conversion may be inaccurate. Consider using '#align AddCommGroup.colimits.cocone_naturality AddCommGroupCat.Colimits.cocone_naturalityₓ'. -/
@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j :=
  by
  ext
  apply Quot.sound
  apply Relation.Map
#align AddCommGroup.colimits.cocone_naturality AddCommGroupCat.Colimits.cocone_naturality

/- warning: AddCommGroup.colimits.cocone_naturality_components -> AddCommGroupCat.Colimits.cocone_naturality_components is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align AddCommGroup.colimits.cocone_naturality_components AddCommGroupCat.Colimits.cocone_naturality_componentsₓ'. -/
@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by rw [← cocone_naturality F f];
  rfl
#align AddCommGroup.colimits.cocone_naturality_components AddCommGroupCat.Colimits.cocone_naturality_components

#print AddCommGroupCat.Colimits.colimitCocone /-
/-- The cocone over the proposed colimit abelian group. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }
#align AddCommGroup.colimits.colimit_cocone AddCommGroupCat.Colimits.colimitCocone
-/

#print AddCommGroupCat.Colimits.descFunLift /-
/-- The function from the free abelian group on the diagram to the cone point of any other
cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | of j x => (s.ι.app j) x
  | zero => 0
  | neg x => -desc_fun_lift x
  | add x y => desc_fun_lift x + desc_fun_lift y
#align AddCommGroup.colimits.desc_fun_lift AddCommGroupCat.Colimits.descFunLift
-/

#print AddCommGroupCat.Colimits.descFun /-
/-- The function from the colimit abelian group to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt :=
  by
  fapply Quot.lift
  · exact desc_fun_lift F s
  · intro x y r
    induction r <;> try dsimp
    -- refl
    · rfl
    -- symm
    · exact r_ih.symm
    -- trans
    · exact Eq.trans r_ih_h r_ih_k
    -- map
    · simp
    -- zero
    · simp
    -- neg
    · simp
    -- add
    · simp
    -- neg_1
    · rw [r_ih]
    -- add_1
    · rw [r_ih]
    -- add_2
    · rw [r_ih]
    -- zero_add
    · rw [zero_add]
    -- add_zero
    · rw [add_zero]
    -- add_left_neg
    · rw [add_left_neg]
    -- add_comm
    · rw [add_comm]
    -- add_assoc
    · rw [add_assoc]
#align AddCommGroup.colimits.desc_fun AddCommGroupCat.Colimits.descFun
-/

#print AddCommGroupCat.Colimits.descMorphism /-
/-- The group homomorphism from the colimit abelian group to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt
    where
  toFun := descFun F s
  map_zero' := rfl
  map_add' x y := by induction x <;> induction y <;> rfl
#align AddCommGroup.colimits.desc_morphism AddCommGroupCat.Colimits.descMorphism
-/

#print AddCommGroupCat.Colimits.colimitCoconeIsColimit /-
/-- Evidence that the proposed colimit is the colimit. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone F)
    where
  desc s := descMorphism F s
  uniq s m w := by
    ext
    induction x
    induction x
    · have w' :=
        congr_fun (congr_arg (fun f : F.obj x_j ⟶ s.X => (f : F.obj x_j → s.X)) (w x_j)) x_x
      erw [w']
      rfl
    · simp [*]
    · simp [*]
    · simp [*]
    rfl
#align AddCommGroup.colimits.colimit_cocone_is_colimit AddCommGroupCat.Colimits.colimitCoconeIsColimit
-/

#print AddCommGroupCat.Colimits.hasColimits_addCommGroupCat /-
instance hasColimits_addCommGroupCat : HasColimits AddCommGroupCat
    where HasColimitsOfShape J 𝒥 :=
    {
      HasColimit := fun F =>
        has_colimit.mk
          { Cocone := colimit_cocone F
            IsColimit := colimit_cocone_is_colimit F } }
#align AddCommGroup.colimits.has_colimits_AddCommGroup AddCommGroupCat.Colimits.hasColimits_addCommGroupCat
-/

end AddCommGroupCat.Colimits

namespace AddCommGroupCat

open quotientAddGroup

/- warning: AddCommGroup.cokernel_iso_quotient -> AddCommGroupCat.cokernelIsoQuotient is a dubious translation:
lean 3 declaration is
  forall {G : AddCommGroupCat.{u1}} {H : AddCommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1})) G H), CategoryTheory.Iso.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Limits.cokernel.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.CategoryTheory.preadditive.{u1}) G H f (AddCommGroupCat.cokernelIsoQuotient._proof_1.{u1} G H f)) (AddCommGroupCat.of.{u1} (HasQuotient.Quotient.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} H) (AddSubgroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) H) (AddCommGroup.toAddGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) H) (AddCommGroupCat.addCommGroupInstance.{u1} H))) (quotientAddGroup.Subgroup.hasQuotient.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) H) (AddCommGroup.toAddGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) H) (AddCommGroupCat.addCommGroupInstance.{u1} H))) (AddMonoidHom.range.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) G) (AddCommGroup.toAddGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) G) (AddCommGroupCat.addCommGroupInstance.{u1} G)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) H) (AddCommGroup.toAddGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) H) (AddCommGroupCat.addCommGroupInstance.{u1} H)) f)) (QuotientAddGroup.Quotient.addCommGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} AddCommGroupCat.{u1} Type.{u1} AddCommGroupCat.hasCoeToSort.{u1} H) (AddCommGroupCat.addCommGroupInstance.{u1} H) (AddMonoidHom.range.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) G) (AddCommGroup.toAddGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) G) (AddCommGroupCat.addCommGroupInstance.{u1} G)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) H) (AddCommGroup.toAddGroup.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} AddCommGroup.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} AddCommGroup.{u1}) H) (AddCommGroupCat.addCommGroupInstance.{u1} H)) f)))
but is expected to have type
  forall {G : AddCommGroupCat.{u1}} {H : AddCommGroupCat.{u1}} (f : Quiver.Hom.{succ u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} AddCommGroupCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1})) G H), CategoryTheory.Iso.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Limits.cokernel.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) G H f (CategoryTheory.Limits.HasCokernels.has_colimit.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Limits.hasCokernels_of_hasCoequalizers.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.instPreadditiveAddCommGroupCatInstAddCommGroupCatLargeCategory.{u1}) (CategoryTheory.Limits.hasColimitsOfShapeOfHasColimitsOfSize.{0, 0, u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} CategoryTheory.Limits.WalkingParallelPair CategoryTheory.Limits.walkingParallelPairHomCategory (CategoryTheory.Limits.hasSmallestColimitsOfHasColimits.{u1, succ u1} AddCommGroupCat.{u1} instAddCommGroupCatLargeCategory.{u1} AddCommGroupCat.Colimits.hasColimits_addCommGroupCat.{u1}))) G H f)) (AddCommGroupCat.of.{u1} (HasQuotient.Quotient.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroup.toAddGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroupCat.addCommGroupInstance.{u1} H))) (QuotientAddGroup.instHasQuotientAddSubgroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroup.toAddGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroupCat.addCommGroupInstance.{u1} H))) (AddMonoidHom.range.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} G) (AddCommGroup.toAddGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} G) (AddCommGroupCat.addCommGroupInstance.{u1} G)) (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroup.toAddGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroupCat.addCommGroupInstance.{u1} H)) f)) (QuotientAddGroup.Quotient.addCommGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroupCat.addCommGroupInstance.{u1} H) (AddMonoidHom.range.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} G) (AddCommGroup.toAddGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} G) (AddCommGroupCat.addCommGroupInstance.{u1} G)) (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroup.toAddGroup.{u1} (CategoryTheory.Bundled.α.{u1, u1} AddCommGroup.{u1} H) (AddCommGroupCat.addCommGroupInstance.{u1} H)) f)))
Case conversion may be inaccurate. Consider using '#align AddCommGroup.cokernel_iso_quotient AddCommGroupCat.cokernelIsoQuotientₓ'. -/
/-- The categorical cokernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical quotient.
-/
noncomputable def cokernelIsoQuotient {G H : AddCommGroupCat.{u}} (f : G ⟶ H) :
    cokernel f ≅ AddCommGroupCat.of (H ⧸ AddMonoidHom.range f)
    where
  Hom :=
    cokernel.desc f (mk' _)
      (by
        ext; apply Quotient.sound; apply left_rel_apply.mpr; fconstructor; exact -x
        simp only [add_zero, AddMonoidHom.map_neg])
  inv :=
    QuotientAddGroup.lift _ (cokernel.π f)
      (by
        intro x H_1; cases H_1; induction H_1_h
        simp only [cokernel.condition_apply, zero_apply])
  -- obviously can take care of the next goals, but it is really slow
  hom_inv_id' := by ext1;
    simp only [coequalizer_as_cokernel, category.comp_id, cokernel.π_desc_assoc]; ext1; rfl
  inv_hom_id' := by
    ext x : 2
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, comp_apply, lift_mk,
      cokernel.π_desc_apply, mk'_apply, id_apply]
#align AddCommGroup.cokernel_iso_quotient AddCommGroupCat.cokernelIsoQuotient

end AddCommGroupCat

