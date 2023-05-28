/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.category.Ring.basic
! leanprover-community/mathlib commit dbdf71cee7bb20367cb7e37279c08b0c218cf967
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.Basic
import Mathbin.CategoryTheory.ConcreteCategory.ReflectsIsomorphisms
import Mathbin.CategoryTheory.Elementwise
import Mathbin.Algebra.Ring.Equiv

/-!
# Category instances for semiring, ring, comm_semiring, and comm_ring.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the bundled categories:
* `SemiRing`
* `Ring`
* `CommSemiRing`
* `CommRing`
along with the relevant forgetful functors between them.
-/


universe u v

open CategoryTheory

#print SemiRingCat /-
/-- The category of semirings. -/
def SemiRingCat : Type (u + 1) :=
  Bundled Semiring
#align SemiRing SemiRingCat
-/

namespace SemiRingCat

#print SemiRingCat.AssocRingHom /-
/-- `ring_hom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. We use the same trick in `category_theory.Mon.assoc_monoid_hom`. -/
abbrev AssocRingHom (M N : Type _) [Semiring M] [Semiring N] :=
  RingHom M N
#align SemiRing.assoc_ring_hom SemiRingCat.AssocRingHom
-/

#print SemiRingCat.bundledHom /-
instance bundledHom : BundledHom AssocRingHom :=
  ⟨fun M N [Semiring M] [Semiring N] => @RingHom.toFun M N _ _, fun M [Semiring M] =>
    @RingHom.id M _, fun M N P [Semiring M] [Semiring N] [Semiring P] => @RingHom.comp M N P _ _ _,
    fun M N [Semiring M] [Semiring N] => @RingHom.coe_inj M N _ _⟩
#align SemiRing.bundled_hom SemiRingCat.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for SemiRingCat

instance : CoeSort SemiRingCat (Type _) :=
  Bundled.hasCoeToSort

#print SemiRingCat.of /-
/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [Semiring R] : SemiRingCat :=
  Bundled.of R
#align SemiRing.of SemiRingCat.of
-/

#print SemiRingCat.ofHom /-
/-- Typecheck a `ring_hom` as a morphism in `SemiRing`. -/
def ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : of R ⟶ of S :=
  f
#align SemiRing.of_hom SemiRingCat.ofHom
-/

/- warning: SemiRing.of_hom_apply -> SemiRingCat.ofHom_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align SemiRing.of_hom_apply SemiRingCat.ofHom_applyₓ'. -/
@[simp]
theorem ofHom_apply {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
#align SemiRing.of_hom_apply SemiRingCat.ofHom_apply

instance : Inhabited SemiRingCat :=
  ⟨of PUnit⟩

instance (R : SemiRingCat) : Semiring R :=
  R.str

#print SemiRingCat.coe_of /-
@[simp]
theorem coe_of (R : Type u) [Semiring R] : (SemiRingCat.of R : Type u) = R :=
  rfl
#align SemiRing.coe_of SemiRingCat.coe_of
-/

#print SemiRingCat.hasForgetToMonCat /-
instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat :=
  BundledHom.mkHasForget₂ (fun R hR => @MonoidWithZero.toMonoid R (@Semiring.toMonoidWithZero R hR))
    (fun R₁ R₂ => RingHom.toMonoidHom) fun _ _ _ => rfl
#align SemiRing.has_forget_to_Mon SemiRingCat.hasForgetToMonCat
-/

#print SemiRingCat.hasForgetToAddCommMonCat /-
instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat
    where-- can't use bundled_hom.mk_has_forget₂, since AddCommMon is an induced category
  forget₂ :=
    { obj := fun R => AddCommMonCat.of R
      map := fun R₁ R₂ f => RingHom.toAddMonoidHom f }
#align SemiRing.has_forget_to_AddCommMon SemiRingCat.hasForgetToAddCommMonCat
-/

end SemiRingCat

#print RingCat /-
/-- The category of rings. -/
def RingCat : Type (u + 1) :=
  Bundled Ring
#align Ring RingCat
-/

namespace RingCat

instance : BundledHom.ParentProjection @Ring.toSemiring :=
  ⟨⟩

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler λ Ring,
has_coe_to_sort[has_coe_to_sort] Ring (Type*) -/
deriving instance
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler λ Ring,
  has_coe_to_sort[has_coe_to_sort] Ring (Type*)», LargeCategory, ConcreteCategory for RingCat

#print RingCat.of /-
/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [Ring R] : RingCat :=
  Bundled.of R
#align Ring.of RingCat.of
-/

#print RingCat.ofHom /-
/-- Typecheck a `ring_hom` as a morphism in `Ring`. -/
def ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : of R ⟶ of S :=
  f
#align Ring.of_hom RingCat.ofHom
-/

@[simp]
theorem ofHom_apply {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (x : R) : ofHom f x = f x :=
  rfl
#align Ring.of_hom_apply RingCat.ofHom_apply

instance : Inhabited RingCat :=
  ⟨of PUnit⟩

instance (R : RingCat) : Ring R :=
  R.str

#print RingCat.coe_of /-
@[simp]
theorem coe_of (R : Type u) [Ring R] : (RingCat.of R : Type u) = R :=
  rfl
#align Ring.coe_of RingCat.coe_of
-/

#print RingCat.hasForgetToSemiRingCat /-
instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat :=
  BundledHom.forget₂ _ _
#align Ring.has_forget_to_SemiRing RingCat.hasForgetToSemiRingCat
-/

#print RingCat.hasForgetToAddCommGroupCat /-
instance hasForgetToAddCommGroupCat : HasForget₂ RingCat AddCommGroupCat
    where-- can't use bundled_hom.mk_has_forget₂, since AddCommGroup is an induced category
  forget₂ :=
    { obj := fun R => AddCommGroupCat.of R
      map := fun R₁ R₂ f => RingHom.toAddMonoidHom f }
#align Ring.has_forget_to_AddCommGroup RingCat.hasForgetToAddCommGroupCat
-/

end RingCat

#print CommSemiRingCat /-
/-- The category of commutative semirings. -/
def CommSemiRingCat : Type (u + 1) :=
  Bundled CommSemiring
#align CommSemiRing CommSemiRingCat
-/

namespace CommSemiRingCat

instance : BundledHom.ParentProjection @CommSemiring.toSemiring :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommSemiRingCat

instance : CoeSort CommSemiRingCat (Type _) :=
  Bundled.hasCoeToSort

#print CommSemiRing.of /-
/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [CommSemiring R] : CommSemiRingCat :=
  Bundled.of R
#align CommSemiRing.of CommSemiRing.of
-/

#print CommSemiRing.ofHom /-
/-- Typecheck a `ring_hom` as a morphism in `CommSemiRing`. -/
def ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) : of R ⟶ of S :=
  f
#align CommSemiRing.of_hom CommSemiRing.ofHom
-/

/- warning: CommSemiRing.of_hom_apply clashes with [anonymous] -> [anonymous]
warning: CommSemiRing.of_hom_apply -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} {S : Type.{u}} [_inst_1 : CommSemiring.{u} R] [_inst_2 : CommSemiring.{u} S] (f : RingHom.{u, u} R S (Semiring.toNonAssocSemiring.{u} R (CommSemiring.toSemiring.{u} R _inst_1)) (Semiring.toNonAssocSemiring.{u} S (CommSemiring.toSemiring.{u} S _inst_2))) (x : R), Eq.{succ u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} S _inst_2)) (coeFn.{succ u, succ u} (Quiver.Hom.{succ u, succ u} CommSemiRingCat.{u} (CategoryTheory.CategoryStruct.toQuiver.{u, succ u} CommSemiRingCat.{u} (CategoryTheory.Category.toCategoryStruct.{u, succ u} CommSemiRingCat.{u} CommSemiRingCat.largeCategory.{u})) (CommSemiRing.of.{u} R _inst_1) (CommSemiRing.of.{u} S _inst_2)) (fun (_x : RingHom.{u, u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} R _inst_1)) (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} S _inst_2)) (Semiring.toNonAssocSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} R _inst_1)) (CommSemiring.toSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} R _inst_1)) (CategoryTheory.Bundled.str.{u, u} CommSemiring.{u} (CommSemiRing.of.{u} R _inst_1)))) (Semiring.toNonAssocSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} S _inst_2)) (CommSemiring.toSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} S _inst_2)) (CategoryTheory.Bundled.str.{u, u} CommSemiring.{u} (CommSemiRing.of.{u} S _inst_2))))) => (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} R _inst_1)) -> (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} S _inst_2))) (RingHom.hasCoeToFun.{u, u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} R _inst_1)) (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} S _inst_2)) (Semiring.toNonAssocSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} R _inst_1)) (CommSemiring.toSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} R _inst_1)) (CategoryTheory.Bundled.str.{u, u} CommSemiring.{u} (CommSemiRing.of.{u} R _inst_1)))) (Semiring.toNonAssocSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} S _inst_2)) (CommSemiring.toSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommSemiring.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommSemiring.{u}) (CommSemiRing.of.{u} S _inst_2)) (CategoryTheory.Bundled.str.{u, u} CommSemiring.{u} (CommSemiRing.of.{u} S _inst_2))))) (CommSemiRing.ofHom.{u} R S _inst_1 _inst_2 f) x) (coeFn.{succ u, succ u} (RingHom.{u, u} R S (Semiring.toNonAssocSemiring.{u} R (CommSemiring.toSemiring.{u} R _inst_1)) (Semiring.toNonAssocSemiring.{u} S (CommSemiring.toSemiring.{u} S _inst_2))) (fun (_x : RingHom.{u, u} R S (Semiring.toNonAssocSemiring.{u} R (CommSemiring.toSemiring.{u} R _inst_1)) (Semiring.toNonAssocSemiring.{u} S (CommSemiring.toSemiring.{u} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u, u} R S (Semiring.toNonAssocSemiring.{u} R (CommSemiring.toSemiring.{u} R _inst_1)) (Semiring.toNonAssocSemiring.{u} S (CommSemiring.toSemiring.{u} S _inst_2))) f x)
but is expected to have type
  forall {R : Type.{u}} {S : Type.{v}}, (Nat -> R -> S) -> Nat -> (List.{u} R) -> (List.{v} S)
Case conversion may be inaccurate. Consider using '#align CommSemiRing.of_hom_apply [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
#align CommSemiRing.of_hom_apply [anonymous]

instance : Inhabited CommSemiRingCat :=
  ⟨of PUnit⟩

instance (R : CommSemiRingCat) : CommSemiring R :=
  R.str

#print CommSemiRing.coe_of /-
@[simp]
theorem coe_of (R : Type u) [CommSemiring R] : (CommSemiRing.of R : Type u) = R :=
  rfl
#align CommSemiRing.coe_of CommSemiRing.coe_of
-/

#print CommSemiRing.hasForgetToSemiRingCat /-
instance hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat :=
  BundledHom.forget₂ _ _
#align CommSemiRing.has_forget_to_SemiRing CommSemiRing.hasForgetToSemiRingCat
-/

#print CommSemiRing.hasForgetToCommMonCat /-
/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat :=
  HasForget₂.mk' (fun R : CommSemiRingCat => CommMonCat.of R) (fun R => rfl)
    (fun R₁ R₂ f => f.toMonoidHom) (by tidy)
#align CommSemiRing.has_forget_to_CommMon CommSemiRing.hasForgetToCommMonCat
-/

end CommSemiRingCat

#print CommRingCat /-
/-- The category of commutative rings. -/
def CommRingCat : Type (u + 1) :=
  Bundled CommRing
#align CommRing CommRingCat
-/

namespace CommRingCat

instance : BundledHom.ParentProjection @CommRing.toRing :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommRingCat

instance : CoeSort CommRingCat (Type _) :=
  Bundled.hasCoeToSort

#print CommRingCat.of /-
/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [CommRing R] : CommRingCat :=
  Bundled.of R
#align CommRing.of CommRingCat.of
-/

#print CommRingCat.ofHom /-
/-- Typecheck a `ring_hom` as a morphism in `CommRing`. -/
def ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : of R ⟶ of S :=
  f
#align CommRing.of_hom CommRingCat.ofHom
-/

/- warning: CommRing.of_hom_apply clashes with [anonymous] -> [anonymous]
warning: CommRing.of_hom_apply -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} {S : Type.{u}} [_inst_1 : CommRing.{u} R] [_inst_2 : CommRing.{u} S] (f : RingHom.{u, u} R S (NonAssocRing.toNonAssocSemiring.{u} R (Ring.toNonAssocRing.{u} R (CommRing.toRing.{u} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u} S (Ring.toNonAssocRing.{u} S (CommRing.toRing.{u} S _inst_2)))) (x : R), Eq.{succ u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (coeFn.{succ u, succ u} (Quiver.Hom.{succ u, succ u} CommRingCat.{u} (CategoryTheory.CategoryStruct.toQuiver.{u, succ u} CommRingCat.{u} (CategoryTheory.Category.toCategoryStruct.{u, succ u} CommRingCat.{u} CommRingCat.largeCategory.{u})) (CommRingCat.of.{u} R _inst_1) (CommRingCat.of.{u} S _inst_2)) (fun (_x : RingHom.{u, u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (Semiring.toNonAssocSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) (Ring.toSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) (CommRing.toRing.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) (CategoryTheory.Bundled.str.{u, u} CommRing.{u} (CommRingCat.of.{u} R _inst_1))))) (Semiring.toNonAssocSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (Ring.toSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (CommRing.toRing.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (CategoryTheory.Bundled.str.{u, u} CommRing.{u} (CommRingCat.of.{u} S _inst_2)))))) => (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) -> (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2))) (RingHom.hasCoeToFun.{u, u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (Semiring.toNonAssocSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) (Ring.toSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) (CommRing.toRing.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} R _inst_1)) (CategoryTheory.Bundled.str.{u, u} CommRing.{u} (CommRingCat.of.{u} R _inst_1))))) (Semiring.toNonAssocSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (Ring.toSemiring.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (CommRing.toRing.{u} (coeSort.{succ (succ u), succ (succ u)} (CategoryTheory.Bundled.{u, u} CommRing.{u}) Type.{u} (CategoryTheory.Bundled.hasCoeToSort.{u, u} CommRing.{u}) (CommRingCat.of.{u} S _inst_2)) (CategoryTheory.Bundled.str.{u, u} CommRing.{u} (CommRingCat.of.{u} S _inst_2)))))) (CommRingCat.ofHom.{u} R S _inst_1 _inst_2 f) x) (coeFn.{succ u, succ u} (RingHom.{u, u} R S (NonAssocRing.toNonAssocSemiring.{u} R (Ring.toNonAssocRing.{u} R (CommRing.toRing.{u} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u} S (Ring.toNonAssocRing.{u} S (CommRing.toRing.{u} S _inst_2)))) (fun (_x : RingHom.{u, u} R S (NonAssocRing.toNonAssocSemiring.{u} R (Ring.toNonAssocRing.{u} R (CommRing.toRing.{u} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u} S (Ring.toNonAssocRing.{u} S (CommRing.toRing.{u} S _inst_2)))) => R -> S) (RingHom.hasCoeToFun.{u, u} R S (NonAssocRing.toNonAssocSemiring.{u} R (Ring.toNonAssocRing.{u} R (CommRing.toRing.{u} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u} S (Ring.toNonAssocRing.{u} S (CommRing.toRing.{u} S _inst_2)))) f x)
but is expected to have type
  forall {R : Type.{u}} {S : Type.{v}}, (Nat -> R -> S) -> Nat -> (List.{u} R) -> (List.{v} S)
Case conversion may be inaccurate. Consider using '#align CommRing.of_hom_apply [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    ofHom f x = f x :=
  rfl
#align CommRing.of_hom_apply [anonymous]

instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

instance (R : CommRingCat) : CommRing R :=
  R.str

#print CommRingCat.coe_of /-
@[simp]
theorem coe_of (R : Type u) [CommRing R] : (CommRingCat.of R : Type u) = R :=
  rfl
#align CommRing.coe_of CommRingCat.coe_of
-/

#print CommRingCat.hasForgetToRingCat /-
instance hasForgetToRingCat : HasForget₂ CommRingCat RingCat :=
  BundledHom.forget₂ _ _
#align CommRing.has_forget_to_Ring CommRingCat.hasForgetToRingCat
-/

#print CommRingCat.hasForgetToCommSemiRingCat /-
/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
instance hasForgetToCommSemiRingCat : HasForget₂ CommRingCat CommSemiRingCat :=
  HasForget₂.mk' (fun R : CommRingCat => CommSemiRing.of R) (fun R => rfl) (fun R₁ R₂ f => f)
    (by tidy)
#align CommRing.has_forget_to_CommSemiRing CommRingCat.hasForgetToCommSemiRingCat
-/

instance : Full (forget₂ CommRingCat CommSemiRingCat) where preimage X Y f := f

end CommRingCat

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `add_ring_hom.map_zero` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
example {R S : CommRingCat} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 := by simp [h]

namespace RingEquiv

variable {X Y : Type u}

/- warning: ring_equiv.to_Ring_iso -> RingEquiv.toRingCatIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Ring.{u1} X] [_inst_2 : Ring.{u1} Y], (RingEquiv.{u1, u1} X Y (Distrib.toHasMul.{u1} X (Ring.toDistrib.{u1} X _inst_1)) (Distrib.toHasAdd.{u1} X (Ring.toDistrib.{u1} X _inst_1)) (Distrib.toHasMul.{u1} Y (Ring.toDistrib.{u1} Y _inst_2)) (Distrib.toHasAdd.{u1} Y (Ring.toDistrib.{u1} Y _inst_2))) -> (CategoryTheory.Iso.{u1, succ u1} RingCat.{u1} RingCat.largeCategory.{u1} (RingCat.of.{u1} X _inst_1) (RingCat.of.{u1} Y _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Ring.{u1} X] [_inst_2 : Ring.{u1} Y], (RingEquiv.{u1, u1} X Y (NonUnitalNonAssocRing.toMul.{u1} X (NonAssocRing.toNonUnitalNonAssocRing.{u1} X (Ring.toNonAssocRing.{u1} X _inst_1))) (NonUnitalNonAssocRing.toMul.{u1} Y (NonAssocRing.toNonUnitalNonAssocRing.{u1} Y (Ring.toNonAssocRing.{u1} Y _inst_2))) (Distrib.toAdd.{u1} X (NonUnitalNonAssocSemiring.toDistrib.{u1} X (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} X (NonAssocRing.toNonUnitalNonAssocRing.{u1} X (Ring.toNonAssocRing.{u1} X _inst_1))))) (Distrib.toAdd.{u1} Y (NonUnitalNonAssocSemiring.toDistrib.{u1} Y (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} Y (NonAssocRing.toNonUnitalNonAssocRing.{u1} Y (Ring.toNonAssocRing.{u1} Y _inst_2)))))) -> (CategoryTheory.Iso.{u1, succ u1} RingCat.{u1} instRingCatLargeCategory.{u1} (RingCat.of.{u1} X _inst_1) (RingCat.of.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align ring_equiv.to_Ring_iso RingEquiv.toRingCatIsoₓ'. -/
/-- Build an isomorphism in the category `Ring` from a `ring_equiv` between `ring`s. -/
@[simps]
def toRingCatIso [Ring X] [Ring Y] (e : X ≃+* Y) : RingCat.of X ≅ RingCat.of Y
    where
  Hom := e.toRingHom
  inv := e.symm.toRingHom
#align ring_equiv.to_Ring_iso RingEquiv.toRingCatIso

/- warning: ring_equiv.to_CommRing_iso -> RingEquiv.toCommRingCatIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : CommRing.{u1} X] [_inst_2 : CommRing.{u1} Y], (RingEquiv.{u1, u1} X Y (Distrib.toHasMul.{u1} X (Ring.toDistrib.{u1} X (CommRing.toRing.{u1} X _inst_1))) (Distrib.toHasAdd.{u1} X (Ring.toDistrib.{u1} X (CommRing.toRing.{u1} X _inst_1))) (Distrib.toHasMul.{u1} Y (Ring.toDistrib.{u1} Y (CommRing.toRing.{u1} Y _inst_2))) (Distrib.toHasAdd.{u1} Y (Ring.toDistrib.{u1} Y (CommRing.toRing.{u1} Y _inst_2)))) -> (CategoryTheory.Iso.{u1, succ u1} CommRingCat.{u1} CommRingCat.largeCategory.{u1} (CommRingCat.of.{u1} X _inst_1) (CommRingCat.of.{u1} Y _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : CommRing.{u1} X] [_inst_2 : CommRing.{u1} Y], (RingEquiv.{u1, u1} X Y (NonUnitalNonAssocRing.toMul.{u1} X (NonAssocRing.toNonUnitalNonAssocRing.{u1} X (Ring.toNonAssocRing.{u1} X (CommRing.toRing.{u1} X _inst_1)))) (NonUnitalNonAssocRing.toMul.{u1} Y (NonAssocRing.toNonUnitalNonAssocRing.{u1} Y (Ring.toNonAssocRing.{u1} Y (CommRing.toRing.{u1} Y _inst_2)))) (Distrib.toAdd.{u1} X (NonUnitalNonAssocSemiring.toDistrib.{u1} X (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} X (NonAssocRing.toNonUnitalNonAssocRing.{u1} X (Ring.toNonAssocRing.{u1} X (CommRing.toRing.{u1} X _inst_1)))))) (Distrib.toAdd.{u1} Y (NonUnitalNonAssocSemiring.toDistrib.{u1} Y (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} Y (NonAssocRing.toNonUnitalNonAssocRing.{u1} Y (Ring.toNonAssocRing.{u1} Y (CommRing.toRing.{u1} Y _inst_2))))))) -> (CategoryTheory.Iso.{u1, succ u1} CommRingCat.{u1} instCommRingCatLargeCategory.{u1} (CommRingCat.of.{u1} X _inst_1) (CommRingCat.of.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align ring_equiv.to_CommRing_iso RingEquiv.toCommRingCatIsoₓ'. -/
/-- Build an isomorphism in the category `CommRing` from a `ring_equiv` between `comm_ring`s. -/
@[simps]
def toCommRingCatIso [CommRing X] [CommRing Y] (e : X ≃+* Y) : CommRingCat.of X ≅ CommRingCat.of Y
    where
  Hom := e.toRingHom
  inv := e.symm.toRingHom
#align ring_equiv.to_CommRing_iso RingEquiv.toCommRingCatIso

end RingEquiv

namespace CategoryTheory.Iso

/- warning: category_theory.iso.Ring_iso_to_ring_equiv -> CategoryTheory.Iso.ringCatIsoToRingEquiv is a dubious translation:
lean 3 declaration is
  forall {X : RingCat.{u1}} {Y : RingCat.{u1}}, (CategoryTheory.Iso.{u1, succ u1} RingCat.{u1} RingCat.largeCategory.{u1} X Y) -> (RingEquiv.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} X) (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} Y) (Distrib.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} X) (Ring.toDistrib.{u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} X) (RingCat.ring.{u1} X))) (Distrib.toHasAdd.{u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} X) (Ring.toDistrib.{u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} X) (RingCat.ring.{u1} X))) (Distrib.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} Y) (Ring.toDistrib.{u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} Y) (RingCat.ring.{u1} Y))) (Distrib.toHasAdd.{u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} Y) (Ring.toDistrib.{u1} (coeSort.{succ (succ u1), succ (succ u1)} RingCat.{u1} Type.{u1} RingCat.hasCoeToSort.{u1} Y) (RingCat.ring.{u1} Y))))
but is expected to have type
  forall {X : RingCat.{u1}} {Y : RingCat.{u1}}, (CategoryTheory.Iso.{u1, succ u1} RingCat.{u1} instRingCatLargeCategory.{u1} X Y) -> (RingEquiv.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (NonUnitalNonAssocRing.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (RingCat.instRingα_1.{u1} X)))) (NonUnitalNonAssocRing.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (RingCat.instRingα_1.{u1} Y)))) (Distrib.toAdd.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (NonUnitalNonAssocSemiring.toDistrib.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} X) (RingCat.instRingα_1.{u1} X)))))) (Distrib.toAdd.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (NonUnitalNonAssocSemiring.toDistrib.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} Ring.{u1} Y) (RingCat.instRingα_1.{u1} Y)))))))
Case conversion may be inaccurate. Consider using '#align category_theory.iso.Ring_iso_to_ring_equiv CategoryTheory.Iso.ringCatIsoToRingEquivₓ'. -/
/-- Build a `ring_equiv` from an isomorphism in the category `Ring`. -/
def ringCatIsoToRingEquiv {X Y : RingCat} (i : X ≅ Y) : X ≃+* Y
    where
  toFun := i.Hom
  invFun := i.inv
  left_inv := by tidy
  right_inv := by tidy
  map_add' := by tidy
  map_mul' := by tidy
#align category_theory.iso.Ring_iso_to_ring_equiv CategoryTheory.Iso.ringCatIsoToRingEquiv

/- warning: category_theory.iso.CommRing_iso_to_ring_equiv -> CategoryTheory.Iso.commRingCatIsoToRingEquiv is a dubious translation:
lean 3 declaration is
  forall {X : CommRingCat.{u1}} {Y : CommRingCat.{u1}}, (CategoryTheory.Iso.{u1, succ u1} CommRingCat.{u1} CommRingCat.largeCategory.{u1} X Y) -> (RingEquiv.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} X) (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} Y) (Distrib.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} X) (Ring.toDistrib.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} X) (CommRing.toRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} X) (CommRingCat.commRing.{u1} X)))) (Distrib.toHasAdd.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} X) (Ring.toDistrib.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} X) (CommRing.toRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} X) (CommRingCat.commRing.{u1} X)))) (Distrib.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} Y) (Ring.toDistrib.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} Y) (CommRing.toRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} Y) (CommRingCat.commRing.{u1} Y)))) (Distrib.toHasAdd.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} Y) (Ring.toDistrib.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} Y) (CommRing.toRing.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} Y) (CommRingCat.commRing.{u1} Y)))))
but is expected to have type
  forall {X : CommRingCat.{u1}} {Y : CommRingCat.{u1}}, (CategoryTheory.Iso.{u1, succ u1} CommRingCat.{u1} instCommRingCatLargeCategory.{u1} X Y) -> (RingEquiv.{u1, u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (NonUnitalNonAssocRing.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (CommRing.toRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (CommRingCat.instCommRingα_1.{u1} X))))) (NonUnitalNonAssocRing.toMul.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (CommRing.toRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (CommRingCat.instCommRingα_1.{u1} Y))))) (Distrib.toAdd.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (NonUnitalNonAssocSemiring.toDistrib.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (CommRing.toRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} X) (CommRingCat.instCommRingα_1.{u1} X))))))) (Distrib.toAdd.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (NonUnitalNonAssocSemiring.toDistrib.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (NonAssocRing.toNonUnitalNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (Ring.toNonAssocRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (CommRing.toRing.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} Y) (CommRingCat.instCommRingα_1.{u1} Y))))))))
Case conversion may be inaccurate. Consider using '#align category_theory.iso.CommRing_iso_to_ring_equiv CategoryTheory.Iso.commRingCatIsoToRingEquivₓ'. -/
/-- Build a `ring_equiv` from an isomorphism in the category `CommRing`. -/
def commRingCatIsoToRingEquiv {X Y : CommRingCat} (i : X ≅ Y) : X ≃+* Y
    where
  toFun := i.Hom
  invFun := i.inv
  left_inv := by tidy
  right_inv := by tidy
  map_add' := by tidy
  map_mul' := by tidy
#align category_theory.iso.CommRing_iso_to_ring_equiv CategoryTheory.Iso.commRingCatIsoToRingEquiv

#print CategoryTheory.Iso.commRingIsoToRingEquiv_toRingHom /-
@[simp]
theorem commRingIsoToRingEquiv_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.toRingHom = i.Hom :=
  by
  ext
  rfl
#align category_theory.iso.CommRing_iso_to_ring_equiv_to_ring_hom CategoryTheory.Iso.commRingIsoToRingEquiv_toRingHom
-/

#print CategoryTheory.Iso.commRingIsoToRingEquiv_symm_toRingHom /-
@[simp]
theorem commRingIsoToRingEquiv_symm_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.symm.toRingHom = i.inv :=
  by
  ext
  rfl
#align category_theory.iso.CommRing_iso_to_ring_equiv_symm_to_ring_hom CategoryTheory.Iso.commRingIsoToRingEquiv_symm_toRingHom
-/

end CategoryTheory.Iso

/- warning: ring_equiv_iso_Ring_iso -> ringEquivIsoRingIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Ring.{u1} X] [_inst_2 : Ring.{u1} Y], CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (RingEquiv.{u1, u1} X Y (Distrib.toHasMul.{u1} X (Ring.toDistrib.{u1} X _inst_1)) (Distrib.toHasAdd.{u1} X (Ring.toDistrib.{u1} X _inst_1)) (Distrib.toHasMul.{u1} Y (Ring.toDistrib.{u1} Y _inst_2)) (Distrib.toHasAdd.{u1} Y (Ring.toDistrib.{u1} Y _inst_2))) (CategoryTheory.Iso.{u1, succ u1} RingCat.{u1} RingCat.largeCategory.{u1} (RingCat.of.{u1} X _inst_1) (RingCat.of.{u1} Y _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Ring.{u1} X] [_inst_2 : Ring.{u1} Y], CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (RingEquiv.{u1, u1} X Y (NonUnitalNonAssocRing.toMul.{u1} X (NonAssocRing.toNonUnitalNonAssocRing.{u1} X (Ring.toNonAssocRing.{u1} X _inst_1))) (NonUnitalNonAssocRing.toMul.{u1} Y (NonAssocRing.toNonUnitalNonAssocRing.{u1} Y (Ring.toNonAssocRing.{u1} Y _inst_2))) (Distrib.toAdd.{u1} X (NonUnitalNonAssocSemiring.toDistrib.{u1} X (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} X (NonAssocRing.toNonUnitalNonAssocRing.{u1} X (Ring.toNonAssocRing.{u1} X _inst_1))))) (Distrib.toAdd.{u1} Y (NonUnitalNonAssocSemiring.toDistrib.{u1} Y (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} Y (NonAssocRing.toNonUnitalNonAssocRing.{u1} Y (Ring.toNonAssocRing.{u1} Y _inst_2)))))) (CategoryTheory.Iso.{u1, succ u1} RingCat.{u1} instRingCatLargeCategory.{u1} (RingCat.of.{u1} X _inst_1) (RingCat.of.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align ring_equiv_iso_Ring_iso ringEquivIsoRingIsoₓ'. -/
/-- Ring equivalences between `ring`s are the same as (isomorphic to) isomorphisms in `Ring`. -/
def ringEquivIsoRingIso {X Y : Type u} [Ring X] [Ring Y] : X ≃+* Y ≅ RingCat.of X ≅ RingCat.of Y
    where
  Hom e := e.toRingCatIso
  inv i := i.ringCatIsoToRingEquiv
#align ring_equiv_iso_Ring_iso ringEquivIsoRingIso

/- warning: ring_equiv_iso_CommRing_iso -> ringEquivIsoCommRingIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : CommRing.{u1} X] [_inst_2 : CommRing.{u1} Y], CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (RingEquiv.{u1, u1} X Y (Distrib.toHasMul.{u1} X (Ring.toDistrib.{u1} X (CommRing.toRing.{u1} X _inst_1))) (Distrib.toHasAdd.{u1} X (Ring.toDistrib.{u1} X (CommRing.toRing.{u1} X _inst_1))) (Distrib.toHasMul.{u1} Y (Ring.toDistrib.{u1} Y (CommRing.toRing.{u1} Y _inst_2))) (Distrib.toHasAdd.{u1} Y (Ring.toDistrib.{u1} Y (CommRing.toRing.{u1} Y _inst_2)))) (CategoryTheory.Iso.{u1, succ u1} CommRingCat.{u1} CommRingCat.largeCategory.{u1} (CommRingCat.of.{u1} X _inst_1) (CommRingCat.of.{u1} Y _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : CommRing.{u1} X] [_inst_2 : CommRing.{u1} Y], CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (RingEquiv.{u1, u1} X Y (NonUnitalNonAssocRing.toMul.{u1} X (NonAssocRing.toNonUnitalNonAssocRing.{u1} X (Ring.toNonAssocRing.{u1} X (CommRing.toRing.{u1} X _inst_1)))) (NonUnitalNonAssocRing.toMul.{u1} Y (NonAssocRing.toNonUnitalNonAssocRing.{u1} Y (Ring.toNonAssocRing.{u1} Y (CommRing.toRing.{u1} Y _inst_2)))) (Distrib.toAdd.{u1} X (NonUnitalNonAssocSemiring.toDistrib.{u1} X (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} X (NonAssocRing.toNonUnitalNonAssocRing.{u1} X (Ring.toNonAssocRing.{u1} X (CommRing.toRing.{u1} X _inst_1)))))) (Distrib.toAdd.{u1} Y (NonUnitalNonAssocSemiring.toDistrib.{u1} Y (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} Y (NonAssocRing.toNonUnitalNonAssocRing.{u1} Y (Ring.toNonAssocRing.{u1} Y (CommRing.toRing.{u1} Y _inst_2))))))) (CategoryTheory.Iso.{u1, succ u1} CommRingCat.{u1} instCommRingCatLargeCategory.{u1} (CommRingCat.of.{u1} X _inst_1) (CommRingCat.of.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align ring_equiv_iso_CommRing_iso ringEquivIsoCommRingIsoₓ'. -/
/-- Ring equivalences between `comm_ring`s are the same as (isomorphic to) isomorphisms
in `CommRing`. -/
def ringEquivIsoCommRingIso {X Y : Type u} [CommRing X] [CommRing Y] :
    X ≃+* Y ≅ CommRingCat.of X ≅ CommRingCat.of Y
    where
  Hom e := e.toCommRingCatIso
  inv i := i.commRingCatIsoToRingEquiv
#align ring_equiv_iso_CommRing_iso ringEquivIsoCommRingIso

#print RingCat.forget_reflects_isos /-
instance RingCat.forget_reflects_isos : ReflectsIsomorphisms (forget RingCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget RingCat).map f)
    let e : X ≃+* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Ring_iso).1⟩
#align Ring.forget_reflects_isos RingCat.forget_reflects_isos
-/

#print CommRingCat.forget_reflects_isos /-
instance CommRingCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommRingCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget CommRingCat).map f)
    let e : X ≃+* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommRing_iso).1⟩
#align CommRing.forget_reflects_isos CommRingCat.forget_reflects_isos
-/

#print CommRingCat.comp_eq_ring_hom_comp /-
theorem CommRingCat.comp_eq_ring_hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g.comp f :=
  rfl
#align CommRing.comp_eq_ring_hom_comp CommRingCat.comp_eq_ring_hom_comp
-/

#print CommRingCat.ringHom_comp_eq_comp /-
theorem CommRingCat.ringHom_comp_eq_comp {R S T : Type _} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) : g.comp f = CommRingCat.ofHom f ≫ CommRingCat.ofHom g :=
  rfl
#align CommRing.ring_hom_comp_eq_comp CommRingCat.ringHom_comp_eq_comp
-/

-- It would be nice if we could have the following,
-- but it requires making `reflects_isomorphisms_forget₂` an instance,
-- which can cause typeclass loops:
attribute [local instance] reflects_isomorphisms_forget₂

example : ReflectsIsomorphisms (forget₂ RingCat AddCommGroupCat) := by infer_instance

