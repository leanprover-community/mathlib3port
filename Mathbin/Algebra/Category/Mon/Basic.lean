/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Mon.basic
! leanprover-community/mathlib commit 4125b9adf2e268d1cf438092d690a78f7c664743
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Algebra.PunitInstances
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-!
# Category instances for monoid, add_monoid, comm_monoid, and add_comm_monoid.

We introduce the bundled categories:
* `Mon`
* `AddMon`
* `CommMon`
* `AddCommMon`
along with the relevant forgetful functors between them.
-/


universe u v

open CategoryTheory

#print MonCat /-
/-- The category of monoids and monoid morphisms. -/
@[to_additive AddMonCat]
def MonCat : Type (u + 1) :=
  Bundled Monoid
#align Mon MonCat
#align AddMon AddMonCat
-/

/-- The category of additive monoids and monoid morphisms. -/
add_decl_doc AddMonCat

namespace MonCat

#print MonCat.AssocMonoidHom /-
/-- `monoid_hom` doesn't actually assume associativity. This alias is needed to make the category
theory machinery work. -/
@[to_additive
      "`add_monoid_hom` doesn't actually assume associativity. This alias is needed to make\nthe category theory machinery work."]
abbrev AssocMonoidHom (M N : Type _) [Monoid M] [Monoid N] :=
  MonoidHom M N
#align Mon.assoc_monoid_hom MonCat.AssocMonoidHom
#align AddMon.assoc_add_monoid_hom AddMonCat.AssocAddMonoidHom
-/

#print MonCat.bundledHom /-
@[to_additive]
instance bundledHom : BundledHom AssocMonoidHom :=
  ⟨fun M N [Monoid M] [Monoid N] => @MonoidHom.toFun M N _ _, fun M [Monoid M] => @MonoidHom.id M _,
    fun M N P [Monoid M] [Monoid N] [Monoid P] => @MonoidHom.comp M N P _ _ _,
    fun M N [Monoid M] [Monoid N] => @MonoidHom.coe_inj M N _ _⟩
#align Mon.bundled_hom MonCat.bundledHom
#align AddMon.bundled_hom AddMonCat.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for MonCat

attribute [to_additive] MonCat.largeCategory MonCat.concreteCategory

@[to_additive]
instance : CoeSort MonCat (Type _) :=
  Bundled.hasCoeToSort

#print MonCat.of /-
/-- Construct a bundled `Mon` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [Monoid M] : MonCat :=
  Bundled.of M
#align Mon.of MonCat.of
#align AddMon.of AddMonCat.of
-/

/-- Construct a bundled `Mon` from the underlying type and typeclass. -/
add_decl_doc AddMonCat.of

#print MonCat.ofHom /-
/-- Typecheck a `monoid_hom` as a morphism in `Mon`. -/
@[to_additive]
def ofHom {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) : of X ⟶ of Y :=
  f
#align Mon.of_hom MonCat.ofHom
#align AddMon.of_hom AddMonCat.ofHom
-/

/-- Typecheck a `add_monoid_hom` as a morphism in `AddMon`. -/
add_decl_doc AddMonCat.ofHom

/- warning: Mon.of_hom_apply -> MonCat.ofHom_apply is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Monoid.{u1} X] [_inst_2 : Monoid.{u1} Y] (f : MonoidHom.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)) (x : X), Eq.{succ u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} Y _inst_2)) (coeFn.{succ u1, succ u1} (Quiver.Hom.{succ u1, succ u1} MonCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} MonCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1})) (MonCat.of.{u1} X _inst_1) (MonCat.of.{u1} Y _inst_2)) (fun (_x : MonoidHom.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} X _inst_1)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} Y _inst_2)) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} X _inst_1)) (CategoryTheory.Bundled.str.{u1, u1} Monoid.{u1} (MonCat.of.{u1} X _inst_1))) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} Y _inst_2)) (CategoryTheory.Bundled.str.{u1, u1} Monoid.{u1} (MonCat.of.{u1} Y _inst_2)))) => (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} X _inst_1)) -> (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} Y _inst_2))) (MonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} X _inst_1)) (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} Y _inst_2)) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} X _inst_1)) (CategoryTheory.Bundled.str.{u1, u1} Monoid.{u1} (MonCat.of.{u1} X _inst_1))) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (CategoryTheory.Bundled.{u1, u1} Monoid.{u1}) Type.{u1} (CategoryTheory.Bundled.hasCoeToSort.{u1, u1} Monoid.{u1}) (MonCat.of.{u1} Y _inst_2)) (CategoryTheory.Bundled.str.{u1, u1} Monoid.{u1} (MonCat.of.{u1} Y _inst_2)))) (MonCat.ofHom.{u1} X Y _inst_1 _inst_2 f) x) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)) (fun (_x : MonoidHom.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)) => X -> Y) (MonoidHom.hasCoeToFun.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)) f x)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Monoid.{u1} X] [_inst_2 : Monoid.{u1} Y] (f : MonoidHom.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)) (x : X), Eq.{succ u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} MonCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} MonCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} MonCat.{u1} MonCat.largeCategory.{u1} MonCat.concreteCategory.{u1})) (MonCat.of.{u1} Y _inst_2)) (Prefunctor.map.{succ u1, succ u1, succ u1, succ u1} MonCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} MonCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1})) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.forget.{succ u1, u1, u1} MonCat.{u1} MonCat.largeCategory.{u1} MonCat.concreteCategory.{u1})) (MonCat.of.{u1} X _inst_1) (MonCat.of.{u1} Y _inst_2) (MonCat.ofHom.{u1} X Y _inst_1 _inst_2 f) x) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)) X (fun (_x : X) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : X) => Y) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)) X Y (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X _inst_1)) (MulOneClass.toMul.{u1} Y (Monoid.toMulOneClass.{u1} Y _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)) X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2) (MonoidHom.monoidHomClass.{u1, u1} X Y (Monoid.toMulOneClass.{u1} X _inst_1) (Monoid.toMulOneClass.{u1} Y _inst_2)))) f x)
Case conversion may be inaccurate. Consider using '#align Mon.of_hom_apply MonCat.ofHom_applyₓ'. -/
@[simp]
theorem ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) : ofHom f x = f x :=
  rfl
#align Mon.of_hom_apply MonCat.ofHom_apply

@[to_additive]
instance : Inhabited MonCat :=
  ⟨-- The default instance for `monoid punit` is derived via `punit.comm_ring`,
        -- which breaks to_additive.
        @of
        PUnit <|
      @Group.toMonoid _ <| @CommGroup.toGroup _ PUnit.commGroup⟩

@[to_additive]
instance (M : MonCat) : Monoid M :=
  M.str

#print MonCat.coe_of /-
@[simp, to_additive]
theorem coe_of (R : Type u) [Monoid R] : (MonCat.of R : Type u) = R :=
  rfl
#align Mon.coe_of MonCat.coe_of
#align AddMon.coe_of AddMonCat.coe_of
-/

end MonCat

#print CommMonCat /-
/-- The category of commutative monoids and monoid morphisms. -/
@[to_additive AddCommMonCat]
def CommMonCat : Type (u + 1) :=
  Bundled CommMonoid
#align CommMon CommMonCat
#align AddCommMon AddCommMonCat
-/

/-- The category of additive commutative monoids and monoid morphisms. -/
add_decl_doc AddCommMonCat

namespace CommMonCat

@[to_additive]
instance : BundledHom.ParentProjection CommMonoid.toMonoid :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommMonCat

attribute [to_additive] CommMonCat.largeCategory CommMonCat.concreteCategory

@[to_additive]
instance : CoeSort CommMonCat (Type _) :=
  Bundled.hasCoeToSort

#print CommMonCat.of /-
/-- Construct a bundled `CommMon` from the underlying type and typeclass. -/
@[to_additive]
def of (M : Type u) [CommMonoid M] : CommMonCat :=
  Bundled.of M
#align CommMon.of CommMonCat.of
#align AddCommMon.of AddCommMonCat.of
-/

/-- Construct a bundled `AddCommMon` from the underlying type and typeclass. -/
add_decl_doc AddCommMonCat.of

@[to_additive]
instance : Inhabited CommMonCat :=
  ⟨-- The default instance for `comm_monoid punit` is derived via `punit.comm_ring`,
        -- which breaks to_additive.
        @of
        PUnit <|
      @CommGroup.toCommMonoid _ PUnit.commGroup⟩

@[to_additive]
instance (M : CommMonCat) : CommMonoid M :=
  M.str

#print CommMonCat.coe_of /-
@[simp, to_additive]
theorem coe_of (R : Type u) [CommMonoid R] : (CommMonCat.of R : Type u) = R :=
  rfl
#align CommMon.coe_of CommMonCat.coe_of
#align AddCommMon.coe_of AddCommMonCat.coe_of
-/

#print CommMonCat.hasForgetToMonCat /-
@[to_additive has_forget_to_AddMon]
instance hasForgetToMonCat : HasForget₂ CommMonCat MonCat :=
  BundledHom.forget₂ _ _
#align CommMon.has_forget_to_Mon CommMonCat.hasForgetToMonCat
#align AddCommMon.has_forget_to_AddMon AddCommMonCat.hasForgetToAddMonCat
-/

@[to_additive]
instance : Coe CommMonCat.{u} MonCat.{u} where coe := (forget₂ CommMonCat MonCat).obj

end CommMonCat

-- We verify that the coercions of morphisms to functions work correctly:
example {R S : MonCat} (f : R ⟶ S) : (R : Type) → (S : Type) :=
  f

example {R S : CommMonCat} (f : R ⟶ S) : (R : Type) → (S : Type) :=
  f

-- We verify that when constructing a morphism in `CommMon`,
-- when we construct the `to_fun` field, the types are presented as `↥R`,
-- rather than `R.α` or (as we used to have) `↥(bundled.map comm_monoid.to_monoid R)`.
example (R : CommMonCat.{u}) : R ⟶ R :=
  { toFun := fun x => by
      match_target(R : Type u)
      match_hyp x : (R : Type u)
      exact x * x
    map_one' := by simp
    map_mul' := fun x y => by
      rw [mul_assoc x y (x * y), ← mul_assoc y x y, mul_comm y x, mul_assoc, mul_assoc] }

variable {X Y : Type u}

section

variable [Monoid X] [Monoid Y]

/- warning: mul_equiv.to_Mon_iso -> MulEquiv.toMonCatIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Monoid.{u1} X] [_inst_2 : Monoid.{u1} Y], (MulEquiv.{u1, u1} X Y (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X _inst_1)) (MulOneClass.toHasMul.{u1} Y (Monoid.toMulOneClass.{u1} Y _inst_2))) -> (CategoryTheory.Iso.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1} (MonCat.of.{u1} X _inst_1) (MonCat.of.{u1} Y _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Monoid.{u1} X] [_inst_2 : Monoid.{u1} Y], (MulEquiv.{u1, u1} X Y (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X _inst_1)) (MulOneClass.toMul.{u1} Y (Monoid.toMulOneClass.{u1} Y _inst_2))) -> (CategoryTheory.Iso.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1} (MonCat.of.{u1} X _inst_1) (MonCat.of.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_Mon_iso MulEquiv.toMonCatIsoₓ'. -/
/-- Build an isomorphism in the category `Mon` from a `mul_equiv` between `monoid`s. -/
@[to_additive AddEquiv.toAddMonCatIso
      "Build an isomorphism in the category `AddMon` from\nan `add_equiv` between `add_monoid`s.",
  simps]
def MulEquiv.toMonCatIso (e : X ≃* Y) : MonCat.of X ≅ MonCat.of Y
    where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
#align mul_equiv.to_Mon_iso MulEquiv.toMonCatIso
#align add_equiv.to_AddMon_iso AddEquiv.toAddMonCatIso

end

section

variable [CommMonoid X] [CommMonoid Y]

/- warning: mul_equiv.to_CommMon_iso -> MulEquiv.toCommMonCatIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : CommMonoid.{u1} X] [_inst_2 : CommMonoid.{u1} Y], (MulEquiv.{u1, u1} X Y (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X (CommMonoid.toMonoid.{u1} X _inst_1))) (MulOneClass.toHasMul.{u1} Y (Monoid.toMulOneClass.{u1} Y (CommMonoid.toMonoid.{u1} Y _inst_2)))) -> (CategoryTheory.Iso.{u1, succ u1} CommMonCat.{u1} CommMonCat.largeCategory.{u1} (CommMonCat.of.{u1} X _inst_1) (CommMonCat.of.{u1} Y _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : CommMonoid.{u1} X] [_inst_2 : CommMonoid.{u1} Y], (MulEquiv.{u1, u1} X Y (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X (CommMonoid.toMonoid.{u1} X _inst_1))) (MulOneClass.toMul.{u1} Y (Monoid.toMulOneClass.{u1} Y (CommMonoid.toMonoid.{u1} Y _inst_2)))) -> (CategoryTheory.Iso.{u1, succ u1} CommMonCat.{u1} CommMonCat.largeCategory.{u1} (CommMonCat.of.{u1} X _inst_1) (CommMonCat.of.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_CommMon_iso MulEquiv.toCommMonCatIsoₓ'. -/
/-- Build an isomorphism in the category `CommMon` from a `mul_equiv` between `comm_monoid`s. -/
@[to_additive AddEquiv.toAddCommMonCatIso
      "Build an isomorphism in the category `AddCommMon`\nfrom an `add_equiv` between `add_comm_monoid`s.",
  simps]
def MulEquiv.toCommMonCatIso (e : X ≃* Y) : CommMonCat.of X ≅ CommMonCat.of Y
    where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
#align mul_equiv.to_CommMon_iso MulEquiv.toCommMonCatIso
#align add_equiv.to_AddCommMon_iso AddEquiv.toAddCommMonCatIso

end

namespace CategoryTheory.Iso

/- warning: category_theory.iso.Mon_iso_to_mul_equiv -> CategoryTheory.Iso.monCatIsoToMulEquiv is a dubious translation:
lean 3 declaration is
  forall {X : MonCat.{u1}} {Y : MonCat.{u1}}, (CategoryTheory.Iso.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1} X Y) -> (MulEquiv.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.hasCoeToSort.{u1} X) (coeSort.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.hasCoeToSort.{u1} Y) (MulOneClass.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.hasCoeToSort.{u1} X) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.hasCoeToSort.{u1} X) (MonCat.monoid.{u1} X))) (MulOneClass.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.hasCoeToSort.{u1} Y) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.hasCoeToSort.{u1} Y) (MonCat.monoid.{u1} Y))))
but is expected to have type
  forall {X : MonCat.{u1}} {Y : MonCat.{u1}}, (CategoryTheory.Iso.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1} X Y) -> (MulEquiv.{u1, u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.instCoeSortMonCatType.{u1} X) (CoeSort.coe.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.instCoeSortMonCatType.{u1} Y) (MulOneClass.toMul.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.instCoeSortMonCatType.{u1} X) (Monoid.toMulOneClass.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.instCoeSortMonCatType.{u1} X) (MonCat.instMonoidCoeMonCatTypeInstCoeSortMonCatType.{u1} X))) (MulOneClass.toMul.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.instCoeSortMonCatType.{u1} Y) (Monoid.toMulOneClass.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} MonCat.{u1} Type.{u1} MonCat.instCoeSortMonCatType.{u1} Y) (MonCat.instMonoidCoeMonCatTypeInstCoeSortMonCatType.{u1} Y))))
Case conversion may be inaccurate. Consider using '#align category_theory.iso.Mon_iso_to_mul_equiv CategoryTheory.Iso.monCatIsoToMulEquivₓ'. -/
/-- Build a `mul_equiv` from an isomorphism in the category `Mon`. -/
@[to_additive AddMon_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism in the category\n`AddMon`."]
def monCatIsoToMulEquiv {X Y : MonCat} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.Mon_iso_to_mul_equiv CategoryTheory.Iso.monCatIsoToMulEquiv
#align category_theory.iso.AddMon_iso_to_add_equiv CategoryTheory.Iso.addMonCatIsoToAddEquiv

/- warning: category_theory.iso.CommMon_iso_to_mul_equiv -> CategoryTheory.Iso.commMonCatIsoToMulEquiv is a dubious translation:
lean 3 declaration is
  forall {X : CommMonCat.{u1}} {Y : CommMonCat.{u1}}, (CategoryTheory.Iso.{u1, succ u1} CommMonCat.{u1} CommMonCat.largeCategory.{u1} X Y) -> (MulEquiv.{u1, u1} (coeSort.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.hasCoeToSort.{u1} X) (coeSort.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.hasCoeToSort.{u1} Y) (MulOneClass.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.hasCoeToSort.{u1} X) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.hasCoeToSort.{u1} X) (CommMonoid.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.hasCoeToSort.{u1} X) (CommMonCat.commMonoid.{u1} X)))) (MulOneClass.toHasMul.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.hasCoeToSort.{u1} Y) (Monoid.toMulOneClass.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.hasCoeToSort.{u1} Y) (CommMonoid.toMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.hasCoeToSort.{u1} Y) (CommMonCat.commMonoid.{u1} Y)))))
but is expected to have type
  forall {X : CommMonCat.{u1}} {Y : CommMonCat.{u1}}, (CategoryTheory.Iso.{u1, succ u1} CommMonCat.{u1} CommMonCat.largeCategory.{u1} X Y) -> (MulEquiv.{u1, u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.instCoeSortCommMonCatType.{u1} X) (CoeSort.coe.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.instCoeSortCommMonCatType.{u1} Y) (MulOneClass.toMul.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.instCoeSortCommMonCatType.{u1} X) (Monoid.toMulOneClass.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.instCoeSortCommMonCatType.{u1} X) (CommMonoid.toMonoid.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.instCoeSortCommMonCatType.{u1} X) (CommMonCat.instCommMonoidCoeCommMonCatTypeInstCoeSortCommMonCatType.{u1} X)))) (MulOneClass.toMul.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.instCoeSortCommMonCatType.{u1} Y) (Monoid.toMulOneClass.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.instCoeSortCommMonCatType.{u1} Y) (CommMonoid.toMonoid.{u1} (CoeSort.coe.{succ (succ u1), succ (succ u1)} CommMonCat.{u1} Type.{u1} CommMonCat.instCoeSortCommMonCatType.{u1} Y) (CommMonCat.instCommMonoidCoeCommMonCatTypeInstCoeSortCommMonCatType.{u1} Y)))))
Case conversion may be inaccurate. Consider using '#align category_theory.iso.CommMon_iso_to_mul_equiv CategoryTheory.Iso.commMonCatIsoToMulEquivₓ'. -/
/-- Build a `mul_equiv` from an isomorphism in the category `CommMon`. -/
@[to_additive "Build an `add_equiv` from an isomorphism in the category\n`AddCommMon`."]
def commMonCatIsoToMulEquiv {X Y : CommMonCat} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.CommMon_iso_to_mul_equiv CategoryTheory.Iso.commMonCatIsoToMulEquiv
#align category_theory.iso.CommMon_iso_to_add_equiv CategoryTheory.Iso.commMonCatIsoToAddEquiv

end CategoryTheory.Iso

/- warning: mul_equiv_iso_Mon_iso -> mulEquivIsoMonCatIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Monoid.{u1} X] [_inst_2 : Monoid.{u1} Y], CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (MulEquiv.{u1, u1} X Y (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X _inst_1)) (MulOneClass.toHasMul.{u1} Y (Monoid.toMulOneClass.{u1} Y _inst_2))) (CategoryTheory.Iso.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1} (MonCat.of.{u1} X _inst_1) (MonCat.of.{u1} Y _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : Monoid.{u1} X] [_inst_2 : Monoid.{u1} Y], CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (MulEquiv.{u1, u1} X Y (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X _inst_1)) (MulOneClass.toMul.{u1} Y (Monoid.toMulOneClass.{u1} Y _inst_2))) (CategoryTheory.Iso.{u1, succ u1} MonCat.{u1} MonCat.largeCategory.{u1} (MonCat.of.{u1} X _inst_1) (MonCat.of.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align mul_equiv_iso_Mon_iso mulEquivIsoMonCatIsoₓ'. -/
/-- multiplicative equivalences between `monoid`s are the same as (isomorphic to) isomorphisms
in `Mon` -/
@[to_additive addEquivIsoAddMonCatIso
      "additive equivalences between `add_monoid`s are the same\nas (isomorphic to) isomorphisms in `AddMon`"]
def mulEquivIsoMonCatIso {X Y : Type u} [Monoid X] [Monoid Y] : X ≃* Y ≅ MonCat.of X ≅ MonCat.of Y
    where
  Hom e := e.toMonCatIso
  inv i := i.monCatIsoToMulEquiv
#align mul_equiv_iso_Mon_iso mulEquivIsoMonCatIso
#align add_equiv_iso_AddMon_iso addEquivIsoAddMonCatIso

/- warning: mul_equiv_iso_CommMon_iso -> mulEquivIsoCommMonCatIso is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : CommMonoid.{u1} X] [_inst_2 : CommMonoid.{u1} Y], CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (MulEquiv.{u1, u1} X Y (MulOneClass.toHasMul.{u1} X (Monoid.toMulOneClass.{u1} X (CommMonoid.toMonoid.{u1} X _inst_1))) (MulOneClass.toHasMul.{u1} Y (Monoid.toMulOneClass.{u1} Y (CommMonoid.toMonoid.{u1} Y _inst_2)))) (CategoryTheory.Iso.{u1, succ u1} CommMonCat.{u1} CommMonCat.largeCategory.{u1} (CommMonCat.of.{u1} X _inst_1) (CommMonCat.of.{u1} Y _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u1}} [_inst_1 : CommMonoid.{u1} X] [_inst_2 : CommMonoid.{u1} Y], CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (MulEquiv.{u1, u1} X Y (MulOneClass.toMul.{u1} X (Monoid.toMulOneClass.{u1} X (CommMonoid.toMonoid.{u1} X _inst_1))) (MulOneClass.toMul.{u1} Y (Monoid.toMulOneClass.{u1} Y (CommMonoid.toMonoid.{u1} Y _inst_2)))) (CategoryTheory.Iso.{u1, succ u1} CommMonCat.{u1} CommMonCat.largeCategory.{u1} (CommMonCat.of.{u1} X _inst_1) (CommMonCat.of.{u1} Y _inst_2))
Case conversion may be inaccurate. Consider using '#align mul_equiv_iso_CommMon_iso mulEquivIsoCommMonCatIsoₓ'. -/
/-- multiplicative equivalences between `comm_monoid`s are the same as (isomorphic to) isomorphisms
in `CommMon` -/
@[to_additive addEquivIsoAddCommMonCatIso
      "additive equivalences between `add_comm_monoid`s are\nthe same as (isomorphic to) isomorphisms in `AddCommMon`"]
def mulEquivIsoCommMonCatIso {X Y : Type u} [CommMonoid X] [CommMonoid Y] :
    X ≃* Y ≅ CommMonCat.of X ≅ CommMonCat.of Y
    where
  Hom e := e.toCommMonCatIso
  inv i := i.commMonCatIsoToMulEquiv
#align mul_equiv_iso_CommMon_iso mulEquivIsoCommMonCatIso
#align add_equiv_iso_AddCommMon_iso addEquivIsoAddCommMonCatIso

#print MonCat.forget_reflects_isos /-
@[to_additive]
instance MonCat.forget_reflects_isos : ReflectsIsomorphisms (forget MonCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget MonCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Mon_iso).1⟩
#align Mon.forget_reflects_isos MonCat.forget_reflects_isos
#align AddMon.forget_reflects_isos AddMonCat.forget_reflects_isos
-/

#print CommMonCat.forget_reflects_isos /-
@[to_additive]
instance CommMonCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommMonCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget CommMonCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommMon_iso).1⟩
#align CommMon.forget_reflects_isos CommMonCat.forget_reflects_isos
#align AddCommMon.forget_reflects_isos AddCommMonCat.forget_reflects_isos
-/

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/


example : ReflectsIsomorphisms (forget₂ CommMonCat MonCat) := by infer_instance

