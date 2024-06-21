/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Algebra.Category.MonCat.Basic
import CategoryTheory.Endomorphism

#align_import algebra.category.Group.basic from "leanprover-community/mathlib"@"cb3ceec8485239a61ed51d944cb9a95b68c6bafc"

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce the bundled categories:
* `Group`
* `AddGroup`
* `CommGroup`
* `AddCommGroup`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/


universe u v

open CategoryTheory

#print Grp /-
/-- The category of groups and group morphisms. -/
@[to_additive AddGrp]
def Grp : Type (u + 1) :=
  Bundled Group
#align Group Grp
#align AddGroup AddGrp
-/

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGrp

namespace Grp

@[to_additive]
instance : BundledHom.ParentProjection Group.toMonoid :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for Grp

attribute [to_additive] Grp.largeCategory Grp.concreteCategory

@[to_additive]
instance : CoeSort Grp (Type _) :=
  Bundled.hasCoeToSort

#print Grp.of /-
/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [Group X] : Grp :=
  Bundled.of X
#align Group.of Grp.of
#align AddGroup.of AddGrp.of
-/

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGrp.of

#print Grp.ofHom /-
/-- Typecheck a `monoid_hom` as a morphism in `Group`. -/
@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f
#align Group.of_hom Grp.ofHom
#align AddGroup.of_hom AddGrp.ofHom
-/

/-- Typecheck a `add_monoid_hom` as a morphism in `AddGroup`. -/
add_decl_doc AddGrp.ofHom

#print Grp.ofHom_apply /-
@[simp, to_additive]
theorem ofHom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) : ofHom f x = f x :=
  rfl
#align Group.of_hom_apply Grp.ofHom_apply
#align AddGroup.of_hom_apply AddGrp.ofHom_apply
-/

@[to_additive]
instance (G : Grp) : Group G :=
  G.str

#print Grp.coe_of /-
@[simp, to_additive]
theorem coe_of (R : Type u) [Group R] : (Grp.of R : Type u) = R :=
  rfl
#align Group.coe_of Grp.coe_of
#align AddGroup.coe_of AddGrp.coe_of
-/

@[to_additive]
instance : Inhabited Grp :=
  ⟨Grp.of PUnit⟩

#print Grp.ofUnique /-
@[to_additive]
instance ofUnique (G : Type _) [Group G] [i : Unique G] : Unique (Grp.of G) :=
  i
#align Group.of_unique Grp.ofUnique
#align AddGroup.of_unique AddGrp.ofUnique
-/

#print Grp.one_apply /-
@[simp, to_additive]
theorem one_apply (G H : Grp) (g : G) : (1 : G ⟶ H) g = 1 :=
  rfl
#align Group.one_apply Grp.one_apply
#align AddGroup.zero_apply AddGrp.zero_apply
-/

#print Grp.ext /-
@[ext, to_additive]
theorem ext (G H : Grp) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ := by ext1; apply w
#align Group.ext Grp.ext
#align AddGroup.ext AddGrp.ext
-/

#print Grp.hasForgetToMonCat /-
@[to_additive has_forget_to_AddMon]
instance hasForgetToMonCat : HasForget₂ Grp MonCat :=
  BundledHom.forget₂ _ _
#align Group.has_forget_to_Mon Grp.hasForgetToMonCat
#align AddGroup.has_forget_to_AddMon AddGrp.hasForgetToAddMonCat
-/

@[to_additive]
instance : Coe Grp.{u} MonCat.{u} where coe := (forget₂ Grp MonCat).obj

end Grp

#print CommGrp /-
/-- The category of commutative groups and group morphisms. -/
@[to_additive AddCommGrp]
def CommGrp : Type (u + 1) :=
  Bundled CommGroup
#align CommGroup CommGrp
#align AddCommGroup AddCommGrp
-/

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGrp

#print Ab /-
/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab :=
  AddCommGrp
#align Ab Ab
-/

namespace CommGrp

@[to_additive]
instance : BundledHom.ParentProjection CommGroup.toGroup :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommGrp

attribute [to_additive] CommGrp.largeCategory CommGrp.concreteCategory

@[to_additive]
instance : CoeSort CommGrp (Type _) :=
  Bundled.hasCoeToSort

#print CommGrp.of /-
/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive]
def of (G : Type u) [CommGroup G] : CommGrp :=
  Bundled.of G
#align CommGroup.of CommGrp.of
#align AddCommGroup.of AddCommGrp.of
-/

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGrp.of

#print CommGrp.ofHom /-
/-- Typecheck a `monoid_hom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f
#align CommGroup.of_hom CommGrp.ofHom
#align AddCommGroup.of_hom AddCommGrp.ofHom
-/

/-- Typecheck a `add_monoid_hom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGrp.ofHom

#print CommGrp.ofHom_apply /-
@[simp, to_additive]
theorem ofHom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    ofHom f x = f x :=
  rfl
#align CommGroup.of_hom_apply CommGrp.ofHom_apply
#align AddCommGroup.of_hom_apply AddCommGrp.ofHom_apply
-/

#print CommGrp.commGroupInstance /-
@[to_additive]
instance commGroupInstance (G : CommGrp) : CommGroup G :=
  G.str
#align CommGroup.comm_group_instance CommGrp.commGroupInstance
#align AddCommGroup.add_comm_group_instance AddCommGrp.addCommGroupInstance
-/

#print CommGrp.coe_of /-
@[simp, to_additive]
theorem coe_of (R : Type u) [CommGroup R] : (CommGrp.of R : Type u) = R :=
  rfl
#align CommGroup.coe_of CommGrp.coe_of
#align AddCommGroup.coe_of AddCommGrp.coe_of
-/

@[to_additive]
instance : Inhabited CommGrp :=
  ⟨CommGrp.of PUnit⟩

#print CommGrp.ofUnique /-
@[to_additive]
instance ofUnique (G : Type _) [CommGroup G] [i : Unique G] : Unique (CommGrp.of G) :=
  i
#align CommGroup.of_unique CommGrp.ofUnique
#align AddCommGroup.of_unique AddCommGrp.ofUnique
-/

#print CommGrp.one_apply /-
@[simp, to_additive]
theorem one_apply (G H : CommGrp) (g : G) : (1 : G ⟶ H) g = 1 :=
  rfl
#align CommGroup.one_apply CommGrp.one_apply
#align AddCommGroup.zero_apply AddCommGrp.zero_apply
-/

#print CommGrp.ext /-
@[ext, to_additive]
theorem ext (G H : CommGrp) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ := by ext1; apply w
#align CommGroup.ext CommGrp.ext
#align AddCommGroup.ext AddCommGrp.ext
-/

#print CommGrp.hasForgetToGroup /-
@[to_additive has_forget_to_AddGroup]
instance hasForgetToGroup : HasForget₂ CommGrp Grp :=
  BundledHom.forget₂ _ _
#align CommGroup.has_forget_to_Group CommGrp.hasForgetToGroup
#align AddCommGroup.has_forget_to_AddGroup AddCommGrp.hasForgetToAddGroup
-/

@[to_additive]
instance : Coe CommGrp.{u} Grp.{u} where coe := (forget₂ CommGrp Grp).obj

#print CommGrp.hasForgetToCommMonCat /-
@[to_additive has_forget_to_AddCommMon]
instance hasForgetToCommMonCat : HasForget₂ CommGrp CommMonCat :=
  InducedCategory.hasForget₂ fun G : CommGrp => CommMonCat.of G
#align CommGroup.has_forget_to_CommMon CommGrp.hasForgetToCommMonCat
#align AddCommGroup.has_forget_to_AddCommMon AddCommGrp.hasForgetToAddCommMonCat
-/

@[to_additive]
instance : Coe CommGrp.{u} CommMonCat.{u} where coe := (forget₂ CommGrp CommMonCat).obj

end CommGrp

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `monoid_hom.map_map` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
@[to_additive]
example {R S : CommGrp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

namespace AddCommGrp

#print AddCommGrp.asHom /-
-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ulift_instances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
def asHom {G : AddCommGrp.{0}} (g : G) : AddCommGrp.of ℤ ⟶ G :=
  zmultiplesHom G g
#align AddCommGroup.as_hom AddCommGrp.asHom
-/

#print AddCommGrp.asHom_apply /-
@[simp]
theorem asHom_apply {G : AddCommGrp.{0}} (g : G) (i : ℤ) : (asHom g) i = i • g :=
  rfl
#align AddCommGroup.as_hom_apply AddCommGrp.asHom_apply
-/

#print AddCommGrp.asHom_injective /-
theorem asHom_injective {G : AddCommGrp.{0}} : Function.Injective (@asHom G) := fun h k w => by
  convert congr_arg (fun k : AddCommGrp.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp
#align AddCommGroup.as_hom_injective AddCommGrp.asHom_injective
-/

#print AddCommGrp.int_hom_ext /-
@[ext]
theorem int_hom_ext {G : AddCommGrp.{0}} (f g : AddCommGrp.of ℤ ⟶ G) (w : f (1 : ℤ) = g (1 : ℤ)) :
    f = g :=
  AddMonoidHom.ext_int w
#align AddCommGroup.int_hom_ext AddCommGrp.int_hom_ext
-/

#print AddCommGrp.injective_of_mono /-
-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGrp.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h =>
  by
  have t0 : as_hom g₁ ≫ f = as_hom g₂ ≫ f := by
    ext
    simpa [as_hom_apply] using h
  have t1 : as_hom g₁ = as_hom g₂ := (cancel_mono _).1 t0
  apply as_hom_injective t1
#align AddCommGroup.injective_of_mono AddCommGrp.injective_of_mono
-/

end AddCommGrp

#print MulEquiv.toGrpIso /-
/-- Build an isomorphism in the category `Group` from a `mul_equiv` between `group`s. -/
@[to_additive AddEquiv.toAddGrpIso, simps]
def MulEquiv.toGrpIso {X Y : Grp} (e : X ≃* Y) : X ≅ Y
    where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
#align mul_equiv.to_Group_iso MulEquiv.toGrpIso
#align add_equiv.to_AddGroup_iso AddEquiv.toAddGrpIso
-/

/-- Build an isomorphism in the category `AddGroup` from an `add_equiv` between `add_group`s. -/
add_decl_doc AddEquiv.toAddGrpIso

#print MulEquiv.toCommGrpIso /-
/-- Build an isomorphism in the category `CommGroup` from a `mul_equiv` between `comm_group`s. -/
@[to_additive AddEquiv.toAddCommGrpIso, simps]
def MulEquiv.toCommGrpIso {X Y : CommGrp} (e : X ≃* Y) : X ≅ Y
    where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
#align mul_equiv.to_CommGroup_iso MulEquiv.toCommGrpIso
#align add_equiv.to_AddCommGroup_iso AddEquiv.toAddCommGrpIso
-/

/-- Build an isomorphism in the category `AddCommGroup` from a `add_equiv` between
`add_comm_group`s. -/
add_decl_doc AddEquiv.toAddCommGrpIso

namespace CategoryTheory.Iso

#print CategoryTheory.Iso.groupIsoToMulEquiv /-
/-- Build a `mul_equiv` from an isomorphism in the category `Group`. -/
@[to_additive AddGroup_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism in the category\n`AddGroup`.",
  simps]
def groupIsoToMulEquiv {X Y : Grp} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.Group_iso_to_mul_equiv CategoryTheory.Iso.groupIsoToMulEquiv
#align category_theory.iso.AddGroup_iso_to_add_equiv CategoryTheory.Iso.addGroupIsoToAddEquiv
-/

#print CategoryTheory.Iso.commGroupIsoToMulEquiv /-
/-- Build a `mul_equiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive AddCommGroup_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism\nin the category `AddCommGroup`.",
  simps]
def commGroupIsoToMulEquiv {X Y : CommGrp} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.CommGroup_iso_to_mul_equiv CategoryTheory.Iso.commGroupIsoToMulEquiv
#align category_theory.iso.AddCommGroup_iso_to_add_equiv CategoryTheory.Iso.addCommGroupIsoToAddEquiv
-/

end CategoryTheory.Iso

#print mulEquivIsoGroupIso /-
/-- multiplicative equivalences between `group`s are the same as (isomorphic to) isomorphisms
in `Group` -/
@[to_additive addEquivIsoAddGroupIso
      "additive equivalences between `add_group`s are the same\nas (isomorphic to) isomorphisms in `AddGroup`"]
def mulEquivIsoGroupIso {X Y : Grp.{u}} : X ≃* Y ≅ X ≅ Y
    where
  Hom e := e.toGrpIso
  inv i := i.groupIsoToMulEquiv
#align mul_equiv_iso_Group_iso mulEquivIsoGroupIso
#align add_equiv_iso_AddGroup_iso addEquivIsoAddGroupIso
-/

#print mulEquivIsoCommGroupIso /-
/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
@[to_additive addEquivIsoAddCommGroupIso
      "additive equivalences between `add_comm_group`s are\nthe same as (isomorphic to) isomorphisms in `AddCommGroup`"]
def mulEquivIsoCommGroupIso {X Y : CommGrp.{u}} : X ≃* Y ≅ X ≅ Y
    where
  Hom e := e.toCommGrpIso
  inv i := i.commGroupIsoToMulEquiv
#align mul_equiv_iso_CommGroup_iso mulEquivIsoCommGroupIso
#align add_equiv_iso_AddCommGroup_iso addEquivIsoAddCommGroupIso
-/

namespace CategoryTheory.Aut

#print CategoryTheory.Aut.isoPerm /-
/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : Grp.of (Aut α) ≅ Grp.of (Equiv.Perm α)
    where
  Hom := ⟨fun g => g.toEquiv, by tidy, by tidy⟩
  inv := ⟨fun g => g.toIso, by tidy, by tidy⟩
#align category_theory.Aut.iso_perm CategoryTheory.Aut.isoPerm
-/

#print CategoryTheory.Aut.mulEquivPerm /-
/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv
#align category_theory.Aut.mul_equiv_perm CategoryTheory.Aut.mulEquivPerm
-/

end CategoryTheory.Aut

#print Grp.forget_reflects_isos /-
@[to_additive]
instance Grp.forget_reflects_isos : CategoryTheory.Functor.ReflectsIsomorphisms (forget Grp.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget Grp).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Group_iso).1⟩
#align Group.forget_reflects_isos Grp.forget_reflects_isos
#align AddGroup.forget_reflects_isos AddGrp.forget_reflects_isos
-/

#print CommGrp.forget_reflects_isos /-
@[to_additive]
instance CommGrp.forget_reflects_isos :
    CategoryTheory.Functor.ReflectsIsomorphisms (forget CommGrp.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget CommGrp).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommGroup_iso).1⟩
#align CommGroup.forget_reflects_isos CommGrp.forget_reflects_isos
#align AddCommGroup.forget_reflects_isos AddCommGrp.forget_reflects_isos
-/

