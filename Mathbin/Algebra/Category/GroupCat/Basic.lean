/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.category.Group.basic
! leanprover-community/mathlib commit 9830a300340708eaa85d477c3fb96dd25f9468a5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.MonCat.Basic
import Mathbin.CategoryTheory.Endomorphism

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

We introduce the bundled categories:
* `Group`
* `AddGroup`
* `CommGroup`
* `AddCommGroup`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/


universe u v

open CategoryTheory

/-- The category of groups and group morphisms. -/
@[to_additive AddGroupCat]
def GroupCat : Type (u + 1) :=
  Bundled Group
#align Group GroupCat

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGroupCat

namespace GroupCat

@[to_additive]
instance : BundledHom.ParentProjection Group.toMonoid :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for GroupCat

attribute [to_additive] GroupCat.largeCategory GroupCat.concreteCategory

@[to_additive]
instance : CoeSort GroupCat (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [Group X] : GroupCat :=
  Bundled.of X
#align Group.of GroupCat.of

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGroupCat.of

/-- Typecheck a `monoid_hom` as a morphism in `Group`. -/
@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f
#align Group.of_hom GroupCat.ofHom

/-- Typecheck a `add_monoid_hom` as a morphism in `AddGroup`. -/
add_decl_doc AddGroupCat.ofHom

@[simp, to_additive]
theorem of_hom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) : ofHom f x = f x :=
  rfl
#align Group.of_hom_apply GroupCat.of_hom_apply

@[to_additive]
instance (G : GroupCat) : Group G :=
  G.str

@[simp, to_additive]
theorem coe_of (R : Type u) [Group R] : (GroupCat.of R : Type u) = R :=
  rfl
#align Group.coe_of GroupCat.coe_of

@[to_additive]
instance : Inhabited GroupCat :=
  ⟨GroupCat.of PUnit⟩

@[to_additive]
instance ofUnique (G : Type _) [Group G] [i : Unique G] : Unique (GroupCat.of G) :=
  i
#align Group.of_unique GroupCat.ofUnique

@[simp, to_additive]
theorem one_apply (G H : GroupCat) (g : G) : (1 : G ⟶ H) g = 1 :=
  rfl
#align Group.one_apply GroupCat.one_apply

@[ext, to_additive]
theorem ext (G H : GroupCat) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
  by
  ext1
  apply w
#align Group.ext GroupCat.ext

@[to_additive has_forget_to_AddMon]
instance hasForgetToMon : HasForget₂ GroupCat MonCat :=
  BundledHom.forget₂ _ _
#align Group.has_forget_to_Mon GroupCat.hasForgetToMon

@[to_additive]
instance : Coe GroupCat.{u} MonCat.{u} where coe := (forget₂ GroupCat MonCat).obj

end GroupCat

/-- The category of commutative groups and group morphisms. -/
@[to_additive AddCommGroupCat]
def CommGroupCat : Type (u + 1) :=
  Bundled CommGroup
#align CommGroup CommGroupCat

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGroupCat

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev AbCat :=
  AddCommGroupCat
#align Ab AbCat

namespace CommGroupCat

@[to_additive]
instance : BundledHom.ParentProjection CommGroup.toGroup :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommGroupCat

attribute [to_additive] CommGroupCat.largeCategory CommGroupCat.concreteCategory

@[to_additive]
instance : CoeSort CommGroupCat (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive]
def of (G : Type u) [CommGroup G] : CommGroupCat :=
  Bundled.of G
#align CommGroup.of CommGroupCat.of

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGroupCat.of

/-- Typecheck a `monoid_hom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f
#align CommGroup.of_hom CommGroupCat.ofHom

/-- Typecheck a `add_monoid_hom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGroupCat.ofHom

@[simp, to_additive]
theorem of_hom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    ofHom f x = f x :=
  rfl
#align CommGroup.of_hom_apply CommGroupCat.of_hom_apply

@[to_additive]
instance commGroupInstance (G : CommGroupCat) : CommGroup G :=
  G.str
#align CommGroup.comm_group_instance CommGroupCat.commGroupInstance

@[simp, to_additive]
theorem coe_of (R : Type u) [CommGroup R] : (CommGroupCat.of R : Type u) = R :=
  rfl
#align CommGroup.coe_of CommGroupCat.coe_of

@[to_additive]
instance : Inhabited CommGroupCat :=
  ⟨CommGroupCat.of PUnit⟩

@[to_additive]
instance ofUnique (G : Type _) [CommGroup G] [i : Unique G] : Unique (CommGroupCat.of G) :=
  i
#align CommGroup.of_unique CommGroupCat.ofUnique

@[simp, to_additive]
theorem one_apply (G H : CommGroupCat) (g : G) : (1 : G ⟶ H) g = 1 :=
  rfl
#align CommGroup.one_apply CommGroupCat.one_apply

@[ext, to_additive]
theorem ext (G H : CommGroupCat) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
  by
  ext1
  apply w
#align CommGroup.ext CommGroupCat.ext

@[to_additive has_forget_to_AddGroup]
instance hasForgetToGroup : HasForget₂ CommGroupCat GroupCat :=
  BundledHom.forget₂ _ _
#align CommGroup.has_forget_to_Group CommGroupCat.hasForgetToGroup

@[to_additive]
instance : Coe CommGroupCat.{u} GroupCat.{u} where coe := (forget₂ CommGroupCat GroupCat).obj

@[to_additive has_forget_to_AddCommMon]
instance hasForgetToCommMon : HasForget₂ CommGroupCat CommMonCat :=
  InducedCategory.hasForget₂ fun G : CommGroupCat => CommMonCat.of G
#align CommGroup.has_forget_to_CommMon CommGroupCat.hasForgetToCommMon

@[to_additive]
instance : Coe CommGroupCat.{u} CommMonCat.{u} where coe := (forget₂ CommGroupCat CommMonCat).obj

end CommGroupCat

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `monoid_hom.map_map` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
@[to_additive]
example {R S : CommGroupCat} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

namespace AddCommGroupCat

-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ulift_instances.lean` file
/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
def asHom {G : AddCommGroupCat.{0}} (g : G) : AddCommGroupCat.of ℤ ⟶ G :=
  zmultiplesHom G g
#align AddCommGroup.as_hom AddCommGroupCat.asHom

@[simp]
theorem as_hom_apply {G : AddCommGroupCat.{0}} (g : G) (i : ℤ) : (asHom g) i = i • g :=
  rfl
#align AddCommGroup.as_hom_apply AddCommGroupCat.as_hom_apply

theorem as_hom_injective {G : AddCommGroupCat.{0}} : Function.Injective (@asHom G) := fun h k w =>
  by convert congr_arg (fun k : AddCommGroupCat.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp
#align AddCommGroup.as_hom_injective AddCommGroupCat.as_hom_injective

@[ext]
theorem int_hom_ext {G : AddCommGroupCat.{0}} (f g : AddCommGroupCat.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  AddMonoidHom.ext_int w
#align AddCommGroup.int_hom_ext AddCommGroupCat.int_hom_ext

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGroupCat.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h =>
  by
  have t0 : as_hom g₁ ≫ f = as_hom g₂ ≫ f := by
    ext
    simpa [as_hom_apply] using h
  have t1 : as_hom g₁ = as_hom g₂ := (cancel_mono _).1 t0
  apply as_hom_injective t1
#align AddCommGroup.injective_of_mono AddCommGroupCat.injective_of_mono

end AddCommGroupCat

/-- Build an isomorphism in the category `Group` from a `mul_equiv` between `group`s. -/
@[to_additive AddEquiv.toAddGroupIso, simps]
def MulEquiv.toGroupIso {X Y : GroupCat} (e : X ≃* Y) : X ≅ Y
    where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
#align mul_equiv.to_Group_iso MulEquiv.toGroupIso

/-- Build an isomorphism in the category `AddGroup` from an `add_equiv` between `add_group`s. -/
add_decl_doc AddEquiv.toAddGroupIso

/-- Build an isomorphism in the category `CommGroup` from a `mul_equiv` between `comm_group`s. -/
@[to_additive AddEquiv.toAddCommGroupIso, simps]
def MulEquiv.toCommGroupIso {X Y : CommGroupCat} (e : X ≃* Y) : X ≅ Y
    where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom
#align mul_equiv.to_CommGroup_iso MulEquiv.toCommGroupIso

/-- Build an isomorphism in the category `AddCommGroup` from a `add_equiv` between
`add_comm_group`s. -/
add_decl_doc AddEquiv.toAddCommGroupIso

namespace CategoryTheory.Iso

/-- Build a `mul_equiv` from an isomorphism in the category `Group`. -/
@[to_additive AddGroup_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism in the category\n`AddGroup`.",
  simps]
def groupIsoToMulEquiv {X Y : GroupCat} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.Group_iso_to_mul_equiv CategoryTheory.Iso.groupIsoToMulEquiv

/-- Build a `mul_equiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive AddCommGroup_iso_to_add_equiv
      "Build an `add_equiv` from an isomorphism\nin the category `AddCommGroup`.",
  simps]
def commGroupIsoToMulEquiv {X Y : CommGroupCat} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id
#align category_theory.iso.CommGroup_iso_to_mul_equiv CategoryTheory.Iso.commGroupIsoToMulEquiv

end CategoryTheory.Iso

/-- multiplicative equivalences between `group`s are the same as (isomorphic to) isomorphisms
in `Group` -/
@[to_additive addEquivIsoAddGroupIso
      "additive equivalences between `add_group`s are the same\nas (isomorphic to) isomorphisms in `AddGroup`"]
def mulEquivIsoGroupIso {X Y : GroupCat.{u}} : X ≃* Y ≅ X ≅ Y
    where
  Hom e := e.toGroupIso
  inv i := i.groupIsoToMulEquiv
#align mul_equiv_iso_Group_iso mulEquivIsoGroupIso

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
@[to_additive addEquivIsoAddCommGroupIso
      "additive equivalences between `add_comm_group`s are\nthe same as (isomorphic to) isomorphisms in `AddCommGroup`"]
def mulEquivIsoCommGroupIso {X Y : CommGroupCat.{u}} : X ≃* Y ≅ X ≅ Y
    where
  Hom e := e.toCommGroupIso
  inv i := i.commGroupIsoToMulEquiv
#align mul_equiv_iso_CommGroup_iso mulEquivIsoCommGroupIso

namespace CategoryTheory.AutCat

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : GroupCat.of (AutCat α) ≅ GroupCat.of (Equiv.Perm α)
    where
  Hom := ⟨fun g => g.toEquiv, by tidy, by tidy⟩
  inv := ⟨fun g => g.toIso, by tidy, by tidy⟩
#align category_theory.Aut.iso_perm CategoryTheory.AutCat.isoPerm

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : AutCat α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv
#align category_theory.Aut.mul_equiv_perm CategoryTheory.AutCat.mulEquivPerm

end CategoryTheory.AutCat

@[to_additive]
instance GroupCat.forget_reflects_isos : ReflectsIsomorphisms (forget GroupCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget GroupCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Group_iso).1⟩
#align Group.forget_reflects_isos GroupCat.forget_reflects_isos

@[to_additive]
instance CommGroupCat.forget_reflects_isos : ReflectsIsomorphisms (forget CommGroupCat.{u})
    where reflects X Y f _ := by
    skip
    let i := as_iso ((forget CommGroupCat).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommGroup_iso).1⟩
#align CommGroup.forget_reflects_isos CommGroupCat.forget_reflects_isos

