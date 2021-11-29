import Mathbin.Algebra.PemptyInstances 
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom 
import Mathbin.CategoryTheory.ReflectsIsomorphisms

/-!
# Category instances for has_mul, has_add, semigroup and add_semigroup

We introduce the bundled categories:
* `Magma`
* `AddMagma`
* `Semigroup`
* `AddSemigroup`
along with the relevant forgetful functors between them.

This closely follows `algebra.category.Mon.basic`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/


universe u v

open CategoryTheory

/-- The category of magmas and magma morphisms. -/
@[toAdditive AddMagma]
def Magma : Type (u + 1) :=
  bundled Mul

/-- The category of additive magmas and additive magma morphisms. -/
add_decl_doc AddMagma

namespace Magma

@[toAdditive]
instance bundled_hom : bundled_hom @MulHom :=
  ⟨@MulHom.toFun, @MulHom.id, @MulHom.comp, @MulHom.coe_inj⟩

-- error in Algebra.Category.Semigroup.Basic: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler large_category
attribute [derive #["[", expr large_category, ",", expr concrete_category, "]"]] Magma

attribute [toAdditive] Magma.largeCategory Magma.concreteCategory

@[toAdditive]
instance : CoeSort Magma (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Magma` from the underlying type and typeclass. -/
@[toAdditive]
def of (M : Type u) [Mul M] : Magma :=
  bundled.of M

/-- Construct a bundled `AddMagma` from the underlying type and typeclass. -/
add_decl_doc AddMagma.of

/-- Typecheck a `mul_hom` as a morphism in `Magma`. -/
@[toAdditive]
def of_hom {X Y : Type u} [Mul X] [Mul Y] (f : MulHom X Y) : of X ⟶ of Y :=
  f

/-- Typecheck a `add_hom` as a morphism in `AddMagma`. -/
add_decl_doc AddMagma.ofHom

@[toAdditive]
instance : Inhabited Magma :=
  ⟨Magma.of Pempty⟩

@[toAdditive]
instance (M : Magma) : Mul M :=
  M.str

@[simp, toAdditive]
theorem coe_of (R : Type u) [Mul R] : (Magma.of R : Type u) = R :=
  rfl

end Magma

/-- The category of semigroups and semigroup morphisms. -/
@[toAdditive AddSemigroupₓₓ]
def Semigroupₓₓ : Type (u + 1) :=
  bundled Semigroupₓ

/-- The category of additive semigroups and semigroup morphisms. -/
add_decl_doc AddSemigroupₓₓ

namespace Semigroupₓₓ

@[toAdditive]
instance : bundled_hom.parent_projection Semigroupₓ.toHasMul :=
  ⟨⟩

-- error in Algebra.Category.Semigroup.Basic: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler large_category
attribute [derive #["[", expr large_category, ",", expr concrete_category, "]"]] Semigroup

attribute [toAdditive] Semigroupₓₓ.largeCategory Semigroupₓₓ.concreteCategory

@[toAdditive]
instance : CoeSort Semigroupₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Semigroup` from the underlying type and typeclass. -/
@[toAdditive]
def of (M : Type u) [Semigroupₓ M] : Semigroupₓₓ :=
  bundled.of M

/-- Construct a bundled `AddSemigroup` from the underlying type and typeclass. -/
add_decl_doc AddSemigroupₓₓ.of

/-- Typecheck a `mul_hom` as a morphism in `Semigroup`. -/
@[toAdditive]
def of_hom {X Y : Type u} [Semigroupₓ X] [Semigroupₓ Y] (f : MulHom X Y) : of X ⟶ of Y :=
  f

/-- Typecheck a `add_hom` as a morphism in `AddSemigroup`. -/
add_decl_doc AddSemigroupₓₓ.ofHom

@[toAdditive]
instance : Inhabited Semigroupₓₓ :=
  ⟨Semigroupₓₓ.of Pempty⟩

@[toAdditive]
instance (M : Semigroupₓₓ) : Semigroupₓ M :=
  M.str

@[simp, toAdditive]
theorem coe_of (R : Type u) [Semigroupₓ R] : (Semigroupₓₓ.of R : Type u) = R :=
  rfl

@[toAdditive has_forget_to_AddMagma]
instance has_forget_to_Magma : has_forget₂ Semigroupₓₓ Magma :=
  bundled_hom.forget₂ _ _

end Semigroupₓₓ

variable {X Y : Type u}

section 

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `Magma` from a `mul_equiv` between `has_mul`s. -/
@[toAdditive AddEquiv.toAddMagmaIso
      "Build an isomorphism in the category `AddMagma` from\nan `add_equiv` between `has_add`s.",
  simps]
def MulEquiv.toMagmaIso (e : X ≃* Y) : Magma.of X ≅ Magma.of Y :=
  { Hom := e.to_mul_hom, inv := e.symm.to_mul_hom }

end 

section 

variable [Semigroupₓ X] [Semigroupₓ Y]

/-- Build an isomorphism in the category `Semigroup` from a `mul_equiv` between `semigroup`s. -/
@[toAdditive AddEquiv.toAddSemigroupIso
      "Build an isomorphism in the category\n`AddSemigroup` from an `add_equiv` between `add_semigroup`s.",
  simps]
def MulEquiv.toSemigroupIso (e : X ≃* Y) : Semigroupₓₓ.of X ≅ Semigroupₓₓ.of Y :=
  { Hom := e.to_mul_hom, inv := e.symm.to_mul_hom }

end 

namespace CategoryTheory.Iso

/-- Build a `mul_equiv` from an isomorphism in the category `Magma`. -/
@[toAdditive AddMagma_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category\n`AddMagma`."]
def Magma_iso_to_mul_equiv {X Y : Magma} (i : X ≅ Y) : X ≃* Y :=
  { toFun := i.hom, invFun := i.inv,
    left_inv :=
      by 
        rw [Function.LeftInverse]
        simp ,
    right_inv :=
      by 
        rw [Function.RightInverse]
        rw [Function.LeftInverse]
        simp ,
    map_mul' :=
      by 
        simp  }

/-- Build a `mul_equiv` from an isomorphism in the category `Semigroup`. -/
@[toAdditive "Build an `add_equiv` from an isomorphism in the category\n`AddSemigroup`."]
def Semigroup_iso_to_mul_equiv {X Y : Semigroupₓₓ} (i : X ≅ Y) : X ≃* Y :=
  { toFun := i.hom, invFun := i.inv,
    left_inv :=
      by 
        rw [Function.LeftInverse]
        simp ,
    right_inv :=
      by 
        rw [Function.RightInverse]
        rw [Function.LeftInverse]
        simp ,
    map_mul' :=
      by 
        simp  }

end CategoryTheory.Iso

/-- multiplicative equivalences between `has_mul`s are the same as (isomorphic to) isomorphisms
in `Magma` -/
@[toAdditive addEquivIsoAddMagmaIso
      "additive equivalences between `has_add`s are the same\nas (isomorphic to) isomorphisms in `AddMagma`"]
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] : X ≃* Y ≅ Magma.of X ≅ Magma.of Y :=
  { Hom := fun e => e.to_Magma_iso, inv := fun i => i.Magma_iso_to_mul_equiv }

/-- multiplicative equivalences between `semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[toAdditive addEquivIsoAddSemigroupIso
      "additive equivalences between `add_semigroup`s are\nthe same as (isomorphic to) isomorphisms in `AddSemigroup`"]
def mulEquivIsoSemigroupIso {X Y : Type u} [Semigroupₓ X] [Semigroupₓ Y] :
  X ≃* Y ≅ Semigroupₓₓ.of X ≅ Semigroupₓₓ.of Y :=
  { Hom := fun e => e.to_Semigroup_iso, inv := fun i => i.Semigroup_iso_to_mul_equiv }

@[toAdditive]
instance Magma.forget_reflects_isos : reflects_isomorphisms (forget Magma.{u}) :=
  { reflects :=
      fun X Y f _ =>
        by 
          skip 
          let i := as_iso ((forget Magma).map f)
          let e : X ≃* Y := { f, i.to_equiv with  }
          exact ⟨(is_iso.of_iso e.to_Magma_iso).1⟩ }

@[toAdditive]
instance Semigroupₓₓ.forget_reflects_isos : reflects_isomorphisms (forget Semigroupₓₓ.{u}) :=
  { reflects :=
      fun X Y f _ =>
        by 
          skip 
          let i := as_iso ((forget Semigroupₓₓ).map f)
          let e : X ≃* Y := { f, i.to_equiv with  }
          exact ⟨(is_iso.of_iso e.to_Semigroup_iso).1⟩ }

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/


example : reflects_isomorphisms (forget₂ Semigroupₓₓ Magma) :=
  by 
    infer_instance

