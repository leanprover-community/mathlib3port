/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# Categorical (co)products

This file defines (co)products as special cases of (co)limits.

A product is the categorical generalization of the object `Π i, f i` where `f : ι → C`. It is a
limit cone over the diagram formed by `f`, implemented by converting `f` into a functor
`discrete ι ⥤ C`.

A coproduct is the dual concept.

## Main definitions

* a `fan` is a cone over a discrete category
* `fan.mk` constructs a fan from an indexed collection of maps
* a `pi` is a `limit (discrete.functor f)`

Each of these has a dual.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/


noncomputable section

universe w v u u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {β : Type w}

variable {C : Type u} [Category.{v} C]

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
-- We don't need an analogue of `pair` (for binary products), `parallel_pair` (for equalizers),
-- or `(co)span`, since we already have `discrete.functor`.
abbrev Fan (f : β → C) :=
  Cone (Discrete.functor f)

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
abbrev Cofan (f : β → C) :=
  Cocone (Discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps]
def Fan.mk {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : Fan f where
  x := P
  π := { app := p }

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps]
def Cofan.mk {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) : Cofan f where
  x := P
  ι := { app := p }

/-- An abbreviation for `has_limit (discrete.functor f)`. -/
abbrev HasProduct (f : β → C) :=
  HasLimit (Discrete.functor f)

/-- An abbreviation for `has_colimit (discrete.functor f)`. -/
abbrev HasCoproduct (f : β → C) :=
  HasColimit (Discrete.functor f)

section

variable (C)

/-- An abbreviation for `has_limits_of_shape (discrete f)`. -/
abbrev HasProductsOfShape (β : Type v) :=
  HasLimitsOfShape.{v} (Discrete β)

/-- An abbreviation for `has_colimits_of_shape (discrete f)`. -/
abbrev HasCoproductsOfShape (β : Type v) :=
  HasColimitsOfShape.{v} (Discrete β)

end

/-- `pi_obj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (discrete.functor f)`,
so for most facts about `pi_obj f`, you will just use general facts about limits.) -/
abbrev piObj (f : β → C) [HasProduct f] :=
  limit (Discrete.functor f)

/-- `sigma_obj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (discrete.functor f)`,
so for most facts about `sigma_obj f`, you will just use general facts about colimits.) -/
abbrev sigmaObj (f : β → C) [HasCoproduct f] :=
  colimit (Discrete.functor f)

-- mathport name: «expr∏ »
notation "∏ " f:20 => piObj f

-- mathport name: «expr∐ »
notation "∐ " f:20 => sigmaObj f

/-- The `b`-th projection from the pi object over `f` has the form `∏ f ⟶ f b`. -/
abbrev Pi.π (f : β → C) [HasProduct f] (b : β) : ∏ f ⟶ f b :=
  limit.π (Discrete.functor f) b

/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
abbrev Sigma.ι (f : β → C) [HasCoproduct f] (b : β) : f b ⟶ ∐ f :=
  colimit.ι (Discrete.functor f) b

/-- The fan constructed of the projections from the product is limiting. -/
def productIsProduct (f : β → C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f)) :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f))
    (Cones.ext (Iso.refl _)
      (by
        tidy))

/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
def coproductIsCoproduct (f : β → C) [HasCoproduct f] : IsColimit (Cofan.mk _ (Sigma.ι f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f))
    (Cocones.ext (Iso.refl _)
      (by
        tidy))

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ f`. -/
abbrev Pi.lift {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ∏ f :=
  limit.lift _ (Fan.mk P p)

/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
abbrev Sigma.desc {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ∐ f ⟶ P :=
  colimit.desc _ (Cofan.mk P p)

/-- Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
abbrev Pi.map {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) : ∏ f ⟶ ∏ g :=
  limMap (Discrete.natTrans p)

/-- Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbrev Pi.mapIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∏ f ≅ ∏ g :=
  lim.mapIso (Discrete.natIso p)

/-- Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
abbrev Sigma.map {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) : ∐ f ⟶ ∐ g :=
  colimMap (Discrete.natTrans p)

/-- Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbrev Sigma.mapIso {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∐ f ≅ ∐ g :=
  colim.mapIso (Discrete.natIso p)

section Comparison

variable {D : Type u₂} [Category.{v} D] (G : C ⥤ D)

variable (f : β → C)

/-- The comparison morphism for the product of `f`. This is an iso iff `G` preserves the product
of `f`, see `preserves_product.of_iso_comparison`. -/
def piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] : G.obj (∏ f) ⟶ ∏ fun b => G.obj (f b) :=
  Pi.lift fun b => G.map (Pi.π f b)

@[simp, reassoc]
theorem pi_comparison_comp_π [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β) :
    piComparison G f ≫ Pi.π _ b = G.map (Pi.π f b) :=
  limit.lift_π _ b

@[simp, reassoc]
theorem map_lift_pi_comparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C) (g : ∀ j, P ⟶ f j) :
    G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fun j => G.map (g j) := by
  ext
  simp [← G.map_comp]

/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `preserves_coproduct.of_iso_comparison`. -/
def sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] : (∐ fun b => G.obj (f b)) ⟶ G.obj (∐ f) :=
  Sigma.desc fun b => G.map (Sigma.ι f b)

@[simp, reassoc]
theorem ι_comp_sigma_comparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β) :
    Sigma.ι _ b ≫ sigmaComparison G f = G.map (Sigma.ι f b) :=
  colimit.ι_desc _ b

@[simp, reassoc]
theorem sigma_comparison_map_desc [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C) (g : ∀ j, f j ⟶ P) :
    sigmaComparison G f ≫ G.map (Sigma.desc g) = Sigma.desc fun j => G.map (g j) := by
  ext
  simp [← G.map_comp]

end Comparison

variable (C)

/-- An abbreviation for `Π J, has_limits_of_shape (discrete J) C` -/
abbrev HasProducts :=
  ∀ J : Type v, HasLimitsOfShape (Discrete J) C

/-- An abbreviation for `Π J, has_colimits_of_shape (discrete J) C` -/
abbrev HasCoproducts :=
  ∀ J : Type v, HasColimitsOfShape (Discrete J) C

end CategoryTheory.Limits

