/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jakob von Raumer
-/
import Mathbin.Algebra.Group.Ext
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.Limits.Shapes.Kernels

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

We treat first the case of a general category with zero morphisms,
and subsequently the case of a preadditive category.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `binary_bicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `binary_bicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

In a preadditive category,
* any `binary_biproduct` satisfies `total : fst ≫ inl + snd ≫ inr = 𝟙 X`
* any `binary_product` is a `binary_biproduct`
* any `binary_coproduct` is a `binary_biproduct`

For biproducts indexed by a `fintype J`, a `bicone` again consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

In a preadditive category,
* any `biproduct` satisfies `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
* any `product` is a `biproduct`
* any `coproduct` is a `biproduct`

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.

## Implementation
Prior to #14046, `has_finite_biproducts` required a `decidable_eq` instance on the indexing type.
As this had no pay-off (everything about limits is non-constructive in mathlib), and occasional cost
(constructing decidability instances appropriate for constructions involving the indexing type),
we made everything classical.
-/


noncomputable section

universe w w' v u

open CategoryTheory

open CategoryTheory.Functor

open Classical

namespace CategoryTheory

namespace Limits

variable {J : Type w}

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A `c : bicone F` is:
* an object `c.X` and
* morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
@[nolint has_nonempty_instance]
structure Bicone (F : J → C) where
  x : C
  π : ∀ j, X ⟶ F j
  ι : ∀ j, F j ⟶ X
  ι_π : ∀ j j', ι j ≫ π j' = if h : j = j' then eqToHom (congr_arg F h) else 0 := by
    run_tac
      obviously

@[simp, reassoc]
theorem bicone_ι_π_self {F : J → C} (B : Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j) := by
  simpa using B.ι_π j j

@[simp, reassoc]
theorem bicone_ι_π_ne {F : J → C} (B : Bicone F) {j j' : J} (h : j ≠ j') : B.ι j ≫ B.π j' = 0 := by
  simpa [← h] using B.ι_π j j'

variable {F : J → C}

namespace Bicone

attribute [local tidy] tactic.discrete_cases

/-- Extract the cone from a bicone. -/
def toCone (B : Bicone F) : Cone (Discrete.functor F) where
  x := B.x
  π := { app := fun j => B.π j.as }

@[simp]
theorem to_cone_X (B : Bicone F) : B.toCone.x = B.x :=
  rfl

@[simp]
theorem to_cone_π_app (B : Bicone F) (j : Discrete J) : B.toCone.π.app j = B.π j.as :=
  rfl

theorem to_cone_π_app_mk (B : Bicone F) (j : J) : B.toCone.π.app ⟨j⟩ = B.π j :=
  rfl

/-- Extract the cocone from a bicone. -/
def toCocone (B : Bicone F) : Cocone (Discrete.functor F) where
  x := B.x
  ι := { app := fun j => B.ι j.as }

@[simp]
theorem to_cocone_X (B : Bicone F) : B.toCocone.x = B.x :=
  rfl

@[simp]
theorem to_cocone_ι_app (B : Bicone F) (j : Discrete J) : B.toCocone.ι.app j = B.ι j.as :=
  rfl

theorem to_cocone_ι_app_mk (B : Bicone F) (j : J) : B.toCocone.ι.app ⟨j⟩ = B.ι j :=
  rfl

/-- We can turn any limit cone over a discrete collection of objects into a bicone. -/
@[simps]
def ofLimitCone {f : J → C} {t : Cone (Discrete.functor f)} (ht : IsLimit t) : Bicone f where
  x := t.x
  π := fun j => t.π.app ⟨j⟩
  ι := fun j => ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0)
  ι_π := fun j j' => by
    simp

-- ./././Mathport/Syntax/Translate/Basic.lean:649:16: unsupported tactic `discrete_cases #[]
theorem ι_of_is_limit {f : J → C} {t : Bicone f} (ht : IsLimit t.toCone) (j : J) :
    t.ι j = ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    trace "./././Mathport/Syntax/Translate/Basic.lean:649:16: unsupported tactic `discrete_cases #[]"
    simp [← t.ι_π]

/-- We can turn any colimit cocone over a discrete collection of objects into a bicone. -/
@[simps]
def ofColimitCocone {f : J → C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t) : Bicone f where
  x := t.x
  π := fun j => ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0)
  ι := fun j => t.ι.app ⟨j⟩
  ι_π := fun j j' => by
    simp

-- ./././Mathport/Syntax/Translate/Basic.lean:649:16: unsupported tactic `discrete_cases #[]
theorem π_of_is_colimit {f : J → C} {t : Bicone f} (ht : IsColimit t.toCocone) (j : J) :
    t.π j = ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    trace "./././Mathport/Syntax/Translate/Basic.lean:649:16: unsupported tactic `discrete_cases #[]"
    simp [← t.ι_π]

/-- Structure witnessing that a bicone is both a limit cone and a colimit cocone. -/
@[nolint has_nonempty_instance]
structure IsBilimit {F : J → C} (B : Bicone F) where
  IsLimit : IsLimit B.toCone
  IsColimit : IsColimit B.toCocone

attribute [local ext] bicone.is_bilimit

instance subsingleton_is_bilimit {f : J → C} {c : Bicone f} : Subsingleton c.IsBilimit :=
  ⟨fun h h' => Bicone.IsBilimit.ext _ _ (Subsingleton.elimₓ _ _) (Subsingleton.elimₓ _ _)⟩

section Whisker

variable {K : Type w'}

/-- Whisker a bicone with an equivalence between the indexing types. -/
@[simps]
def whisker {f : J → C} (c : Bicone f) (g : K ≃ J) : Bicone (f ∘ g) where
  x := c.x
  π := fun k => c.π (g k)
  ι := fun k => c.ι (g k)
  ι_π := fun k k' => by
    simp only [← c.ι_π]
    split_ifs with h h' h' <;> simp [← Equivₓ.apply_eq_iff_eq g] at h h' <;> tauto

attribute [local tidy] tactic.discrete_cases

/-- Taking the cone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cone and postcomposing with a suitable isomorphism. -/
def whiskerToCone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCone ≅
      (Cones.postcompose (Discrete.functorComp f g).inv).obj (c.toCone.whisker (Discrete.functor (discrete.mk ∘ g))) :=
  Cones.ext (Iso.refl _)
    (by
      tidy)

/-- Taking the cocone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cocone and precomposing with a suitable isomorphism. -/
def whiskerToCocone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCocone ≅
      (Cocones.precompose (Discrete.functorComp f g).Hom).obj
        (c.toCocone.whisker (Discrete.functor (discrete.mk ∘ g))) :=
  Cocones.ext (Iso.refl _)
    (by
      tidy)

/-- Whiskering a bicone with an equivalence between types preserves being a bilimit bicone. -/
def whiskerIsBilimitIff {f : J → C} (c : Bicone f) (g : K ≃ J) : (c.whisker g).IsBilimit ≃ c.IsBilimit := by
  refine' equivOfSubsingletonOfSubsingleton (fun hc => ⟨_, _⟩) fun hc => ⟨_, _⟩
  · let this := is_limit.of_iso_limit hc.is_limit (bicone.whisker_to_cone c g)
    let this := (is_limit.postcompose_hom_equiv (discrete.functor_comp f g).symm _) this
    exact is_limit.of_whisker_equivalence (discrete.equivalence g) this
    
  · let this := is_colimit.of_iso_colimit hc.is_colimit (bicone.whisker_to_cocone c g)
    let this := (is_colimit.precompose_hom_equiv (discrete.functor_comp f g) _) this
    exact is_colimit.of_whisker_equivalence (discrete.equivalence g) this
    
  · apply is_limit.of_iso_limit _ (bicone.whisker_to_cone c g).symm
    apply (is_limit.postcompose_hom_equiv (discrete.functor_comp f g).symm _).symm _
    exact is_limit.whisker_equivalence hc.is_limit (discrete.equivalence g)
    
  · apply is_colimit.of_iso_colimit _ (bicone.whisker_to_cocone c g).symm
    apply (is_colimit.precompose_hom_equiv (discrete.functor_comp f g) _).symm _
    exact is_colimit.whisker_equivalence hc.is_colimit (discrete.equivalence g)
    

end Whisker

end Bicone

/-- A bicone over `F : J → C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_nonempty_instance]
structure LimitBicone (F : J → C) where
  Bicone : Bicone F
  IsBilimit : bicone.IsBilimit

/-- `has_biproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
class HasBiproduct (F : J → C) : Prop where mk' ::
  exists_biproduct : Nonempty (LimitBicone F)

theorem HasBiproduct.mk {F : J → C} (d : LimitBicone F) : HasBiproduct F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `biproduct_data F` from `has_biproduct F`. -/
def getBiproductData (F : J → C) [HasBiproduct F] : LimitBicone F :=
  Classical.choice HasBiproduct.exists_biproduct

/-- A bicone for `F` which is both a limit cone and a colimit cocone. -/
def Biproduct.bicone (F : J → C) [HasBiproduct F] : Bicone F :=
  (getBiproductData F).Bicone

/-- `biproduct.bicone F` is a bilimit bicone. -/
def Biproduct.isBilimit (F : J → C) [HasBiproduct F] : (Biproduct.bicone F).IsBilimit :=
  (getBiproductData F).IsBilimit

/-- `biproduct.bicone F` is a limit cone. -/
def Biproduct.isLimit (F : J → C) [HasBiproduct F] : IsLimit (Biproduct.bicone F).toCone :=
  (getBiproductData F).IsBilimit.IsLimit

/-- `biproduct.bicone F` is a colimit cocone. -/
def Biproduct.isColimit (F : J → C) [HasBiproduct F] : IsColimit (Biproduct.bicone F).toCocone :=
  (getBiproductData F).IsBilimit.IsColimit

instance (priority := 100) has_product_of_has_biproduct [HasBiproduct F] : HasLimit (Discrete.functor F) :=
  HasLimit.mk { Cone := (Biproduct.bicone F).toCone, IsLimit := Biproduct.isLimit F }

instance (priority := 100) has_coproduct_of_has_biproduct [HasBiproduct F] : HasColimit (Discrete.functor F) :=
  HasColimit.mk { Cocone := (Biproduct.bicone F).toCocone, IsColimit := Biproduct.isColimit F }

variable (J C)

/-- `C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`.
-/
class HasBiproductsOfShape : Prop where
  HasBiproduct : ∀ F : J → C, HasBiproduct F

attribute [instance] has_biproducts_of_shape.has_biproduct

/-- `has_finite_biproducts C` represents a choice of biproduct for every family of objects in `C`
indexed by a finite type. -/
class HasFiniteBiproducts : Prop where
  HasBiproductsOfShape : ∀ (J : Type) [Fintype J], HasBiproductsOfShape J C

attribute [instance] has_finite_biproducts.has_biproducts_of_shape

instance (priority := 100) has_finite_products_of_has_finite_biproducts [HasFiniteBiproducts C] :
    HasFiniteProducts C where out := fun J _ => ⟨fun F => has_limit_of_iso discrete.nat_iso_functor.symm⟩

instance (priority := 100) has_finite_coproducts_of_has_finite_biproducts [HasFiniteBiproducts C] :
    HasFiniteCoproducts C where out := fun J _ => ⟨fun F => has_colimit_of_iso discrete.nat_iso_functor⟩

variable {J C}

/-- The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproductIso (F : J → C) [HasBiproduct F] : Limits.piObj F ≅ Limits.sigmaObj F :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Biproduct.isLimit F)).trans <|
    IsColimit.coconePointUniqueUpToIso (Biproduct.isColimit F) (colimit.isColimit _)

end Limits

namespace Limits

variable {J : Type w}

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
   abbreviation for `limit (discrete.functor f)`, so for most facts about `biproduct f`, you will
   just use general facts about limits and colimits.) -/
abbrev biproduct (f : J → C) [HasBiproduct f] : C :=
  (Biproduct.bicone f).x

-- mathport name: «expr⨁ »
notation "⨁ " f:20 => biproduct f

/-- The projection onto a summand of a biproduct. -/
abbrev biproduct.π (f : J → C) [HasBiproduct f] (b : J) : ⨁ f ⟶ f b :=
  (Biproduct.bicone f).π b

@[simp]
theorem biproduct.bicone_π (f : J → C) [HasBiproduct f] (b : J) : (Biproduct.bicone f).π b = biproduct.π f b :=
  rfl

/-- The inclusion into a summand of a biproduct. -/
abbrev biproduct.ι (f : J → C) [HasBiproduct f] (b : J) : f b ⟶ ⨁ f :=
  (Biproduct.bicone f).ι b

@[simp]
theorem biproduct.bicone_ι (f : J → C) [HasBiproduct f] (b : J) : (Biproduct.bicone f).ι b = biproduct.ι f b :=
  rfl

/-- Note that as this lemma has a `if` in the statement, we include a `decidable_eq` argument.
This means you may not be able to `simp` using this lemma unless you `open_locale classical`. -/
@[reassoc]
theorem biproduct.ι_π [DecidableEq J] (f : J → C) [HasBiproduct f] (j j' : J) :
    biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eqToHom (congr_arg f h) else 0 := by
  convert (biproduct.bicone f).ι_π j j'

@[simp, reassoc]
theorem biproduct.ι_π_self (f : J → C) [HasBiproduct f] (j : J) : biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ := by
  simp [← biproduct.ι_π]

@[simp, reassoc]
theorem biproduct.ι_π_ne (f : J → C) [HasBiproduct f] {j j' : J} (h : j ≠ j') :
    biproduct.ι f j ≫ biproduct.π f j' = 0 := by
  simp [← biproduct.ι_π, ← h]

/-- Given a collection of maps into the summands, we obtain a map into the biproduct. -/
abbrev biproduct.lift {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ⨁ f :=
  (Biproduct.isLimit f).lift (Fan.mk P p)

/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
abbrev biproduct.desc {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ⨁ f ⟶ P :=
  (Biproduct.isColimit f).desc (Cofan.mk P p)

@[simp, reassoc]
theorem biproduct.lift_π {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, P ⟶ f b) (j : J) :
    biproduct.lift p ≫ biproduct.π f j = p j :=
  (Biproduct.isLimit f).fac _ ⟨j⟩

@[simp, reassoc]
theorem biproduct.ι_desc {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, f b ⟶ P) (j : J) :
    biproduct.ι f j ≫ biproduct.desc p = p j :=
  (Biproduct.isColimit f).fac _ ⟨j⟩

/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
abbrev biproduct.map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
  IsLimit.map (Biproduct.bicone f).toCone (Biproduct.isLimit g) (Discrete.natTrans fun j => p j.as)

/-- An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
abbrev biproduct.map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
  IsColimit.map (Biproduct.isColimit f) (Biproduct.bicone g).toCocone (Discrete.natTrans fun j => p j.as)

@[ext]
theorem biproduct.hom_ext {f : J → C} [HasBiproduct f] {Z : C} (g h : Z ⟶ ⨁ f)
    (w : ∀ j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
  (Biproduct.isLimit f).hom_ext fun j => w j.as

@[ext]
theorem biproduct.hom_ext' {f : J → C} [HasBiproduct f] {Z : C} (g h : ⨁ f ⟶ Z)
    (w : ∀ j, biproduct.ι f j ≫ g = biproduct.ι f j ≫ h) : g = h :=
  (Biproduct.isColimit f).hom_ext fun j => w j.as

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biproduct.isoProduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∏ f :=
  IsLimit.conePointUniqueUpToIso (Biproduct.isLimit f) (limit.isLimit _)

@[simp]
theorem biproduct.iso_product_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).Hom = Pi.lift (biproduct.π f) :=
  limit.hom_ext fun j => by
    simp [← biproduct.iso_product]

@[simp]
theorem biproduct.iso_product_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).inv = biproduct.lift (Pi.π f) :=
  (biproduct.hom_ext _ _) fun j => by
    simp [← iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biproduct.isoCoproduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∐ f :=
  IsColimit.coconePointUniqueUpToIso (Biproduct.isColimit f) (colimit.isColimit _)

@[simp]
theorem biproduct.iso_coproduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).inv = Sigma.desc (biproduct.ι f) :=
  colimit.hom_ext fun j => by
    simp [← biproduct.iso_coproduct]

@[simp]
theorem biproduct.iso_coproduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).Hom = biproduct.desc (Sigma.ι f) :=
  (biproduct.hom_ext' _ _) fun j => by
    simp [iso.eq_comp_inv]

theorem biproduct.map_eq_map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    biproduct.map p = biproduct.map' p := by
  ext j j'
  simp only [← discrete.nat_trans_app, ← limits.is_colimit.ι_map, ← limits.is_limit.map_π, ← category.assoc,
    bicone.to_cone_π_app_mk, biproduct.bicone_π, bicone.to_cocone_ι_app_mk, biproduct.bicone_ι]
  simp only [← biproduct.bicone_ι, ← biproduct.bicone_π, ← bicone.to_cocone_ι_app, ← bicone.to_cone_π_app]
  dsimp'
  rw [biproduct.ι_π_assoc, biproduct.ι_π]
  split_ifs
  · subst h
    rw [eq_to_hom_refl, category.id_comp]
    erw [category.comp_id]
    
  · simp
    

@[simp, reassoc]
theorem biproduct.map_π {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j) (j : J) :
    biproduct.map p ≫ biproduct.π g j = biproduct.π f j ≫ p j :=
  Limits.IsLimit.map_π _ _ _ (Discrete.mk j)

@[simp, reassoc]
theorem biproduct.ι_map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j) (j : J) :
    biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j := by
  rw [biproduct.map_eq_map']
  convert limits.is_colimit.ι_map _ _ _ (discrete.mk j) <;> rfl

@[simp, reassoc]
theorem biproduct.map_desc {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j) {P : C}
    (k : ∀ j, g j ⟶ P) : biproduct.map p ≫ biproduct.desc k = biproduct.desc fun j => p j ≫ k j := by
  ext
  simp

@[simp, reassoc]
theorem biproduct.lift_map {f g : J → C} [HasBiproduct f] [HasBiproduct g] {P : C} (k : ∀ j, P ⟶ f j)
    (p : ∀ j, f j ⟶ g j) : biproduct.lift k ≫ biproduct.map p = biproduct.lift fun j => k j ≫ p j := by
  ext
  simp

/-- Given a collection of isomorphisms between corresponding summands of a pair of biproducts
indexed by the same type, we obtain an isomorphism between the biproducts. -/
@[simps]
def biproduct.mapIso {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ≅ g b) : ⨁ f ≅ ⨁ g where
  Hom := biproduct.map fun b => (p b).Hom
  inv := biproduct.map fun b => (p b).inv

section πKernel

section

variable (f : J → C) [HasBiproduct f]

variable (p : J → Prop) [HasBiproduct (Subtype.restrictₓ p f)]

/-- The canonical morphism from the biproduct over a restricted index type to the biproduct of
the full index type. -/
def biproduct.fromSubtype : ⨁ Subtype.restrictₓ p f ⟶ ⨁ f :=
  biproduct.desc fun j => biproduct.ι _ _

/-- The canonical morphism from a biproduct to the biproduct over a restriction of its index
type. -/
def biproduct.toSubtype : ⨁ f ⟶ ⨁ Subtype.restrictₓ p f :=
  biproduct.lift fun j => biproduct.π _ _

@[simp, reassoc]
theorem biproduct.from_subtype_π [DecidablePred p] (j : J) :
    biproduct.fromSubtype f p ≫ biproduct.π f j = if h : p j then biproduct.π (Subtype.restrictₓ p f) ⟨j, h⟩ else 0 :=
  by
  ext i
  rw [biproduct.from_subtype, biproduct.ι_desc_assoc, biproduct.ι_π]
  by_cases' h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts[rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
    
  · rw [dif_neg h, dif_neg (show (i : J) ≠ j from fun h₂ => h (h₂ ▸ i.2)), comp_zero]
    

theorem biproduct.from_subtype_eq_lift [DecidablePred p] :
    biproduct.fromSubtype f p =
      biproduct.lift fun j => if h : p j then biproduct.π (Subtype.restrictₓ p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext _ _
    (by
      simp )

@[simp, reassoc]
theorem biproduct.from_subtype_π_subtype (j : Subtype p) :
    biproduct.fromSubtype f p ≫ biproduct.π f j = biproduct.π (Subtype.restrictₓ p f) j := by
  ext i
  rw [biproduct.from_subtype, biproduct.ι_desc_assoc, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts[rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[simp, reassoc]
theorem biproduct.to_subtype_π (j : Subtype p) :
    biproduct.toSubtype f p ≫ biproduct.π (Subtype.restrictₓ p f) j = biproduct.π f j :=
  biproduct.lift_π _ _

@[simp, reassoc]
theorem biproduct.ι_to_subtype [DecidablePred p] (j : J) :
    biproduct.ι f j ≫ biproduct.toSubtype f p = if h : p j then biproduct.ι (Subtype.restrictₓ p f) ⟨j, h⟩ else 0 := by
  ext i
  rw [biproduct.to_subtype, category.assoc, biproduct.lift_π, biproduct.ι_π]
  by_cases' h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts[rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
    
  · rw [dif_neg h, dif_neg (show j ≠ i from fun h₂ => h (h₂.symm ▸ i.2)), zero_comp]
    

theorem biproduct.to_subtype_eq_desc [DecidablePred p] :
    biproduct.toSubtype f p =
      biproduct.desc fun j => if h : p j then biproduct.ι (Subtype.restrictₓ p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext' _ _
    (by
      simp )

@[simp, reassoc]
theorem biproduct.ι_to_subtype_subtype (j : Subtype p) :
    biproduct.ι f j ≫ biproduct.toSubtype f p = biproduct.ι (Subtype.restrictₓ p f) j := by
  ext i
  rw [biproduct.to_subtype, category.assoc, biproduct.lift_π, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts[rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[simp, reassoc]
theorem biproduct.ι_from_subtype (j : Subtype p) :
    biproduct.ι (Subtype.restrictₓ p f) j ≫ biproduct.fromSubtype f p = biproduct.ι f j :=
  biproduct.ι_desc _ _

@[simp, reassoc]
theorem biproduct.from_subtype_to_subtype :
    biproduct.fromSubtype f p ≫ biproduct.toSubtype f p = 𝟙 (⨁ Subtype.restrictₓ p f) := by
  refine' biproduct.hom_ext _ _ fun j => _
  rw [category.assoc, biproduct.to_subtype_π, biproduct.from_subtype_π_subtype, category.id_comp]

@[simp, reassoc]
theorem biproduct.to_subtype_from_subtype [DecidablePred p] :
    biproduct.toSubtype f p ≫ biproduct.fromSubtype f p = biproduct.map fun j => if p j then 𝟙 (f j) else 0 := by
  ext1 i
  by_cases' h : p i
  · simp [← h]
    congr
    
  · simp [← h]
    

end

variable (f : J → C) (i : J) [HasBiproduct f] [HasBiproduct (Subtype.restrictₓ (fun j => i ≠ j) f)]

/-- The kernel of `biproduct.π f i` is the inclusion from the biproduct which omits `i`
from the index set `J` into the biproduct over `J`. -/
def biproduct.isLimitFromSubtype :
    IsLimit
      (KernelFork.ofι (biproduct.fromSubtype f fun j => i ≠ j)
        (by
          simp ) :
        KernelFork (biproduct.π f i)) :=
  (Fork.IsLimit.mk' _) fun s =>
    ⟨s.ι ≫ biproduct.toSubtype _ _, by
      ext j
      rw [kernel_fork.ι_of_ι, category.assoc, category.assoc, biproduct.to_subtype_from_subtype_assoc, biproduct.map_π]
      rcases em (i = j) with (rfl | h)
      · rw [if_neg (not_not.2 rfl), comp_zero, comp_zero, kernel_fork.condition]
        
      · rw [if_pos, category.comp_id]
        exact h
        ,
      by
      intro m hm
      rw [← hm, kernel_fork.ι_of_ι, category.assoc, biproduct.from_subtype_to_subtype]
      exact (category.comp_id _).symm⟩

/-- The cokernel of `biproduct.ι f i` is the projection from the biproduct over the index set `J`
onto the biproduct omitting `i`. -/
def biproduct.isColimitToSubtype :
    IsColimit
      (CokernelCofork.ofπ (biproduct.toSubtype f fun j => i ≠ j)
        (by
          simp ) :
        CokernelCofork (biproduct.ι f i)) :=
  (Cofork.IsColimit.mk' _) fun s =>
    ⟨biproduct.fromSubtype _ _ ≫ s.π, by
      ext j
      rw [cokernel_cofork.π_of_π, biproduct.to_subtype_from_subtype_assoc, biproduct.ι_map_assoc]
      rcases em (i = j) with (rfl | h)
      · rw [if_neg (not_not.2 rfl), zero_comp, cokernel_cofork.condition]
        
      · rw [if_pos, category.id_comp]
        exact h
        ,
      by
      intro m hm
      rw [← hm, cokernel_cofork.π_of_π, ← category.assoc, biproduct.from_subtype_to_subtype]
      exact (category.id_comp _).symm⟩

end πKernel

end Limits

namespace Limits

section FiniteBiproducts

variable {J : Type} [Fintype J] {K : Type} [Fintype K] {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasFiniteBiproducts C] {f : J → C} {g : K → C}

/-- Convert a (dependently typed) matrix to a morphism of biproducts.
-/
def biproduct.matrix (m : ∀ j k, f j ⟶ g k) : ⨁ f ⟶ ⨁ g :=
  biproduct.desc fun j => biproduct.lift fun k => m j k

@[simp, reassoc]
theorem biproduct.matrix_π (m : ∀ j k, f j ⟶ g k) (k : K) :
    biproduct.matrix m ≫ biproduct.π g k = biproduct.desc fun j => m j k := by
  ext
  simp [← biproduct.matrix]

@[simp, reassoc]
theorem biproduct.ι_matrix (m : ∀ j k, f j ⟶ g k) (j : J) :
    biproduct.ι f j ≫ biproduct.matrix m = biproduct.lift fun k => m j k := by
  ext
  simp [← biproduct.matrix]

/-- Extract the matrix components from a morphism of biproducts.
-/
def biproduct.components (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K) : f j ⟶ g k :=
  biproduct.ι f j ≫ m ≫ biproduct.π g k

@[simp]
theorem biproduct.matrix_components (m : ∀ j k, f j ⟶ g k) (j : J) (k : K) :
    biproduct.components (biproduct.matrix m) j k = m j k := by
  simp [← biproduct.components]

@[simp]
theorem biproduct.components_matrix (m : ⨁ f ⟶ ⨁ g) : (biproduct.matrix fun j k => biproduct.components m j k) = m := by
  ext
  simp [← biproduct.components]

/-- Morphisms between direct sums are matrices. -/
@[simps]
def biproduct.matrixEquiv : (⨁ f ⟶ ⨁ g) ≃ ∀ j k, f j ⟶ g k where
  toFun := biproduct.components
  invFun := biproduct.matrix
  left_inv := biproduct.components_matrix
  right_inv := fun m => by
    ext
    apply biproduct.matrix_components

end FiniteBiproducts

variable {J : Type w} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

instance biproduct.ι_mono (f : J → C) [HasBiproduct f] (b : J) : IsSplitMono (biproduct.ι f b) :=
  IsSplitMono.mk' { retraction := biproduct.desc <| Pi.single b _ }

instance biproduct.π_epi (f : J → C) [HasBiproduct f] (b : J) : IsSplitEpi (biproduct.π f b) :=
  IsSplitEpi.mk' { section_ := biproduct.lift <| Pi.single b _ }

/-- Auxiliary lemma for `biproduct.unique_up_to_iso`. -/
theorem biproduct.cone_point_unique_up_to_iso_hom (f : J → C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit) :
    (hb.IsLimit.conePointUniqueUpToIso (Biproduct.isLimit _)).Hom = biproduct.lift b.π :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:649:16: unsupported tactic `discrete_cases #[]
/-- Auxiliary lemma for `biproduct.unique_up_to_iso`. -/
theorem biproduct.cone_point_unique_up_to_iso_inv (f : J → C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit) :
    (hb.IsLimit.conePointUniqueUpToIso (Biproduct.isLimit _)).inv = biproduct.desc b.ι := by
  refine' biproduct.hom_ext' _ _ fun j => hb.is_limit.hom_ext fun j' => _
  trace "./././Mathport/Syntax/Translate/Basic.lean:649:16: unsupported tactic `discrete_cases #[]"
  rw [category.assoc, is_limit.cone_point_unique_up_to_iso_inv_comp, bicone.to_cone_π_app, biproduct.bicone_π,
    biproduct.ι_desc, biproduct.ι_π, b.to_cone_π_app, b.ι_π]

/-- Biproducts are unique up to isomorphism. This already follows because bilimits are limits,
    but in the case of biproducts we can give an isomorphism with particularly nice definitional
    properties, namely that `biproduct.lift b.π` and `biproduct.desc b.ι` are inverses of each
    other. -/
@[simps]
def biproduct.uniqueUpToIso (f : J → C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit) : b.x ≅ ⨁ f where
  Hom := biproduct.lift b.π
  inv := biproduct.desc b.ι
  hom_inv_id' := by
    rw [← biproduct.cone_point_unique_up_to_iso_hom f hb, ← biproduct.cone_point_unique_up_to_iso_inv f hb,
      iso.hom_inv_id]
  inv_hom_id' := by
    rw [← biproduct.cone_point_unique_up_to_iso_hom f hb, ← biproduct.cone_point_unique_up_to_iso_inv f hb,
      iso.inv_hom_id]

variable (C)

/-- A category with finite biproducts has a zero object. -/
-- see Note [lower instance priority]
instance (priority := 100) has_zero_object_of_has_finite_biproducts [HasFiniteBiproducts C] : HasZeroObject C := by
  refine' ⟨⟨biproduct Empty.elim, fun X => ⟨⟨⟨0⟩, _⟩⟩, fun X => ⟨⟨⟨0⟩, _⟩⟩⟩⟩
  tidy

section

variable {C} [Unique J] (f : J → C)

/-- The limit bicone for the biproduct over an index type with exactly one term. -/
@[simps]
def limitBiconeOfUnique : LimitBicone f where
  Bicone :=
    { x := f default,
      π := fun j =>
        eqToHom
          (by
            congr ),
      ι := fun j =>
        eqToHom
          (by
            congr ) }
  IsBilimit := { IsLimit := (limitConeOfUnique f).IsLimit, IsColimit := (colimitCoconeOfUnique f).IsColimit }

instance (priority := 100) has_biproduct_unique : HasBiproduct f :=
  HasBiproduct.mk (limitBiconeOfUnique f)

/-- A biproduct over a index type with exactly one term is just the object over that term. -/
@[simps]
def biproductUniqueIso : ⨁ f ≅ f default :=
  (biproduct.uniqueUpToIso _ (limitBiconeOfUnique f).IsBilimit).symm

end

variable {C}

/-- A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`
-/
@[nolint has_nonempty_instance]
structure BinaryBicone (P Q : C) where
  x : C
  fst : X ⟶ P
  snd : X ⟶ Q
  inl : P ⟶ X
  inr : Q ⟶ X
  inl_fst' : inl ≫ fst = 𝟙 P := by
    run_tac
      obviously
  inl_snd' : inl ≫ snd = 0 := by
    run_tac
      obviously
  inr_fst' : inr ≫ fst = 0 := by
    run_tac
      obviously
  inr_snd' : inr ≫ snd = 𝟙 Q := by
    run_tac
      obviously

restate_axiom binary_bicone.inl_fst'

restate_axiom binary_bicone.inl_snd'

restate_axiom binary_bicone.inr_fst'

restate_axiom binary_bicone.inr_snd'

attribute [simp, reassoc] binary_bicone.inl_fst binary_bicone.inl_snd binary_bicone.inr_fst binary_bicone.inr_snd

namespace BinaryBicone

variable {P Q : C}

/-- Extract the cone from a binary bicone. -/
def toCone (c : BinaryBicone P Q) : Cone (pair P Q) :=
  BinaryFan.mk c.fst c.snd

@[simp]
theorem to_cone_X (c : BinaryBicone P Q) : c.toCone.x = c.x :=
  rfl

@[simp]
theorem to_cone_π_app_left (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst :=
  rfl

@[simp]
theorem to_cone_π_app_right (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd :=
  rfl

@[simp]
theorem binary_fan_fst_to_cone (c : BinaryBicone P Q) : BinaryFan.fst c.toCone = c.fst :=
  rfl

@[simp]
theorem binary_fan_snd_to_cone (c : BinaryBicone P Q) : BinaryFan.snd c.toCone = c.snd :=
  rfl

/-- Extract the cocone from a binary bicone. -/
def toCocone (c : BinaryBicone P Q) : Cocone (pair P Q) :=
  BinaryCofan.mk c.inl c.inr

@[simp]
theorem to_cocone_X (c : BinaryBicone P Q) : c.toCocone.x = c.x :=
  rfl

@[simp]
theorem to_cocone_ι_app_left (c : BinaryBicone P Q) : c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl :=
  rfl

@[simp]
theorem to_cocone_ι_app_right (c : BinaryBicone P Q) : c.toCocone.ι.app ⟨WalkingPair.right⟩ = c.inr :=
  rfl

@[simp]
theorem binary_cofan_inl_to_cocone (c : BinaryBicone P Q) : BinaryCofan.inl c.toCocone = c.inl :=
  rfl

@[simp]
theorem binary_cofan_inr_to_cocone (c : BinaryBicone P Q) : BinaryCofan.inr c.toCocone = c.inr :=
  rfl

instance (c : BinaryBicone P Q) : IsSplitMono c.inl :=
  IsSplitMono.mk' { retraction := c.fst, id' := c.inl_fst }

instance (c : BinaryBicone P Q) : IsSplitMono c.inr :=
  IsSplitMono.mk' { retraction := c.snd, id' := c.inr_snd }

instance (c : BinaryBicone P Q) : IsSplitEpi c.fst :=
  IsSplitEpi.mk' { section_ := c.inl, id' := c.inl_fst }

instance (c : BinaryBicone P Q) : IsSplitEpi c.snd :=
  IsSplitEpi.mk' { section_ := c.inr, id' := c.inr_snd }

/-- Convert a `binary_bicone` into a `bicone` over a pair. -/
@[simps]
def toBicone {X Y : C} (b : BinaryBicone X Y) : Bicone (pairFunction X Y) where
  x := b.x
  π := fun j => WalkingPair.casesOn j b.fst b.snd
  ι := fun j => WalkingPair.casesOn j b.inl b.inr
  ι_π := fun j j' => by
    rcases j with ⟨⟩ <;> rcases j' with ⟨⟩
    tidy

/-- A binary bicone is a limit cone if and only if the corresponding bicone is a limit cone. -/
def toBiconeIsLimit {X Y : C} (b : BinaryBicone X Y) : IsLimit b.toBicone.toCone ≃ IsLimit b.toCone :=
  is_limit.equiv_iso_limit <|
    Cones.ext (Iso.refl _) fun j => by
      cases j
      tidy

/-- A binary bicone is a colimit cocone if and only if the corresponding bicone is a colimit
    cocone. -/
def toBiconeIsColimit {X Y : C} (b : BinaryBicone X Y) : IsColimit b.toBicone.toCocone ≃ IsColimit b.toCocone :=
  is_colimit.equiv_iso_colimit <|
    Cocones.ext (Iso.refl _) fun j => by
      cases j
      tidy

end BinaryBicone

namespace Bicone

/-- Convert a `bicone` over a function on `walking_pair` to a binary_bicone. -/
@[simps]
def toBinaryBicone {X Y : C} (b : Bicone (pairFunction X Y)) : BinaryBicone X Y where
  x := b.x
  fst := b.π WalkingPair.left
  snd := b.π WalkingPair.right
  inl := b.ι WalkingPair.left
  inr := b.ι WalkingPair.right
  inl_fst' := by
    simp [← bicone.ι_π]
    rfl
  inr_fst' := by
    simp [← bicone.ι_π]
  inl_snd' := by
    simp [← bicone.ι_π]
  inr_snd' := by
    simp [← bicone.ι_π]
    rfl

/-- A bicone over a pair is a limit cone if and only if the corresponding binary bicone is a limit
    cone.  -/
def toBinaryBiconeIsLimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsLimit b.toBinaryBicone.toCone ≃ IsLimit b.toCone :=
  is_limit.equiv_iso_limit <|
    Cones.ext (Iso.refl _) fun j => by
      rcases j with ⟨⟨⟩⟩ <;> tidy

/-- A bicone over a pair is a colimit cocone if and only if the corresponding binary bicone is a
    colimit cocone. -/
def toBinaryBiconeIsColimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsColimit b.toBinaryBicone.toCocone ≃ IsColimit b.toCocone :=
  is_colimit.equiv_iso_colimit <|
    Cocones.ext (Iso.refl _) fun j => by
      rcases j with ⟨⟨⟩⟩ <;> tidy

end Bicone

/-- Structure witnessing that a binary bicone is a limit cone and a limit cocone. -/
@[nolint has_nonempty_instance]
structure BinaryBicone.IsBilimit {P Q : C} (b : BinaryBicone P Q) where
  IsLimit : IsLimit b.toCone
  IsColimit : IsColimit b.toCocone

/-- A binary bicone is a bilimit bicone if and only if the corresponding bicone is a bilimit. -/
def BinaryBicone.toBiconeIsBilimit {X Y : C} (b : BinaryBicone X Y) : b.toBicone.IsBilimit ≃ b.IsBilimit where
  toFun := fun h => ⟨b.toBiconeIsLimit h.IsLimit, b.toBiconeIsColimit h.IsColimit⟩
  invFun := fun h => ⟨b.toBiconeIsLimit.symm h.IsLimit, b.toBiconeIsColimit.symm h.IsColimit⟩
  left_inv := fun ⟨h, h'⟩ => by
    dsimp' only
    simp
  right_inv := fun ⟨h, h'⟩ => by
    dsimp' only
    simp

/-- A bicone over a pair is a bilimit bicone if and only if the corresponding binary bicone is a
    bilimit. -/
def Bicone.toBinaryBiconeIsBilimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    b.toBinaryBicone.IsBilimit ≃ b.IsBilimit where
  toFun := fun h => ⟨b.toBinaryBiconeIsLimit h.IsLimit, b.toBinaryBiconeIsColimit h.IsColimit⟩
  invFun := fun h => ⟨b.toBinaryBiconeIsLimit.symm h.IsLimit, b.toBinaryBiconeIsColimit.symm h.IsColimit⟩
  left_inv := fun ⟨h, h'⟩ => by
    dsimp' only
    simp
  right_inv := fun ⟨h, h'⟩ => by
    dsimp' only
    simp

/-- A bicone over `P Q : C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_nonempty_instance]
structure BinaryBiproductData (P Q : C) where
  Bicone : BinaryBicone P Q
  IsBilimit : bicone.IsBilimit

/-- `has_binary_biproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class HasBinaryBiproduct (P Q : C) : Prop where mk' ::
  exists_binary_biproduct : Nonempty (BinaryBiproductData P Q)

theorem HasBinaryBiproduct.mk {P Q : C} (d : BinaryBiproductData P Q) : HasBinaryBiproduct P Q :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `binary_biproduct_data F` from `has_binary_biproduct F`.
-/
def getBinaryBiproductData (P Q : C) [HasBinaryBiproduct P Q] : BinaryBiproductData P Q :=
  Classical.choice HasBinaryBiproduct.exists_binary_biproduct

/-- A bicone for `P Q ` which is both a limit cone and a colimit cocone. -/
def BinaryBiproduct.bicone (P Q : C) [HasBinaryBiproduct P Q] : BinaryBicone P Q :=
  (getBinaryBiproductData P Q).Bicone

/-- `binary_biproduct.bicone P Q` is a limit bicone. -/
def BinaryBiproduct.isBilimit (P Q : C) [HasBinaryBiproduct P Q] : (BinaryBiproduct.bicone P Q).IsBilimit :=
  (getBinaryBiproductData P Q).IsBilimit

/-- `binary_biproduct.bicone P Q` is a limit cone. -/
def BinaryBiproduct.isLimit (P Q : C) [HasBinaryBiproduct P Q] : IsLimit (BinaryBiproduct.bicone P Q).toCone :=
  (getBinaryBiproductData P Q).IsBilimit.IsLimit

/-- `binary_biproduct.bicone P Q` is a colimit cocone. -/
def BinaryBiproduct.isColimit (P Q : C) [HasBinaryBiproduct P Q] : IsColimit (BinaryBiproduct.bicone P Q).toCocone :=
  (getBinaryBiproductData P Q).IsBilimit.IsColimit

section

variable (C)

/-- `has_binary_biproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class HasBinaryBiproducts : Prop where
  HasBinaryBiproduct : ∀ P Q : C, HasBinaryBiproduct P Q

attribute [instance] has_binary_biproducts.has_binary_biproduct

/-- A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
theorem has_binary_biproducts_of_finite_biproducts [HasFiniteBiproducts C] : HasBinaryBiproducts C :=
  { HasBinaryBiproduct := fun P Q =>
      HasBinaryBiproduct.mk
        { Bicone := (Biproduct.bicone (pairFunction P Q)).toBinaryBicone,
          IsBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (Biproduct.isBilimit _) } }

end

variable {P Q : C}

instance HasBinaryBiproduct.has_limit_pair [HasBinaryBiproduct P Q] : HasLimit (pair P Q) :=
  HasLimit.mk ⟨_, BinaryBiproduct.isLimit P Q⟩

instance HasBinaryBiproduct.has_colimit_pair [HasBinaryBiproduct P Q] : HasColimit (pair P Q) :=
  HasColimit.mk ⟨_, BinaryBiproduct.isColimit P Q⟩

instance (priority := 100) has_binary_products_of_has_binary_biproducts [HasBinaryBiproducts C] :
    HasBinaryProducts C where HasLimit := fun F => has_limit_of_iso (diagramIsoPair F).symm

instance (priority := 100) has_binary_coproducts_of_has_binary_biproducts [HasBinaryBiproducts C] :
    HasBinaryCoproducts C where HasColimit := fun F => has_colimit_of_iso (diagramIsoPair F)

/-- The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprodIso (X Y : C) [HasBinaryBiproduct X Y] : Limits.prod X Y ≅ Limits.coprod X Y :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (BinaryBiproduct.isLimit X Y)).trans <|
    IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

/-- An arbitrary choice of biproduct of a pair of objects. -/
abbrev biprod (X Y : C) [HasBinaryBiproduct X Y] :=
  (BinaryBiproduct.bicone X Y).x

-- mathport name: «expr ⊞ »
notation:20 X " ⊞ " Y:20 => biprod X Y

/-- The projection onto the first summand of a binary biproduct. -/
abbrev biprod.fst {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ X :=
  (BinaryBiproduct.bicone X Y).fst

/-- The projection onto the second summand of a binary biproduct. -/
abbrev biprod.snd {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ Y :=
  (BinaryBiproduct.bicone X Y).snd

/-- The inclusion into the first summand of a binary biproduct. -/
abbrev biprod.inl {X Y : C} [HasBinaryBiproduct X Y] : X ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inl

/-- The inclusion into the second summand of a binary biproduct. -/
abbrev biprod.inr {X Y : C} [HasBinaryBiproduct X Y] : Y ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inr

section

variable {X Y : C} [HasBinaryBiproduct X Y]

@[simp]
theorem BinaryBiproduct.bicone_fst : (BinaryBiproduct.bicone X Y).fst = biprod.fst :=
  rfl

@[simp]
theorem BinaryBiproduct.bicone_snd : (BinaryBiproduct.bicone X Y).snd = biprod.snd :=
  rfl

@[simp]
theorem BinaryBiproduct.bicone_inl : (BinaryBiproduct.bicone X Y).inl = biprod.inl :=
  rfl

@[simp]
theorem BinaryBiproduct.bicone_inr : (BinaryBiproduct.bicone X Y).inr = biprod.inr :=
  rfl

end

@[simp, reassoc]
theorem biprod.inl_fst {X Y : C} [HasBinaryBiproduct X Y] : (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
  (BinaryBiproduct.bicone X Y).inl_fst

@[simp, reassoc]
theorem biprod.inl_snd {X Y : C} [HasBinaryBiproduct X Y] : (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
  (BinaryBiproduct.bicone X Y).inl_snd

@[simp, reassoc]
theorem biprod.inr_fst {X Y : C} [HasBinaryBiproduct X Y] : (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
  (BinaryBiproduct.bicone X Y).inr_fst

@[simp, reassoc]
theorem biprod.inr_snd {X Y : C} [HasBinaryBiproduct X Y] : (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
  (BinaryBiproduct.bicone X Y).inr_snd

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbrev biprod.lift {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊞ Y :=
  (BinaryBiproduct.isLimit X Y).lift (BinaryFan.mk f g)

/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbrev biprod.desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⊞ Y ⟶ W :=
  (BinaryBiproduct.isColimit X Y).desc (BinaryCofan.mk f g)

@[simp, reassoc]
theorem biprod.lift_fst {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.fst = f :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.left⟩

@[simp, reassoc]
theorem biprod.lift_snd {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.snd = g :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.right⟩

@[simp, reassoc]
theorem biprod.inl_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inl ≫ biprod.desc f g = f :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.left⟩

@[simp, reassoc]
theorem biprod.inr_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inr ≫ biprod.desc f g = g :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.right⟩

instance biprod.mono_lift_of_mono_left {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [Mono f] :
    Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_fst _ _

instance biprod.mono_lift_of_mono_right {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [Mono g] :
    Mono (biprod.lift f g) :=
  mono_of_mono_fac <| biprod.lift_snd _ _

instance biprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [Epi f] :
    Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inl_desc _ _

instance biprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [Epi g] :
    Epi (biprod.desc f g) :=
  epi_of_epi_fac <| biprod.inr_desc _ _

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbrev biprod.map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    W ⊞ X ⟶ Y ⊞ Z :=
  IsLimit.map (BinaryBiproduct.bicone W X).toCone (BinaryBiproduct.isLimit Y Z) (@mapPair _ _ (pair W X) (pair Y Z) f g)

/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
abbrev biprod.map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    W ⊞ X ⟶ Y ⊞ Z :=
  IsColimit.map (BinaryBiproduct.isColimit W X) (BinaryBiproduct.bicone Y Z).toCocone
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

@[ext]
theorem biprod.hom_ext {X Y Z : C} [HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y) (h₀ : f ≫ biprod.fst = g ≫ biprod.fst)
    (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y) h₀ h₁

@[ext]
theorem biprod.hom_ext' {X Y Z : C} [HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z) (h₀ : biprod.inl ≫ f = biprod.inl ≫ g)
    (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (BinaryBiproduct.isColimit X Y) h₀ h₁

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
def biprod.isoProd (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨯ Y :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) (limit.isLimit _)

@[simp]
theorem biprod.iso_prod_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).Hom = prod.lift biprod.fst biprod.snd := by
  ext <;> simp [← biprod.iso_prod]

@[simp]
theorem biprod.iso_prod_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).inv = biprod.lift prod.fst prod.snd := by
  apply biprod.hom_ext <;> simp [← iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
def biprod.isoCoprod (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨿ Y :=
  IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

@[simp]
theorem biprod.iso_coprod_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).inv = coprod.desc biprod.inl biprod.inr := by
  ext <;> simp [← biprod.iso_coprod] <;> rfl

@[simp]
theorem biprod_iso_coprod_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).Hom = biprod.desc coprod.inl coprod.inr := by
  apply biprod.hom_ext' <;> simp [iso.eq_comp_inv]

theorem biprod.map_eq_map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.map f g = biprod.map' f g := by
  ext
  · simp only [← map_pair_left, ← is_colimit.ι_map, ← is_limit.map_π, ← biprod.inl_fst_assoc, ← category.assoc,
      binary_bicone.to_cone_π_app_left, binary_biproduct.bicone_fst, binary_bicone.to_cocone_ι_app_left,
      binary_biproduct.bicone_inl]
    simp
    
  · simp only [← map_pair_left, ← is_colimit.ι_map, ← is_limit.map_π, ← zero_comp, ← biprod.inl_snd_assoc, ←
      category.assoc, binary_bicone.to_cone_π_app_right, binary_biproduct.bicone_snd,
      binary_bicone.to_cocone_ι_app_left, binary_biproduct.bicone_inl]
    simp
    
  · simp only [← map_pair_right, ← biprod.inr_fst_assoc, ← is_colimit.ι_map, ← is_limit.map_π, ← zero_comp, ←
      category.assoc, binary_bicone.to_cone_π_app_left, binary_biproduct.bicone_fst,
      binary_bicone.to_cocone_ι_app_right, binary_biproduct.bicone_inr]
    simp
    
  · simp only [← map_pair_right, ← is_colimit.ι_map, ← is_limit.map_π, ← biprod.inr_snd_assoc, ← category.assoc,
      binary_bicone.to_cone_π_app_right, binary_biproduct.bicone_snd, binary_bicone.to_cocone_ι_app_right,
      binary_biproduct.bicone_inr]
    simp
    

instance biprod.inl_mono {X Y : C} [HasBinaryBiproduct X Y] : IsSplitMono (biprod.inl : X ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.fst }

instance biprod.inr_mono {X Y : C} [HasBinaryBiproduct X Y] : IsSplitMono (biprod.inr : Y ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.snd }

instance biprod.fst_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.fst : X ⊞ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := biprod.inl }

instance biprod.snd_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.snd : X ⊞ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := biprod.inr }

@[simp, reassoc]
theorem biprod.map_fst {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[simp, reassoc]
theorem biprod.map_snd {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[simp, reassoc]
theorem biprod.inl_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.inl ≫ biprod.map f g = f ≫ biprod.inl := by
  rw [biprod.map_eq_map']
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ ⟨walking_pair.left⟩

@[simp, reassoc]
theorem biprod.inr_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.inr ≫ biprod.map f g = g ≫ biprod.inr := by
  rw [biprod.map_eq_map']
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ ⟨walking_pair.right⟩

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
def biprod.mapIso {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ≅ Y) (g : X ≅ Z) :
    W ⊞ X ≅ Y ⊞ Z where
  Hom := biprod.map f.Hom g.Hom
  inv := biprod.map f.inv g.inv

/-- Auxiliary lemma for `biprod.unique_up_to_iso`. -/
theorem biprod.cone_point_unique_up_to_iso_hom (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).Hom = biprod.lift b.fst b.snd :=
  rfl

/-- Auxiliary lemma for `biprod.unique_up_to_iso`. -/
theorem biprod.cone_point_unique_up_to_iso_inv (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).inv = biprod.desc b.inl b.inr := by
  refine' biprod.hom_ext' _ _ (hb.is_limit.hom_ext fun j => _) (hb.is_limit.hom_ext fun j => _)
  all_goals
    simp only [← category.assoc, ← is_limit.cone_point_unique_up_to_iso_inv_comp]
    rcases j with ⟨⟨⟩⟩
  all_goals
    simp

/-- Binary biproducts are unique up to isomorphism. This already follows because bilimits are
    limits, but in the case of biproducts we can give an isomorphism with particularly nice
    definitional properties, namely that `biprod.lift b.fst b.snd` and `biprod.desc b.inl b.inr`
    are inverses of each other. -/
@[simps]
def biprod.uniqueUpToIso (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y} (hb : b.IsBilimit) :
    b.x ≅ X ⊞ Y where
  Hom := biprod.lift b.fst b.snd
  inv := biprod.desc b.inl b.inr
  hom_inv_id' := by
    rw [← biprod.cone_point_unique_up_to_iso_hom X Y hb, ← biprod.cone_point_unique_up_to_iso_inv X Y hb,
      iso.hom_inv_id]
  inv_hom_id' := by
    rw [← biprod.cone_point_unique_up_to_iso_hom X Y hb, ← biprod.cone_point_unique_up_to_iso_inv X Y hb,
      iso.inv_hom_id]

section

variable (X Y : C) [HasBinaryBiproduct X Y]

-- There are three further variations,
-- about `is_iso biprod.inr`, `is_iso biprod.fst` and `is_iso biprod.snd`,
-- but any one suffices to prove `indecomposable_of_simple`
-- and they are likely not separately useful.
theorem biprod.is_iso_inl_iff_id_eq_fst_comp_inl :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ 𝟙 (X ⊞ Y) = biprod.fst ≫ biprod.inl := by
  constructor
  · intro h
    have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 biprod.inl_fst
    rw [is_iso.inv_hom_id_assoc, category.comp_id] at this
    rw [this, is_iso.inv_hom_id]
    
  · intro h
    exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩
    

end

section BiprodKernel

section BinaryBicone

variable {X Y : C} (c : BinaryBicone X Y)

/-- A kernel fork for the kernel of `binary_bicone.fst`. It consists of the morphism
`binary_bicone.inr`. -/
def BinaryBicone.fstKernelFork : KernelFork c.fst :=
  KernelFork.ofι c.inr c.inr_fst

@[simp]
theorem BinaryBicone.fst_kernel_fork_ι : (BinaryBicone.fstKernelFork c).ι = c.inr :=
  rfl

/-- A kernel fork for the kernel of `binary_bicone.snd`. It consists of the morphism
`binary_bicone.inl`. -/
def BinaryBicone.sndKernelFork : KernelFork c.snd :=
  KernelFork.ofι c.inl c.inl_snd

@[simp]
theorem BinaryBicone.snd_kernel_fork_ι : (BinaryBicone.sndKernelFork c).ι = c.inl :=
  rfl

/-- A cokernel cofork for the cokernel of `binary_bicone.inl`. It consists of the morphism
`binary_bicone.snd`. -/
def BinaryBicone.inlCokernelCofork : CokernelCofork c.inl :=
  CokernelCofork.ofπ c.snd c.inl_snd

@[simp]
theorem BinaryBicone.inl_cokernel_cofork_π : (BinaryBicone.inlCokernelCofork c).π = c.snd :=
  rfl

/-- A cokernel cofork for the cokernel of `binary_bicone.inr`. It consists of the morphism
`binary_bicone.fst`. -/
def BinaryBicone.inrCokernelCofork : CokernelCofork c.inr :=
  CokernelCofork.ofπ c.fst c.inr_fst

@[simp]
theorem BinaryBicone.inr_cokernel_cofork_π : (BinaryBicone.inrCokernelCofork c).π = c.fst :=
  rfl

variable {c}

/-- The fork defined in `binary_bicone.fst_kernel_fork` is indeed a kernel. -/
def BinaryBicone.isLimitFstKernelFork (i : IsLimit c.toCone) : IsLimit c.fstKernelFork :=
  (Fork.IsLimit.mk' _) fun s =>
    ⟨s.ι ≫ c.snd, by
      apply binary_fan.is_limit.hom_ext i <;> simp , fun m hm => by
      simp [hm]⟩

/-- The fork defined in `binary_bicone.snd_kernel_fork` is indeed a kernel. -/
def BinaryBicone.isLimitSndKernelFork (i : IsLimit c.toCone) : IsLimit c.sndKernelFork :=
  (Fork.IsLimit.mk' _) fun s =>
    ⟨s.ι ≫ c.fst, by
      apply binary_fan.is_limit.hom_ext i <;> simp , fun m hm => by
      simp [hm]⟩

/-- The cofork defined in `binary_bicone.inl_cokernel_cofork` is indeed a cokernel. -/
def BinaryBicone.isColimitInlCokernelCofork (i : IsColimit c.toCocone) : IsColimit c.inlCokernelCofork :=
  (Cofork.IsColimit.mk' _) fun s =>
    ⟨c.inr ≫ s.π, by
      apply binary_cofan.is_colimit.hom_ext i <;> simp , fun m hm => by
      simp [hm]⟩

/-- The cofork defined in `binary_bicone.inr_cokernel_cofork` is indeed a cokernel. -/
def BinaryBicone.isColimitInrCokernelCofork (i : IsColimit c.toCocone) : IsColimit c.inrCokernelCofork :=
  (Cofork.IsColimit.mk' _) fun s =>
    ⟨c.inl ≫ s.π, by
      apply binary_cofan.is_colimit.hom_ext i <;> simp , fun m hm => by
      simp [hm]⟩

end BinaryBicone

section HasBinaryBiproduct

variable (X Y : C) [HasBinaryBiproduct X Y]

/-- A kernel fork for the kernel of `biprod.fst`. It consists of the
morphism `biprod.inr`. -/
def biprod.fstKernelFork : KernelFork (biprod.fst : X ⊞ Y ⟶ X) :=
  BinaryBicone.fstKernelFork _

@[simp]
theorem biprod.fst_kernel_fork_ι : Fork.ι (biprod.fstKernelFork X Y) = biprod.inr :=
  rfl

/-- The fork `biprod.fst_kernel_fork` is indeed a limit.  -/
def biprod.isKernelFstKernelFork : IsLimit (biprod.fstKernelFork X Y) :=
  BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)

/-- A kernel fork for the kernel of `biprod.snd`. It consists of the
morphism `biprod.inl`. -/
def biprod.sndKernelFork : KernelFork (biprod.snd : X ⊞ Y ⟶ Y) :=
  BinaryBicone.sndKernelFork _

@[simp]
theorem biprod.snd_kernel_fork_ι : Fork.ι (biprod.sndKernelFork X Y) = biprod.inl :=
  rfl

/-- The fork `biprod.snd_kernel_fork` is indeed a limit.  -/
def biprod.isKernelSndKernelFork : IsLimit (biprod.sndKernelFork X Y) :=
  BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inl`. It consists of the
morphism `biprod.snd`. -/
def biprod.inlCokernelCofork : CokernelCofork (biprod.inl : X ⟶ X ⊞ Y) :=
  BinaryBicone.inlCokernelCofork _

@[simp]
theorem biprod.inl_cokernel_cofork_π : Cofork.π (biprod.inlCokernelCofork X Y) = biprod.snd :=
  rfl

/-- The cofork `biprod.inl_cokernel_fork` is indeed a colimit.  -/
def biprod.isCokernelInlCokernelFork : IsColimit (biprod.inlCokernelCofork X Y) :=
  BinaryBicone.isColimitInlCokernelCofork (BinaryBiproduct.isColimit _ _)

/-- A cokernel cofork for the cokernel of `biprod.inr`. It consists of the
morphism `biprod.fst`. -/
def biprod.inrCokernelCofork : CokernelCofork (biprod.inr : Y ⟶ X ⊞ Y) :=
  BinaryBicone.inrCokernelCofork _

@[simp]
theorem biprod.inr_cokernel_cofork_π : Cofork.π (biprod.inrCokernelCofork X Y) = biprod.fst :=
  rfl

/-- The cofork `biprod.inr_cokernel_fork` is indeed a colimit.  -/
def biprod.isCokernelInrCokernelFork : IsColimit (biprod.inrCokernelCofork X Y) :=
  BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit _ _)

end HasBinaryBiproduct

end BiprodKernel

section IsZero

/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps]
def isoBiprodZero {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ≅ X ⊞ Y where
  Hom := biprod.inl
  inv := biprod.fst
  inv_hom_id' := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [← category.assoc, ← biprod.inl_fst, ← category.comp_id, ← category.id_comp, ← biprod.inl_snd, ←
        comp_zero]
    apply hY.eq_of_tgt

/-- If `X` is a zero object, `Y ≅ X ⊞ Y` for any `Y`. -/
@[simps]
def isoZeroBiprod {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero X) : Y ≅ X ⊞ Y where
  Hom := biprod.inr
  inv := biprod.snd
  inv_hom_id' := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [← category.assoc, ← biprod.inr_snd, ← category.comp_id, ← category.id_comp, ← biprod.inr_fst, ←
        comp_zero]
    apply hY.eq_of_tgt

end IsZero

section

variable [HasBinaryBiproducts C]

/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simps]
def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  Hom := biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst

/-- An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct.
-/
@[simps]
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  Hom := biprod.desc biprod.inr biprod.inl
  inv := biprod.desc biprod.inr biprod.inl

theorem biprod.braiding'_eq_braiding {P Q : C} : biprod.braiding' P Q = biprod.braiding P Q := by
  tidy

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
theorem biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    biprod.map f g ≫ (biprod.braiding _ _).Hom = (biprod.braiding _ _).Hom ≫ biprod.map g f := by
  tidy

@[reassoc]
theorem biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
    (biprod.braiding X W).Hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).Hom = biprod.map g f := by
  tidy

@[simp, reassoc]
theorem biprod.symmetry' (P Q : C) :
    biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) := by
  tidy

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
theorem biprod.symmetry (P Q : C) : (biprod.braiding P Q).Hom ≫ (biprod.braiding Q P).Hom = 𝟙 _ := by
  simp

end

-- TODO:
-- If someone is interested, they could provide the constructions:
--   has_binary_biproducts ↔ has_finite_biproducts
end Limits

namespace Limits

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable {J : Type} [Fintype J]

open CategoryTheory.Preadditive

open BigOperators

/-- In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def isBilimitOfTotal {f : J → C} (b : Bicone f) (total : (∑ j : J, b.π j ≫ b.ι j) = 𝟙 b.x) : b.IsBilimit where
  IsLimit :=
    { lift := fun s => ∑ j : J, s.π.app ⟨j⟩ ≫ b.ι j,
      uniq' := fun s m h => by
        erw [← category.comp_id m, ← Total, comp_sum]
        apply Finset.sum_congr rfl
        intro j m
        erw [reassoc_of (h ⟨j⟩)],
      fac' := fun s j => by
        cases j
        simp only [← sum_comp, ← category.assoc, ← bicone.to_cone_π_app, ← b.ι_π, ← comp_dite]
        -- See note [dsimp, simp].
        dsimp'
        simp }
  IsColimit :=
    { desc := fun s => ∑ j : J, b.π j ≫ s.ι.app ⟨j⟩,
      uniq' := fun s m h => by
        erw [← category.id_comp m, ← Total, sum_comp]
        apply Finset.sum_congr rfl
        intro j m
        erw [category.assoc, h ⟨j⟩],
      fac' := fun s j => by
        cases j
        simp only [← comp_sum, category.assoc, ← bicone.to_cocone_ι_app, ← b.ι_π, ← dite_comp]
        dsimp'
        simp }

theorem IsBilimit.total {f : J → C} {b : Bicone f} (i : b.IsBilimit) : (∑ j : J, b.π j ≫ b.ι j) = 𝟙 b.x :=
  i.IsLimit.hom_ext fun j => by
    cases j
    simp [← sum_comp, ← b.ι_π, ← comp_dite]

/-- In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem has_biproduct_of_total {f : J → C} (b : Bicone f) (total : (∑ j : J, b.π j ≫ b.ι j) = 𝟙 b.x) : HasBiproduct f :=
  HasBiproduct.mk { Bicone := b, IsBilimit := isBilimitOfTotal b Total }

/-- In a preadditive category, any finite bicone which is a limit cone is in fact a bilimit
    bicone. -/
def isBilimitOfIsLimit {f : J → C} (t : Bicone f) (ht : IsLimit t.toCone) : t.IsBilimit :=
  isBilimitOfTotal _ <|
    ht.hom_ext fun j => by
      cases j
      simp [← sum_comp, ← t.ι_π, ← dite_comp, ← comp_dite]

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def biconeIsBilimitOfLimitConeOfIsLimit {f : J → C} {t : Cone (Discrete.functor f)} (ht : IsLimit t) :
    (Bicone.ofLimitCone ht).IsBilimit :=
  isBilimitOfIsLimit _ <|
    IsLimit.ofIsoLimit ht <|
      Cones.ext (Iso.refl _)
        (by
          rintro ⟨j⟩
          tidy)

/-- In a preadditive category, if the product over `f : J → C` exists,
    then the biproduct over `f` exists. -/
theorem HasBiproduct.of_has_product (f : J → C) [HasProduct f] : HasBiproduct f :=
  HasBiproduct.mk { Bicone := _, IsBilimit := biconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

/-- In a preadditive category, any finite bicone which is a colimit cocone is in fact a bilimit
    bicone. -/
def isBilimitOfIsColimit {f : J → C} (t : Bicone f) (ht : IsColimit t.toCocone) : t.IsBilimit :=
  isBilimitOfTotal _ <|
    ht.hom_ext fun j => by
      cases j
      simp_rw [bicone.to_cocone_ι_app, comp_sum, ← category.assoc, t.ι_π, dite_comp]
      tidy

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def biconeIsBilimitOfColimitCoconeOfIsColimit {f : J → C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t) :
    (Bicone.ofColimitCocone ht).IsBilimit :=
  isBilimitOfIsColimit _ <|
    IsColimit.ofIsoColimit ht <|
      Cocones.ext (Iso.refl _)
        (by
          rintro ⟨j⟩
          tidy)

/-- In a preadditive category, if the coproduct over `f : J → C` exists,
    then the biproduct over `f` exists. -/
theorem HasBiproduct.of_has_coproduct (f : J → C) [HasCoproduct f] : HasBiproduct f :=
  HasBiproduct.mk { Bicone := _, IsBilimit := biconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

/-- A preadditive category with finite products has finite biproducts. -/
theorem HasFiniteBiproducts.of_has_finite_products [HasFiniteProducts C] : HasFiniteBiproducts C :=
  ⟨fun J _ => { HasBiproduct := fun F => has_biproduct.of_has_product _ }⟩

/-- A preadditive category with finite coproducts has finite biproducts. -/
theorem HasFiniteBiproducts.of_has_finite_coproducts [HasFiniteCoproducts C] : HasFiniteBiproducts C :=
  ⟨fun J _ => { HasBiproduct := fun F => has_biproduct.of_has_coproduct _ }⟩

section

variable {f : J → C} [HasBiproduct f]

/-- In any preadditive category, any biproduct satsifies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
@[simp]
theorem biproduct.total : (∑ j : J, biproduct.π f j ≫ biproduct.ι f j) = 𝟙 (⨁ f) :=
  IsBilimit.total (Biproduct.isBilimit _)

theorem biproduct.lift_eq {T : C} {g : ∀ j, T ⟶ f j} : biproduct.lift g = ∑ j, g j ≫ biproduct.ι f j := by
  ext j
  simp [← sum_comp, ← biproduct.ι_π, ← comp_dite]

theorem biproduct.desc_eq {T : C} {g : ∀ j, f j ⟶ T} : biproduct.desc g = ∑ j, biproduct.π f j ≫ g j := by
  ext j
  simp [← comp_sum, ← biproduct.ι_π_assoc, ← dite_comp]

@[simp, reassoc]
theorem biproduct.lift_desc {T U : C} {g : ∀ j, T ⟶ f j} {h : ∀ j, f j ⟶ U} :
    biproduct.lift g ≫ biproduct.desc h = ∑ j : J, g j ≫ h j := by
  simp [← biproduct.lift_eq, ← biproduct.desc_eq, ← comp_sum, ← sum_comp, ← biproduct.ι_π_assoc, ← comp_dite, ←
    dite_comp]

theorem biproduct.map_eq [HasFiniteBiproducts C] {f g : J → C} {h : ∀ j, f j ⟶ g j} :
    biproduct.map h = ∑ j : J, biproduct.π f j ≫ h j ≫ biproduct.ι g j := by
  ext
  simp [← biproduct.ι_π, ← biproduct.ι_π_assoc, ← comp_sum, ← sum_comp, ← comp_dite, ← dite_comp]

@[simp, reassoc]
theorem biproduct.matrix_desc {K : Type} [Fintype K] [HasFiniteBiproducts C] {f : J → C} {g : K → C}
    (m : ∀ j k, f j ⟶ g k) {P} (x : ∀ k, g k ⟶ P) :
    biproduct.matrix m ≫ biproduct.desc x = biproduct.desc fun j => ∑ k, m j k ≫ x k := by
  ext
  simp

@[simp, reassoc]
theorem biproduct.lift_matrix {K : Type} [Fintype K] [HasFiniteBiproducts C] {f : J → C} {g : K → C} {P}
    (x : ∀ j, P ⟶ f j) (m : ∀ j k, f j ⟶ g k) :
    biproduct.lift x ≫ biproduct.matrix m = biproduct.lift fun k => ∑ j, x j ≫ m j k := by
  ext
  simp

@[reassoc]
theorem biproduct.matrix_map {K : Type} [Fintype K] [HasFiniteBiproducts C] {f : J → C} {g : K → C} {h : K → C}
    (m : ∀ j k, f j ⟶ g k) (n : ∀ k, g k ⟶ h k) :
    biproduct.matrix m ≫ biproduct.map n = biproduct.matrix fun j k => m j k ≫ n k := by
  ext
  simp

@[reassoc]
theorem biproduct.map_matrix {K : Type} [Fintype K] [HasFiniteBiproducts C] {f : J → C} {g : J → C} {h : K → C}
    (m : ∀ k, f k ⟶ g k) (n : ∀ j k, g j ⟶ h k) :
    biproduct.map m ≫ biproduct.matrix n = biproduct.matrix fun j k => m j ≫ n j k := by
  ext
  simp

end

/-- Reindex a categorical biproduct via an equivalence of the index types. -/
@[simps]
def biproduct.reindex {β γ : Type} [Fintype β] [DecidableEq β] [DecidableEq γ] (ε : β ≃ γ) (f : γ → C) [HasBiproduct f]
    [HasBiproduct (f ∘ ε)] : ⨁ f ∘ ε ≅ ⨁ f where
  Hom := biproduct.desc fun b => biproduct.ι f (ε b)
  inv := biproduct.lift fun b => biproduct.π f (ε b)
  hom_inv_id' := by
    ext b b'
    by_cases' h : b = b'
    · subst h
      simp
      
    · simp [← h]
      
  inv_hom_id' := by
    ext g g'
    by_cases' h : g = g' <;>
      simp [← preadditive.sum_comp, ← preadditive.comp_sum, ← biproduct.ι_π, ← biproduct.ι_π_assoc, ← comp_dite, ←
        Equivₓ.apply_eq_iff_eq_symm_apply, ← Finset.sum_dite_eq' Finset.univ (ε.symm g') _, ← h]

/-- In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def isBinaryBilimitOfTotal {X Y : C} (b : BinaryBicone X Y) (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.x) :
    b.IsBilimit where
  IsLimit :=
    { lift := fun s => BinaryFan.fst s ≫ b.inl + BinaryFan.snd s ≫ b.inr,
      uniq' := fun s m h => by
        erw [← category.comp_id m, ← Total, comp_add, reassoc_of (h ⟨walking_pair.left⟩),
          reassoc_of (h ⟨walking_pair.right⟩)],
      fac' := fun s j => by
        rcases j with ⟨⟨⟩⟩ <;> simp }
  IsColimit :=
    { desc := fun s => b.fst ≫ BinaryCofan.inl s + b.snd ≫ BinaryCofan.inr s,
      uniq' := fun s m h => by
        erw [← category.id_comp m, ← Total, add_comp, category.assoc, category.assoc, h ⟨walking_pair.left⟩,
          h ⟨walking_pair.right⟩],
      fac' := fun s j => by
        rcases j with ⟨⟨⟩⟩ <;> simp }

theorem IsBilimit.binary_total {X Y : C} {b : BinaryBicone X Y} (i : b.IsBilimit) :
    b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.x :=
  i.IsLimit.hom_ext fun j => by
    rcases j with ⟨⟨⟩⟩ <;> simp

/-- In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem has_binary_biproduct_of_total {X Y : C} (b : BinaryBicone X Y) (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.x) :
    HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk { Bicone := b, IsBilimit := isBinaryBilimitOfTotal b Total }

/-- We can turn any limit cone over a pair into a bicone. -/
@[simps]
def BinaryBicone.ofLimitCone {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t) : BinaryBicone X Y where
  x := t.x
  fst := t.π.app ⟨WalkingPair.left⟩
  snd := t.π.app ⟨WalkingPair.right⟩
  inl := ht.lift (BinaryFan.mk (𝟙 X) 0)
  inr := ht.lift (BinaryFan.mk 0 (𝟙 Y))

theorem inl_of_is_limit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) :
    t.inl = ht.lift (BinaryFan.mk (𝟙 X) 0) := by
  apply ht.uniq (binary_fan.mk (𝟙 X) 0) <;> rintro ⟨⟨⟩⟩ <;> dsimp' <;> simp

theorem inr_of_is_limit {X Y : C} {t : BinaryBicone X Y} (ht : IsLimit t.toCone) :
    t.inr = ht.lift (BinaryFan.mk 0 (𝟙 Y)) := by
  apply ht.uniq (binary_fan.mk 0 (𝟙 Y)) <;> rintro ⟨⟨⟩⟩ <;> dsimp' <;> simp

/-- In a preadditive category, any binary bicone which is a limit cone is in fact a bilimit
    bicone. -/
def isBinaryBilimitOfIsLimit {X Y : C} (t : BinaryBicone X Y) (ht : IsLimit t.toCone) : t.IsBilimit :=
  isBinaryBilimitOfTotal _
    (by
      refine' binary_fan.is_limit.hom_ext ht _ _ <;> simp )

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def binaryBiconeIsBilimitOfLimitConeOfIsLimit {X Y : C} {t : Cone (pair X Y)} (ht : IsLimit t) :
    (BinaryBicone.ofLimitCone ht).IsBilimit :=
  isBinaryBilimitOfTotal _ <|
    BinaryFan.IsLimit.hom_ext ht
      (by
        simp )
      (by
        simp )

/-- In a preadditive category, if the product of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
theorem HasBinaryBiproduct.of_has_binary_product (X Y : C) [HasBinaryProduct X Y] : HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk { Bicone := _, IsBilimit := binaryBiconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

/-- In a preadditive category, if all binary products exist, then all binary biproducts exist. -/
theorem HasBinaryBiproducts.of_has_binary_products [HasBinaryProducts C] : HasBinaryBiproducts C :=
  { HasBinaryBiproduct := fun X Y => HasBinaryBiproduct.of_has_binary_product X Y }

/-- We can turn any colimit cocone over a pair into a bicone. -/
@[simps]
def BinaryBicone.ofColimitCocone {X Y : C} {t : Cocone (pair X Y)} (ht : IsColimit t) : BinaryBicone X Y where
  x := t.x
  fst := ht.desc (BinaryCofan.mk (𝟙 X) 0)
  snd := ht.desc (BinaryCofan.mk 0 (𝟙 Y))
  inl := t.ι.app ⟨WalkingPair.left⟩
  inr := t.ι.app ⟨WalkingPair.right⟩

theorem fst_of_is_colimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone) :
    t.fst = ht.desc (BinaryCofan.mk (𝟙 X) 0) := by
  apply ht.uniq (binary_cofan.mk (𝟙 X) 0)
  rintro ⟨⟨⟩⟩ <;> dsimp' <;> simp

theorem snd_of_is_colimit {X Y : C} {t : BinaryBicone X Y} (ht : IsColimit t.toCocone) :
    t.snd = ht.desc (BinaryCofan.mk 0 (𝟙 Y)) := by
  apply ht.uniq (binary_cofan.mk 0 (𝟙 Y))
  rintro ⟨⟨⟩⟩ <;> dsimp' <;> simp

/-- In a preadditive category, any binary bicone which is a colimit cocone is in fact a
    bilimit bicone. -/
def isBinaryBilimitOfIsColimit {X Y : C} (t : BinaryBicone X Y) (ht : IsColimit t.toCocone) : t.IsBilimit :=
  isBinaryBilimitOfTotal _
    (by
      refine' binary_cofan.is_colimit.hom_ext ht _ _ <;> simp
      · rw [category.comp_id t.inl]
        
      · rw [category.comp_id t.inr]
        )

/-- We can turn any colimit cocone over a pair into a bilimit bicone. -/
def binaryBiconeIsBilimitOfColimitCoconeOfIsColimit {X Y : C} {t : Cocone (pair X Y)} (ht : IsColimit t) :
    (BinaryBicone.ofColimitCocone ht).IsBilimit :=
  isBinaryBilimitOfIsColimit (BinaryBicone.ofColimitCocone ht) <|
    IsColimit.ofIsoColimit ht <|
      (Cocones.ext (Iso.refl _)) fun j => by
        rcases j with ⟨⟨⟩⟩
        tidy

/-- In a preadditive category, if the coproduct of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
theorem HasBinaryBiproduct.of_has_binary_coproduct (X Y : C) [HasBinaryCoproduct X Y] : HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { Bicone := _, IsBilimit := binaryBiconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

/-- In a preadditive category, if all binary coproducts exist, then all binary biproducts exist. -/
theorem HasBinaryBiproducts.of_has_binary_coproducts [HasBinaryCoproducts C] : HasBinaryBiproducts C :=
  { HasBinaryBiproduct := fun X Y => HasBinaryBiproduct.of_has_binary_coproduct X Y }

section

variable {X Y : C} [HasBinaryBiproduct X Y]

/-- In any preadditive category, any binary biproduct satsifies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp]
theorem biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) := by
  ext <;> simp [← add_comp]

theorem biprod.lift_eq {T : C} {f : T ⟶ X} {g : T ⟶ Y} : biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by
  ext <;> simp [← add_comp]

theorem biprod.desc_eq {T : C} {f : X ⟶ T} {g : Y ⟶ T} : biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g := by
  ext <;> simp [← add_comp]

@[simp, reassoc]
theorem biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
    biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i := by
  simp [← biprod.lift_eq, ← biprod.desc_eq]

theorem biprod.map_eq [HasBinaryBiproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
    biprod.map f g = biprod.fst ≫ f ≫ biprod.inl + biprod.snd ≫ g ≫ biprod.inr := by
  apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

/-- Every split mono `f` with a cokernel induces a binary bicone with `f` as its `inl` and
the cokernel map as its `snd`.
We will show in `is_bilimit_binary_bicone_of_split_mono_of_cokernel` that this binary bicone is in
fact already a biproduct. -/
@[simps]
def binaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f] {c : CokernelCofork f} (i : IsColimit c) :
    BinaryBicone X c.x where
  x := Y
  fst := retraction f
  snd := c.π
  inl := f
  inr :=
    let c' : CokernelCofork (𝟙 Y - (𝟙 Y - retraction f ≫ f)) :=
      CokernelCofork.ofπ (Cofork.π c)
        (by
          simp )
    let i' : IsColimit c' :=
      isCokernelEpiComp i (retraction f)
        (by
          simp )
    let i'' := isColimitCoforkOfCokernelCofork i'
    (splitEpiOfIdempotentOfIsColimitCofork C
        (by
          simp )
        i'').section_
  inl_fst' := by
    simp
  inl_snd' := by
    simp
  inr_fst' := by
    dsimp' only
    rw [split_epi_of_idempotent_of_is_colimit_cofork_section_, is_colimit_cofork_of_cokernel_cofork_desc,
      is_cokernel_epi_comp_desc]
    dsimp' only [← cokernel_cofork_of_cofork_of_π]
    letI := epi_of_is_colimit_cofork i
    apply zero_of_epi_comp c.π
    simp only [← sub_comp, ← comp_sub, ← category.comp_id, ← category.assoc, ← is_split_mono.id, ← sub_self, ←
      cofork.is_colimit.π_desc_assoc, ← cokernel_cofork.π_of_π, ← is_split_mono.id_assoc]
    apply sub_eq_zero_of_eq
    apply category.id_comp
  inr_snd' := by
    apply split_epi.id

/-- The bicone constructed in `binary_bicone_of_split_mono_of_cokernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categories. -/
def isBilimitBinaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f] {c : CokernelCofork f}
    (i : IsColimit c) : (binaryBiconeOfIsSplitMonoOfCokernel i).IsBilimit :=
  isBinaryBilimitOfTotal _
    (by
      simp only [← binary_bicone_of_is_split_mono_of_cokernel_fst, ← binary_bicone_of_is_split_mono_of_cokernel_inr, ←
        binary_bicone_of_is_split_mono_of_cokernel_snd, ← split_epi_of_idempotent_of_is_colimit_cofork_section_]
      dsimp' only [← binary_bicone_of_is_split_mono_of_cokernel_X]
      rw [is_colimit_cofork_of_cokernel_cofork_desc, is_cokernel_epi_comp_desc]
      simp only [← binary_bicone_of_is_split_mono_of_cokernel_inl, ← cofork.is_colimit.π_desc, ←
        cokernel_cofork_of_cofork_π, ← cofork.π_of_π, ← add_sub_cancel'_right])

/-- If `b` is a binary bicone such that `b.inl` is a kernel of `b.snd`, then `b` is a bilimit
    bicone. -/
def BinaryBicone.isBilimitOfKernelInl {X Y : C} (b : BinaryBicone X Y) (hb : IsLimit b.sndKernelFork) : b.IsBilimit :=
  isBinaryBilimitOfIsLimit _ <|
    (BinaryFan.IsLimit.mk _ (fun T f g => f ≫ b.inl + g ≫ b.inr)
        (fun T f g => by
          simp )
        fun T f g => by
        simp )
      fun T f g m h₁ h₂ => by
      have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by
        simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by
        simpa using sub_eq_zero.2 h₂
      obtain ⟨q : T ⟶ X, hq : q ≫ b.inl = m - (f ≫ b.inl + g ≫ b.inr)⟩ := kernel_fork.is_limit.lift' hb _ h₂'
      rw [← sub_eq_zero, ← hq, ← category.comp_id q, ← b.inl_fst, ← category.assoc, hq, h₁', zero_comp]

/-- If `b` is a binary bicone such that `b.inr` is a kernel of `b.fst`, then `b` is a bilimit
    bicone. -/
def BinaryBicone.isBilimitOfKernelInr {X Y : C} (b : BinaryBicone X Y) (hb : IsLimit b.fstKernelFork) : b.IsBilimit :=
  isBinaryBilimitOfIsLimit _ <|
    (BinaryFan.IsLimit.mk _ (fun T f g => f ≫ b.inl + g ≫ b.inr)
        (fun t f g => by
          simp )
        fun t f g => by
        simp )
      fun T f g m h₁ h₂ => by
      have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by
        simpa using sub_eq_zero.2 h₁
      have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by
        simpa using sub_eq_zero.2 h₂
      obtain ⟨q : T ⟶ Y, hq : q ≫ b.inr = m - (f ≫ b.inl + g ≫ b.inr)⟩ := kernel_fork.is_limit.lift' hb _ h₁'
      rw [← sub_eq_zero, ← hq, ← category.comp_id q, ← b.inr_snd, ← category.assoc, hq, h₂', zero_comp]

/-- If `b` is a binary bicone such that `b.fst` is a cokernel of `b.inr`, then `b` is a bilimit
    bicone. -/
def BinaryBicone.isBilimitOfCokernelFst {X Y : C} (b : BinaryBicone X Y) (hb : IsColimit b.inrCokernelCofork) :
    b.IsBilimit :=
  isBinaryBilimitOfIsColimit _ <|
    (BinaryCofan.IsColimit.mk _ (fun T f g => b.fst ≫ f + b.snd ≫ g)
        (fun T f g => by
          simp )
        fun T f g => by
        simp )
      fun T f g m h₁ h₂ => by
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by
        simpa using sub_eq_zero.2 h₁
      have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by
        simpa using sub_eq_zero.2 h₂
      obtain ⟨q : X ⟶ T, hq : b.fst ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ := cokernel_cofork.is_colimit.desc' hb _ h₂'
      rw [← sub_eq_zero, ← hq, ← category.id_comp q, ← b.inl_fst, category.assoc, hq, h₁', comp_zero]

/-- If `b` is a binary bicone such that `b.snd` is a cokernel of `b.inl`, then `b` is a bilimit
    bicone. -/
def BinaryBicone.isBilimitOfCokernelSnd {X Y : C} (b : BinaryBicone X Y) (hb : IsColimit b.inlCokernelCofork) :
    b.IsBilimit :=
  isBinaryBilimitOfIsColimit _ <|
    (BinaryCofan.IsColimit.mk _ (fun T f g => b.fst ≫ f + b.snd ≫ g)
        (fun T f g => by
          simp )
        fun T f g => by
        simp )
      fun T f g m h₁ h₂ => by
      have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by
        simpa using sub_eq_zero.2 h₁
      have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by
        simpa using sub_eq_zero.2 h₂
      obtain ⟨q : Y ⟶ T, hq : b.snd ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ := cokernel_cofork.is_colimit.desc' hb _ h₁'
      rw [← sub_eq_zero, ← hq, ← category.id_comp q, ← b.inr_snd, category.assoc, hq, h₂', comp_zero]

/-- Every split epi `f` with a kernel induces a binary bicone with `f` as its `snd` and
the kernel map as its `inl`.
We will show in `binary_bicone_of_is_split_mono_of_cokernel` that this binary bicone is in fact
already a biproduct. -/
@[simps]
def binaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f] {c : KernelFork f} (i : IsLimit c) :
    BinaryBicone c.x Y :=
  { x,
    fst :=
      let c' : KernelFork (𝟙 X - (𝟙 X - f ≫ section_ f)) :=
        KernelFork.ofι (Fork.ι c)
          (by
            simp )
      let i' : IsLimit c' :=
        isKernelCompMono i (section_ f)
          (by
            simp )
      let i'' := isLimitForkOfKernelFork i'
      (splitMonoOfIdempotentOfIsLimitFork C
          (by
            simp )
          i'').retraction,
    snd := f, inl := c.ι, inr := section_ f,
    inl_fst' := by
      apply split_mono.id,
    inl_snd' := by
      simp ,
    inr_fst' := by
      dsimp' only
      rw [split_mono_of_idempotent_of_is_limit_fork_retraction, is_limit_fork_of_kernel_fork_lift,
        is_kernel_comp_mono_lift]
      dsimp' only [← kernel_fork_of_fork_ι]
      letI := mono_of_is_limit_fork i
      apply zero_of_comp_mono c.ι
      simp only [← comp_sub, ← category.comp_id, ← category.assoc, ← sub_self, ← fork.is_limit.lift_ι, ← fork.ι_of_ι, ←
        is_split_epi.id_assoc],
    inr_snd' := by
      simp }

/-- The bicone constructed in `binary_bicone_of_is_split_epi_of_kernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categories. -/
def isBilimitBinaryBiconeOfIsSplitEpiOfKernel {X Y : C} {f : X ⟶ Y} [IsSplitEpi f] {c : KernelFork f} (i : IsLimit c) :
    (binaryBiconeOfIsSplitEpiOfKernel i).IsBilimit :=
  BinaryBicone.isBilimitOfKernelInl _ <|
    i.ofIsoLimit <|
      Fork.ext (Iso.refl _)
        (by
          simp )

end

section

variable {X Y : C} (f g : X ⟶ Y)

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
theorem biprod.add_eq_lift_id_desc [HasBinaryBiproduct X X] : f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g := by
  simp

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
theorem biprod.add_eq_lift_desc_id [HasBinaryBiproduct Y Y] : f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) := by
  simp

end

end Preadditive

end Limits

open CategoryTheory.Limits

section

attribute [local ext] preadditive

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
instance subsingleton_preadditive_of_has_binary_biproducts {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasBinaryBiproducts C] : Subsingleton (Preadditive C) :=
  Subsingleton.intro fun a b => by
    ext X Y f g
    have h₁ :=
      @biprod.add_eq_lift_id_desc _ _ a _ _ f g
        (by
          convert (inferInstance : has_binary_biproduct X X))
    have h₂ :=
      @biprod.add_eq_lift_id_desc _ _ b _ _ f g
        (by
          convert (inferInstance : has_binary_biproduct X X))
    refine' h₁.trans (Eq.trans _ h₂.symm)
    congr 2 <;> exact Subsingleton.elimₓ _ _

end

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- An object is indecomposable if it cannot be written as the biproduct of two nonzero objects. -/
def Indecomposable (X : C) : Prop :=
  ¬IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z

end CategoryTheory

