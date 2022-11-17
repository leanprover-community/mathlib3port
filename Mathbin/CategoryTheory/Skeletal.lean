/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.CategoryTheory.IsomorphismClasses
import Mathbin.CategoryTheory.Thin

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of an arbitrary category by taking isomorphism classes, and show it is a
skeleton of the original category.

In addition, construct the skeleton of a thin category as a partial ordering, and (noncomputably)
show it is a skeleton of the original category. The advantage of this special case being handled
separately is that lemmas and definitions about orderings can be used directly, for example for the
subobject lattice. In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

variable (C : Type u₁) [Category.{v₁} C]

variable (D : Type u₂) [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

/-- A category is skeletal if isomorphic objects are equal. -/
def Skeletal : Prop :=
  ∀ ⦃X Y : C⦄, IsIsomorphic X Y → X = Y
#align category_theory.skeletal CategoryTheory.Skeletal

/-- `is_skeleton_of C D F` says that `F : D ⥤ C` exhibits `D` as a skeletal full subcategory of `C`,
in particular `F` is a (strong) equivalence and `D` is skeletal.
-/
structure IsSkeletonOf (F : D ⥤ C) where
  skel : Skeletal D
  eqv : IsEquivalence F
#align category_theory.is_skeleton_of CategoryTheory.IsSkeletonOf

attribute [local instance] is_isomorphic_setoid

variable {C D}

/-- If `C` is thin and skeletal, then any naturally isomorphic functors to `C` are equal. -/
theorem Functor.eq_of_iso {F₁ F₂ : D ⥤ C} [Quiver.IsThin C] (hC : Skeletal C) (hF : F₁ ≅ F₂) : F₁ = F₂ :=
  Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elim _ _
#align category_theory.functor.eq_of_iso CategoryTheory.Functor.eq_of_iso

/-- If `C` is thin and skeletal, `D ⥤ C` is skeletal.
`category_theory.functor_thin` shows it is thin also.
-/
theorem functor_skeletal [Quiver.IsThin C] (hC : Skeletal C) : Skeletal (D ⥤ C) := fun F₁ F₂ h =>
  h.elim (Functor.eq_of_iso hC)
#align category_theory.functor_skeletal CategoryTheory.functor_skeletal

variable (C D)

/-- Construct the skeleton category as the induced category on the isomorphism classes, and derive
its category structure.
-/
def Skeleton : Type u₁ :=
  InducedCategory C Quotient.out deriving Category
#align category_theory.skeleton CategoryTheory.Skeleton

instance [Inhabited C] : Inhabited (Skeleton C) :=
  ⟨⟦default⟧⟩

/-- The functor from the skeleton of `C` to `C`. -/
@[simps]
noncomputable def fromSkeleton : Skeleton C ⥤ C :=
  inducedFunctor _ deriving Full, Faithful
#align category_theory.from_skeleton CategoryTheory.fromSkeleton

instance : EssSurj (fromSkeleton C) where mem_ess_image X := ⟨Quotient.mk'' X, Quotient.mk_out X⟩

noncomputable instance : IsEquivalence (fromSkeleton C) :=
  Equivalence.ofFullyFaithfullyEssSurj (fromSkeleton C)

/-- The equivalence between the skeleton and the category itself. -/
noncomputable def skeletonEquivalence : Skeleton C ≌ C :=
  (fromSkeleton C).asEquivalence
#align category_theory.skeleton_equivalence CategoryTheory.skeletonEquivalence

theorem skeleton_skeletal : Skeletal (Skeleton C) := by
  rintro X Y ⟨h⟩
  have : X.out ≈ Y.out := ⟨(from_skeleton C).mapIso h⟩
  simpa using Quotient.sound this
#align category_theory.skeleton_skeletal CategoryTheory.skeleton_skeletal

/-- The `skeleton` of `C` given by choice is a skeleton of `C`. -/
noncomputable def skeletonIsSkeleton : IsSkeletonOf C (Skeleton C) (fromSkeleton C) where
  skel := skeleton_skeletal C
  eqv := fromSkeleton.isEquivalence C
#align category_theory.skeleton_is_skeleton CategoryTheory.skeletonIsSkeleton

section

variable {C D}

/-- Two categories which are categorically equivalent have skeletons with equivalent objects.
-/
noncomputable def Equivalence.skeletonEquiv (e : C ≌ D) : Skeleton C ≃ Skeleton D :=
  let f := ((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm
  { toFun := f.Functor.obj, invFun := f.inverse.obj, left_inv := fun X => skeleton_skeletal C ⟨(f.unitIso.app X).symm⟩,
    right_inv := fun Y => skeleton_skeletal D ⟨f.counitIso.app Y⟩ }
#align category_theory.equivalence.skeleton_equiv CategoryTheory.Equivalence.skeletonEquiv

end

/-- Construct the skeleton category by taking the quotient of objects. This construction gives a
preorder with nice definitional properties, but is only really appropriate for thin categories.
If your original category is not thin, you probably want to be using `skeleton` instead of this.
-/
def ThinSkeleton : Type u₁ :=
  Quotient (isIsomorphicSetoid C)
#align category_theory.thin_skeleton CategoryTheory.ThinSkeleton

instance inhabitedThinSkeleton [Inhabited C] : Inhabited (ThinSkeleton C) :=
  ⟨Quotient.mk'' default⟩
#align category_theory.inhabited_thin_skeleton CategoryTheory.inhabitedThinSkeleton

instance ThinSkeleton.preorder : Preorder (ThinSkeleton C) where
  le :=
    Quotient.lift₂ (fun X Y => Nonempty (X ⟶ Y))
      (by
        rintro _ _ _ _ ⟨i₁⟩ ⟨i₂⟩
        exact propext ⟨Nonempty.map fun f => i₁.inv ≫ f ≫ i₂.hom, Nonempty.map fun f => i₁.hom ≫ f ≫ i₂.inv⟩)
  le_refl := by
    refine' Quotient.ind fun a => _
    exact ⟨𝟙 _⟩
  le_trans a b c := Quotient.induction_on₃ a b c $ fun A B C => Nonempty.map2 (· ≫ ·)
#align category_theory.thin_skeleton.preorder CategoryTheory.ThinSkeleton.preorder

/-- The functor from a category to its thin skeleton. -/
@[simps]
def toThinSkeleton : C ⥤ ThinSkeleton C where
  obj := Quotient.mk''
  map X Y f := homOfLe (Nonempty.intro f)
#align category_theory.to_thin_skeleton CategoryTheory.toThinSkeleton

/-!
The constructions here are intended to be used when the category `C` is thin, even though
some of the statements can be shown without this assumption.
-/


namespace ThinSkeleton

/-- The thin skeleton is thin. -/
instance thin : Quiver.IsThin (ThinSkeleton C) := fun _ _ =>
  ⟨by
    rintro ⟨⟨f₁⟩⟩ ⟨⟨f₂⟩⟩
    rfl⟩
#align category_theory.thin_skeleton.thin CategoryTheory.ThinSkeleton.thin

variable {C} {D}

/-- A functor `C ⥤ D` computably lowers to a functor `thin_skeleton C ⥤ thin_skeleton D`. -/
@[simps]
def map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where
  obj := Quotient.map F.obj $ fun X₁ X₂ ⟨hX⟩ => ⟨F.mapIso hX⟩
  map X Y := Quotient.recOnSubsingleton₂ X Y $ fun x y k => homOfLe (k.le.elim fun t => ⟨F.map t⟩)
#align category_theory.thin_skeleton.map CategoryTheory.ThinSkeleton.map

theorem comp_to_thin_skeleton (F : C ⥤ D) : F ⋙ toThinSkeleton D = toThinSkeleton C ⋙ map F :=
  rfl
#align category_theory.thin_skeleton.comp_to_thin_skeleton CategoryTheory.ThinSkeleton.comp_to_thin_skeleton

/-- Given a natural transformation `F₁ ⟶ F₂`, induce a natural transformation `map F₁ ⟶ map F₂`.-/
def mapNatTrans {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) :
    map F₁ ⟶ map F₂ where app X := Quotient.recOnSubsingleton X fun x => ⟨⟨⟨k.app x⟩⟩⟩
#align category_theory.thin_skeleton.map_nat_trans CategoryTheory.ThinSkeleton.mapNatTrans

-- TODO: state the lemmas about what happens when you compose with `to_thin_skeleton`
/-- A functor `C ⥤ D ⥤ E` computably lowers to a functor
`thin_skeleton C ⥤ thin_skeleton D ⥤ thin_skeleton E` -/
@[simps]
def map₂ (F : C ⥤ D ⥤ E) : ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E where
  obj x :=
    { obj := fun y =>
        Quotient.map₂ (fun X Y => (F.obj X).obj Y)
          (fun X₁ X₂ ⟨hX⟩ Y₁ Y₂ ⟨hY⟩ => ⟨(F.obj X₁).mapIso hY ≪≫ (F.mapIso hX).app Y₂⟩) x y,
      map := fun y₁ y₂ =>
        Quotient.recOnSubsingleton x $ fun X =>
          Quotient.recOnSubsingleton₂ y₁ y₂ $ fun Y₁ Y₂ hY => homOfLe (hY.le.elim fun g => ⟨(F.obj X).map g⟩) }
  map x₁ x₂ :=
    Quotient.recOnSubsingleton₂ x₁ x₂ $ fun X₁ X₂ f =>
      { app := fun y => Quotient.recOnSubsingleton y fun Y => homOfLe (f.le.elim fun f' => ⟨(F.map f').app Y⟩) }
#align category_theory.thin_skeleton.map₂ CategoryTheory.ThinSkeleton.map₂

variable (C)

section

variable [Quiver.IsThin C]

instance to_thin_skeleton_faithful : Faithful (toThinSkeleton C) where
#align category_theory.thin_skeleton.to_thin_skeleton_faithful CategoryTheory.ThinSkeleton.to_thin_skeleton_faithful

/-- Use `quotient.out` to create a functor out of the thin skeleton. -/
@[simps]
noncomputable def fromThinSkeleton : ThinSkeleton C ⥤ C where
  obj := Quotient.out
  map x y :=
    Quotient.recOnSubsingleton₂ x y $ fun X Y f =>
      (Nonempty.some (Quotient.mk_out X)).Hom ≫ f.le.some ≫ (Nonempty.some (Quotient.mk_out Y)).inv
#align category_theory.thin_skeleton.from_thin_skeleton CategoryTheory.ThinSkeleton.fromThinSkeleton

noncomputable instance fromThinSkeletonEquivalence : IsEquivalence (fromThinSkeleton C) where
  inverse := toThinSkeleton C
  counitIso := NatIso.ofComponents (fun X => Nonempty.some (Quotient.mk_out X)) (by tidy)
  unitIso :=
    NatIso.ofComponents
      (fun x =>
        Quotient.recOnSubsingleton x fun X => eqToIso (Quotient.sound ⟨(Nonempty.some (Quotient.mk_out X)).symm⟩))
      (by tidy)
#align
  category_theory.thin_skeleton.from_thin_skeleton_equivalence CategoryTheory.ThinSkeleton.fromThinSkeletonEquivalence

/-- The equivalence between the thin skeleton and the category itself. -/
noncomputable def equivalence : ThinSkeleton C ≌ C :=
  (fromThinSkeleton C).asEquivalence
#align category_theory.thin_skeleton.equivalence CategoryTheory.ThinSkeleton.equivalence

variable {C}

theorem equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
  ⟨isoOfBothWays f g⟩
#align category_theory.thin_skeleton.equiv_of_both_ways CategoryTheory.ThinSkeleton.equiv_of_both_ways

instance thinSkeletonPartialOrder : PartialOrder (ThinSkeleton C) :=
  { CategoryTheory.ThinSkeleton.preorder C with
    le_antisymm :=
      Quotient.ind₂
        (by
          rintro _ _ ⟨f⟩ ⟨g⟩
          apply Quotient.sound (equiv_of_both_ways f g)) }
#align category_theory.thin_skeleton.thin_skeleton_partial_order CategoryTheory.ThinSkeleton.thinSkeletonPartialOrder

theorem skeletal : Skeletal (ThinSkeleton C) := fun X Y =>
  Quotient.induction_on₂ X Y $ fun x y h => h.elim $ fun i => i.1.le.antisymm i.2.le
#align category_theory.thin_skeleton.skeletal CategoryTheory.ThinSkeleton.skeletal

theorem map_comp_eq (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G :=
  Functor.eq_of_iso skeletal $ NatIso.ofComponents (fun X => Quotient.recOnSubsingleton X fun x => Iso.refl _) (by tidy)
#align category_theory.thin_skeleton.map_comp_eq CategoryTheory.ThinSkeleton.map_comp_eq

theorem map_id_eq : map (𝟭 C) = 𝟭 (ThinSkeleton C) :=
  Functor.eq_of_iso skeletal $ NatIso.ofComponents (fun X => Quotient.recOnSubsingleton X fun x => Iso.refl _) (by tidy)
#align category_theory.thin_skeleton.map_id_eq CategoryTheory.ThinSkeleton.map_id_eq

theorem map_iso_eq {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂ :=
  Functor.eq_of_iso skeletal { Hom := mapNatTrans h.Hom, inv := mapNatTrans h.inv }
#align category_theory.thin_skeleton.map_iso_eq CategoryTheory.ThinSkeleton.map_iso_eq

/-- `from_thin_skeleton C` exhibits the thin skeleton as a skeleton. -/
noncomputable def thinSkeletonIsSkeleton : IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C) where
  skel := skeletal
  eqv := ThinSkeleton.fromThinSkeletonEquivalence C
#align category_theory.thin_skeleton.thin_skeleton_is_skeleton CategoryTheory.ThinSkeleton.thinSkeletonIsSkeleton

noncomputable instance isSkeletonOfInhabited : Inhabited (IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C)) :=
  ⟨thinSkeletonIsSkeleton⟩
#align category_theory.thin_skeleton.is_skeleton_of_inhabited CategoryTheory.ThinSkeleton.isSkeletonOfInhabited

end

variable {C}

/-- An adjunction between thin categories gives an adjunction between their thin skeletons. -/
def lowerAdjunction (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R) : ThinSkeleton.map L ⊣ ThinSkeleton.map R :=
  Adjunction.mkOfUnitCounit
    { Unit :=
        { app := fun X => by
            letI := is_isomorphic_setoid C
            refine'
              Quotient.recOnSubsingleton X fun x =>
                hom_of_le ⟨h.unit.app x⟩ },-- TODO: make quotient.rec_on_subsingleton' so the letI isn't needed
      counit :=
        { app := fun X => by
            letI := is_isomorphic_setoid D
            refine' Quotient.recOnSubsingleton X fun x => hom_of_le ⟨h.counit.app x⟩ } }
#align category_theory.thin_skeleton.lower_adjunction CategoryTheory.ThinSkeleton.lowerAdjunction

end ThinSkeleton

open ThinSkeleton

section

variable {C} {α : Type _} [PartialOrder α]

/-- When `e : C ≌ α` is a categorical equivalence from a thin category `C` to some partial order `α`,
the `thin_skeleton C` is order isomorphic to `α`.
-/
noncomputable def Equivalence.thinSkeletonOrderIso [Quiver.IsThin C] (e : C ≌ α) : ThinSkeleton C ≃o α :=
  ((ThinSkeleton.equivalence C).trans e).toOrderIso
#align category_theory.equivalence.thin_skeleton_order_iso CategoryTheory.Equivalence.thinSkeletonOrderIso

end

end CategoryTheory

