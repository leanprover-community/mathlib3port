import Mathbin.Logic.Small 
import Mathbin.CategoryTheory.Skeletal

/-!
# Essentially small categories.

A category given by `(C : Type u) [category.{v} C]` is `w`-essentially small
if there exists a `small_model C : Type w` equipped with `[small_category (small_model C)]`.

A category is `w`-locally small if every hom type is `w`-small.

The main theorem here is that a category is `w`-essentially small iff
the type `skeleton C` is `w`-small, and `C` is `w`-locally small.
-/


universe w v v' u u'

open CategoryTheory

variable (C : Type u) [category.{v} C]

namespace CategoryTheory

/-- A category is `essentially_small.{w}` if there exists
an equivalence to some `S : Type w` with `[small_category S]`. -/
class essentially_small (C : Type u) [category.{v} C] : Prop where 
  equiv_small_category :
  ∃ (S : Type w)(_ : small_category S),
    by 
      exact Nonempty (C ≌ S)

/-- Constructor for `essentially_small C` from an explicit small category witness. -/
theorem essentially_small.mk' {C : Type u} [category.{v} C] {S : Type w} [small_category S] (e : C ≌ S) :
  essentially_small.{w} C :=
  ⟨⟨S, _, ⟨e⟩⟩⟩

/--
An arbitrarily chosen small model for an essentially small category.
-/
@[nolint has_inhabited_instance]
def small_model (C : Type u) [category.{v} C] [essentially_small.{w} C] : Type w :=
  Classical.some (@essentially_small.equiv_small_category C _ _)

noncomputable instance small_category_small_model (C : Type u) [category.{v} C] [essentially_small.{w} C] :
  small_category (small_model C) :=
  Classical.some (Classical.some_spec (@essentially_small.equiv_small_category C _ _))

/--
The (noncomputable) categorical equivalence between
an essentially small category and its small model.
-/
noncomputable def equiv_small_model (C : Type u) [category.{v} C] [essentially_small.{w} C] : C ≌ small_model C :=
  Nonempty.some (Classical.some_spec (Classical.some_spec (@essentially_small.equiv_small_category C _ _)))

theorem essentially_small_congr {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D] (e : C ≌ D) :
  essentially_small.{w} C ↔ essentially_small.{w} D :=
  by 
    fconstructor
    ·
      rintro ⟨S, 𝒮, ⟨f⟩⟩
      skip 
      exact essentially_small.mk' (e.symm.trans f)
    ·
      rintro ⟨S, 𝒮, ⟨f⟩⟩
      skip 
      exact essentially_small.mk' (e.trans f)

/--
A category is `w`-locally small if every hom set is `w`-small.

See `shrink_homs C` for a category instance where every hom set has been replaced by a small model.
-/
class locally_small (C : Type u) [category.{v} C] : Prop where 
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y) :=  by 
  runTac 
    tactic.apply_instance

instance (C : Type u) [category.{v} C] [locally_small.{w} C] (X Y : C) : Small (X ⟶ Y) :=
  locally_small.hom_small X Y

theorem locally_small_congr {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D] (e : C ≌ D) :
  locally_small.{w} C ↔ locally_small.{w} D :=
  by 
    fconstructor
    ·
      rintro ⟨L⟩
      fconstructor 
      intro X Y 
      specialize L (e.inverse.obj X) (e.inverse.obj Y)
      refine' (small_congr _).mpr L 
      exact equiv_of_fully_faithful e.inverse
    ·
      rintro ⟨L⟩
      fconstructor 
      intro X Y 
      specialize L (e.functor.obj X) (e.functor.obj Y)
      refine' (small_congr _).mpr L 
      exact equiv_of_fully_faithful e.functor

instance (priority := 100) locally_small_self (C : Type u) [category.{v} C] : locally_small.{v} C :=
  {  }

instance (priority := 100) locally_small_of_essentially_small (C : Type u) [category.{v} C] [essentially_small.{w} C] :
  locally_small.{w} C :=
  (locally_small_congr (equiv_small_model C)).mpr (CategoryTheory.locally_small_self _)

/--
We define a type alias `shrink_homs C` for `C`. When we have `locally_small.{w} C`,
we'll put a `category.{w}` instance on `shrink_homs C`.
-/
@[nolint has_inhabited_instance]
def shrink_homs (C : Type u) :=
  C

namespace ShrinkHoms

section 

variable {C' : Type _}

/-- Help the typechecker by explicitly translating from `C` to `shrink_homs C`. -/
def to_shrink_homs {C' : Type _} (X : C') : shrink_homs C' :=
  X

/-- Help the typechecker by explicitly translating from `shrink_homs C` to `C`. -/
def from_shrink_homs {C' : Type _} (X : shrink_homs C') : C' :=
  X

@[simp]
theorem to_from (X : C') : from_shrink_homs (to_shrink_homs X) = X :=
  rfl

@[simp]
theorem from_to (X : shrink_homs C') : to_shrink_homs (from_shrink_homs X) = X :=
  rfl

end 

variable (C) [locally_small.{w} C]

@[simps]
noncomputable instance : category.{w} (shrink_homs C) :=
  { Hom := fun X Y => Shrink (from_shrink_homs X ⟶ from_shrink_homs Y),
    id := fun X => equivShrink _ (𝟙 (from_shrink_homs X)),
    comp := fun X Y Z f g => equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g) }

/-- Implementation of `shrink_homs.equivalence`. -/
@[simps]
noncomputable def Functor : C ⥤ shrink_homs C :=
  { obj := fun X => to_shrink_homs X, map := fun X Y f => equivShrink (X ⟶ Y) f }

/-- Implementation of `shrink_homs.equivalence`. -/
@[simps]
noncomputable def inverse : shrink_homs C ⥤ C :=
  { obj := fun X => from_shrink_homs X,
    map := fun X Y f => (equivShrink (from_shrink_homs X ⟶ from_shrink_homs Y)).symm f }

/--
The categorical equivalence between `C` and `shrink_homs C`, when `C` is locally small.
-/
@[simps]
noncomputable def Equivalenceₓ : C ≌ shrink_homs C :=
  equivalence.mk (Functor C) (inverse C)
    (nat_iso.of_components (fun X => iso.refl X)
      (by 
        tidy))
    (nat_iso.of_components (fun X => iso.refl X)
      (by 
        tidy))

end ShrinkHoms

/--
A category is essentially small if and only if
the underlying type of its skeleton (i.e. the "set" of isomorphism classes) is small,
and it is locally small.
-/
theorem essentially_small_iff (C : Type u) [category.{v} C] :
  essentially_small.{w} C ↔ Small.{w} (skeleton C) ∧ locally_small.{w} C :=
  by 
    fconstructor
    ·
      intro h 
      fconstructor
      ·
        rcases h with ⟨S, 𝒮, ⟨e⟩⟩
        skip 
        refine' ⟨⟨skeleton S, ⟨_⟩⟩⟩
        exact e.skeleton_equiv
      ·
        skip 
        infer_instance
    ·
      rintro ⟨⟨S, ⟨e⟩⟩, L⟩
      skip 
      let e' := (shrink_homs.equivalence C).skeletonEquiv.symm 
      refine' ⟨⟨S, _, ⟨_⟩⟩⟩
      apply induced_category.category (e'.trans e).symm 
      refine'
        (shrink_homs.equivalence C).trans
          ((skeleton_equivalence _).symm.trans (induced_functor (e'.trans e).symm).asEquivalence.symm)

/--
Any thin category is locally small.
-/
instance (priority := 100) locally_small_of_thin {C : Type u} [category.{v} C] [∀ X Y : C, Subsingleton (X ⟶ Y)] :
  locally_small.{w} C :=
  {  }

/--
A thin category is essentially small if and only if the underlying type of its skeleton is small.
-/
theorem essentially_small_iff_of_thin {C : Type u} [category.{v} C] [∀ X Y : C, Subsingleton (X ⟶ Y)] :
  essentially_small.{w} C ↔ Small.{w} (skeleton C) :=
  by 
    simp [essentially_small_iff, CategoryTheory.locally_small_of_thin]

end CategoryTheory

