/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import CategoryTheory.FinCategory
import CategoryTheory.Limits.Cones
import CategoryTheory.Adjunction.Basic
import CategoryTheory.Category.Preorder
import CategoryTheory.Category.Ulift

#align_import category_theory.filtered from "leanprover-community/mathlib"@"ee05e9ce1322178f0c12004eb93c00d2c8c00ed2"

/-!
# Filtered categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

Filtered colimits are often better behaved than arbitrary colimits.
See `category_theory/limits/types` for some details.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and more often preserved by functors).

In this file we show that any functor from a finite category to a filtered category admits a cocone:
* `cocone_nonempty [fin_category J] [is_filtered C] (F : J ⥤ C) : nonempty (cocone F)`
More generally,
for any finite collection of objects and morphisms between them in a filtered category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
This formulation is often more useful in practice and is available via `sup_exists`,
which takes a finset of objects, and an indexed family (indexed by source and target)
of finsets of morphisms.

Furthermore, we give special support for two diagram categories: The `bowtie` and the `tulip`.
This is because these shapes show up in the proofs that forgetful functors of algebraic categories
(e.g. `Mon`, `CommRing`, ...) preserve filtered colimits.

All of the above API, except for the `bowtie` and the `tulip`, is also provided for cofiltered
categories.

## See also
In `category_theory.limits.filtered_colimit_commutes_finite_limit` we show that filtered colimits
commute with finite limits.

-/


open Function

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe w v v₁ u u₁ u₂

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

#print CategoryTheory.IsFilteredOrEmpty /-
/-- A category `is_filtered_or_empty` if
1. for every pair of objects there exists another object "to the right", and
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal.
-/
class IsFilteredOrEmpty : Prop where
  cocone_objs : ∀ X Y : C, ∃ (Z : _) (f : X ⟶ Z) (g : Y ⟶ Z), True
  cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (Z : _) (h : Y ⟶ Z), f ≫ h = g ≫ h
#align category_theory.is_filtered_or_empty CategoryTheory.IsFilteredOrEmpty
-/

#print CategoryTheory.IsFiltered /-
/-- A category `is_filtered` if
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

See <https://stacks.math.columbia.edu/tag/002V>. (They also define a diagram being filtered.)
-/
class IsFiltered extends IsFilteredOrEmpty C : Prop where
  [Nonempty : Nonempty C]
#align category_theory.is_filtered CategoryTheory.IsFiltered
-/

#print CategoryTheory.isFilteredOrEmpty_of_semilatticeSup /-
instance (priority := 100) isFilteredOrEmpty_of_semilatticeSup (α : Type u) [SemilatticeSup α] :
    IsFilteredOrEmpty α
    where
  cocone_objs X Y := ⟨X ⊔ Y, homOfLE le_sup_left, homOfLE le_sup_right, trivial⟩
  cocone_maps X Y f g := ⟨Y, 𝟙 _, by ext⟩
#align category_theory.is_filtered_or_empty_of_semilattice_sup CategoryTheory.isFilteredOrEmpty_of_semilatticeSup
-/

#print CategoryTheory.isFiltered_of_semilatticeSup_nonempty /-
instance (priority := 100) isFiltered_of_semilatticeSup_nonempty (α : Type u) [SemilatticeSup α]
    [Nonempty α] : IsFiltered α where
#align category_theory.is_filtered_of_semilattice_sup_nonempty CategoryTheory.isFiltered_of_semilatticeSup_nonempty
-/

#print CategoryTheory.isFilteredOrEmpty_of_directed_le /-
instance (priority := 100) isFilteredOrEmpty_of_directed_le (α : Type u) [Preorder α]
    [IsDirected α (· ≤ ·)] : IsFilteredOrEmpty α
    where
  cocone_objs X Y :=
    let ⟨Z, h1, h2⟩ := exists_ge_ge X Y
    ⟨Z, homOfLE h1, homOfLE h2, trivial⟩
  cocone_maps X Y f g := ⟨Y, 𝟙 _, by simp⟩
#align category_theory.is_filtered_or_empty_of_directed_le CategoryTheory.isFilteredOrEmpty_of_directed_le
-/

#print CategoryTheory.isFiltered_of_directed_le_nonempty /-
instance (priority := 100) isFiltered_of_directed_le_nonempty (α : Type u) [Preorder α]
    [IsDirected α (· ≤ ·)] [Nonempty α] : IsFiltered α where
#align category_theory.is_filtered_of_directed_le_nonempty CategoryTheory.isFiltered_of_directed_le_nonempty
-/

-- Sanity checks
example (α : Type u) [SemilatticeSup α] [OrderBot α] : IsFiltered α := by infer_instance

example (α : Type u) [SemilatticeSup α] [OrderTop α] : IsFiltered α := by infer_instance

instance : IsFiltered (Discrete PUnit)
    where
  cocone_objs X Y := ⟨⟨PUnit.unit⟩, ⟨⟨by decide⟩⟩, ⟨⟨by decide⟩⟩, trivial⟩
  cocone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by decide⟩⟩, by decide⟩
  Nonempty := ⟨⟨PUnit.unit⟩⟩

namespace IsFiltered

section AllowEmpty

variable {C} [IsFilteredOrEmpty C]

theorem cocone_objs : ∀ X Y : C, ∃ (Z : _) (f : X ⟶ Z) (g : Y ⟶ Z), True :=
  IsFilteredOrEmpty.cocone_objs
#align category_theory.is_filtered.cocone_objs CategoryTheory.IsFiltered.cocone_objs

theorem cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (Z : _) (h : Y ⟶ Z), f ≫ h = g ≫ h :=
  IsFilteredOrEmpty.cocone_maps
#align category_theory.is_filtered.cocone_maps CategoryTheory.IsFiltered.cocone_maps

#print CategoryTheory.IsFiltered.max /-
/-- `max j j'` is an arbitrary choice of object to the right of both `j` and `j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def max (j j' : C) : C :=
  (cocone_objs j j').some
#align category_theory.is_filtered.max CategoryTheory.IsFiltered.max
-/

#print CategoryTheory.IsFiltered.leftToMax /-
/-- `left_to_max j j'` is an arbitrary choice of morphism from `j` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def leftToMax (j j' : C) : j ⟶ max j j' :=
  (cocone_objs j j').choose_spec.some
#align category_theory.is_filtered.left_to_max CategoryTheory.IsFiltered.leftToMax
-/

#print CategoryTheory.IsFiltered.rightToMax /-
/-- `right_to_max j j'` is an arbitrary choice of morphism from `j'` to `max j j'`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def rightToMax (j j' : C) : j' ⟶ max j j' :=
  (cocone_objs j j').choose_spec.choose_spec.some
#align category_theory.is_filtered.right_to_max CategoryTheory.IsFiltered.rightToMax
-/

#print CategoryTheory.IsFiltered.coeq /-
/-- `coeq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq {j j' : C} (f f' : j ⟶ j') : C :=
  (cocone_maps f f').some
#align category_theory.is_filtered.coeq CategoryTheory.IsFiltered.coeq
-/

#print CategoryTheory.IsFiltered.coeqHom /-
/-- `coeq_hom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`coeq_hom f f' : j' ⟶ coeq f f'` such that
`coeq_condition : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeqHom {j j' : C} (f f' : j ⟶ j') : j' ⟶ coeq f f' :=
  (cocone_maps f f').choose_spec.some
#align category_theory.is_filtered.coeq_hom CategoryTheory.IsFiltered.coeqHom
-/

#print CategoryTheory.IsFiltered.coeq_condition /-
/-- `coeq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`f ≫ coeq_hom f f' = f' ≫ coeq_hom f f'`.
-/
@[simp, reassoc]
theorem coeq_condition {j j' : C} (f f' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f' :=
  (cocone_maps f f').choose_spec.choose_spec
#align category_theory.is_filtered.coeq_condition CategoryTheory.IsFiltered.coeq_condition
-/

end AllowEmpty

section Nonempty

open CategoryTheory.Limits

variable {C} [IsFiltered C]

#print CategoryTheory.IsFiltered.sup_objs_exists /-
/-- Any finite collection of objects in a filtered category has an object "to the right".
-/
theorem sup_objs_exists (O : Finset C) : ∃ S : C, ∀ {X}, X ∈ O → Nonempty (X ⟶ S) := by classical
#align category_theory.is_filtered.sup_objs_exists CategoryTheory.IsFiltered.sup_objs_exists
-/

variable (O : Finset C) (H : Finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y))

#print CategoryTheory.IsFiltered.sup_exists /-
/-- Given any `finset` of objects `{X, ...}` and
indexed collection of `finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : X ⟶ S` from each `X`,
such that the triangles commute: `f ≫ T Y = T X`, for `f : X ⟶ Y` in the `finset`.
-/
theorem sup_exists :
    ∃ (S : C) (T : ∀ {X : C}, X ∈ O → (X ⟶ S)),
      ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
        (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H → f ≫ T mY = T mX :=
  by classical
#align category_theory.is_filtered.sup_exists CategoryTheory.IsFiltered.sup_exists
-/

#print CategoryTheory.IsFiltered.sup /-
/-- An arbitrary choice of object "to the right"
of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/
noncomputable def sup : C :=
  (sup_exists O H).some
#align category_theory.is_filtered.sup CategoryTheory.IsFiltered.sup
-/

#print CategoryTheory.IsFiltered.toSup /-
/-- The morphisms to `sup O H`.
-/
noncomputable def toSup {X : C} (m : X ∈ O) : X ⟶ sup O H :=
  (sup_exists O H).choose_spec.some m
#align category_theory.is_filtered.to_sup CategoryTheory.IsFiltered.toSup
-/

#print CategoryTheory.IsFiltered.toSup_commutes /-
/-- The triangles of consisting of a morphism in `H` and the maps to `sup O H` commute.
-/
theorem toSup_commutes {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
    (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H) :
    f ≫ toSup O H mY = toSup O H mX :=
  (sup_exists O H).choose_spec.choose_spec mX mY mf
#align category_theory.is_filtered.to_sup_commutes CategoryTheory.IsFiltered.toSup_commutes
-/

variable {J : Type v} [SmallCategory J] [FinCategory J]

#print CategoryTheory.IsFiltered.cocone_nonempty /-
/-- If we have `is_filtered C`, then for any functor `F : J ⥤ C` with `fin_category J`,
there exists a cocone over `F`.
-/
theorem cocone_nonempty (F : J ⥤ C) : Nonempty (Cocone F) := by classical
#align category_theory.is_filtered.cocone_nonempty CategoryTheory.IsFiltered.cocone_nonempty
-/

#print CategoryTheory.IsFiltered.cocone /-
/-- An arbitrary choice of cocone over `F : J ⥤ C`, for `fin_category J` and `is_filtered C`.
-/
noncomputable def cocone (F : J ⥤ C) : Cocone F :=
  (cocone_nonempty F).some
#align category_theory.is_filtered.cocone CategoryTheory.IsFiltered.cocone
-/

variable {D : Type u₁} [Category.{v₁} D]

#print CategoryTheory.IsFiltered.of_right_adjoint /-
/-- If `C` is filtered, and we have a functor `R : C ⥤ D` with a left adjoint, then `D` is filtered.
-/
theorem of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : IsFiltered D :=
  { cocone_objs := fun X Y =>
      ⟨_, h.homEquiv _ _ (leftToMax _ _), h.homEquiv _ _ (rightToMax _ _), ⟨⟩⟩
    cocone_maps := fun X Y f g =>
      ⟨_, h.homEquiv _ _ (coeqHom _ _), by
        rw [← h.hom_equiv_naturality_left, ← h.hom_equiv_naturality_left, coeq_condition]⟩
    Nonempty := IsFiltered.nonempty.map R.obj }
#align category_theory.is_filtered.of_right_adjoint CategoryTheory.IsFiltered.of_right_adjoint
-/

#print CategoryTheory.IsFiltered.of_isRightAdjoint /-
/-- If `C` is filtered, and we have a right adjoint functor `R : C ⥤ D`, then `D` is filtered. -/
theorem of_isRightAdjoint (R : C ⥤ D) [IsRightAdjoint R] : IsFiltered D :=
  of_right_adjoint (Adjunction.ofRightAdjoint R)
#align category_theory.is_filtered.of_is_right_adjoint CategoryTheory.IsFiltered.of_isRightAdjoint
-/

#print CategoryTheory.IsFiltered.of_equivalence /-
/-- Being filtered is preserved by equivalence of categories. -/
theorem of_equivalence (h : C ≌ D) : IsFiltered D :=
  of_right_adjoint h.symm.toAdjunction
#align category_theory.is_filtered.of_equivalence CategoryTheory.IsFiltered.of_equivalence
-/

end Nonempty

section SpecialShapes

variable {C} [IsFilteredOrEmpty C]

#print CategoryTheory.IsFiltered.max₃ /-
/-- `max₃ j₁ j₂ j₃` is an arbitrary choice of object to the right of `j₁`, `j₂` and `j₃`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def max₃ (j₁ j₂ j₃ : C) : C :=
  max (max j₁ j₂) j₃
#align category_theory.is_filtered.max₃ CategoryTheory.IsFiltered.max₃
-/

#print CategoryTheory.IsFiltered.firstToMax₃ /-
/-- `first_to_max₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₁` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def firstToMax₃ (j₁ j₂ j₃ : C) : j₁ ⟶ max₃ j₁ j₂ j₃ :=
  leftToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃
#align category_theory.is_filtered.first_to_max₃ CategoryTheory.IsFiltered.firstToMax₃
-/

#print CategoryTheory.IsFiltered.secondToMax₃ /-
/-- `second_to_max₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₂` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def secondToMax₃ (j₁ j₂ j₃ : C) : j₂ ⟶ max₃ j₁ j₂ j₃ :=
  rightToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃
#align category_theory.is_filtered.second_to_max₃ CategoryTheory.IsFiltered.secondToMax₃
-/

#print CategoryTheory.IsFiltered.thirdToMax₃ /-
/-- `third_to_max₃ j₁ j₂ j₃` is an arbitrary choice of morphism from `j₃` to `max₃ j₁ j₂ j₃`,
whose existence is ensured by `is_filtered`.
-/
noncomputable def thirdToMax₃ (j₁ j₂ j₃ : C) : j₃ ⟶ max₃ j₁ j₂ j₃ :=
  rightToMax (max j₁ j₂) j₃
#align category_theory.is_filtered.third_to_max₃ CategoryTheory.IsFiltered.thirdToMax₃
-/

#print CategoryTheory.IsFiltered.coeq₃ /-
/-- `coeq₃ f g h`, for morphisms `f g h : j₁ ⟶ j₂`, is an arbitrary choice of object
which admits a morphism `coeq₃_hom f g h : j₂ ⟶ coeq₃ f g h` such that
`coeq₃_condition₁`, `coeq₃_condition₂` and `coeq₃_condition₃` are satisfied.
Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : C :=
  coeq (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
    (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))
#align category_theory.is_filtered.coeq₃ CategoryTheory.IsFiltered.coeq₃
-/

#print CategoryTheory.IsFiltered.coeq₃Hom /-
/-- `coeq₃_hom f g h`, for morphisms `f g h : j₁ ⟶ j₂`, is an arbitrary choice of morphism
`j₂ ⟶ coeq₃ f g h` such that `coeq₃_condition₁`, `coeq₃_condition₂` and `coeq₃_condition₃`
are satisfied. Its existence is ensured by `is_filtered`.
-/
noncomputable def coeq₃Hom {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : j₂ ⟶ coeq₃ f g h :=
  coeqHom f g ≫
    leftToMax (coeq f g) (coeq g h) ≫
      coeqHom (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
        (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))
#align category_theory.is_filtered.coeq₃_hom CategoryTheory.IsFiltered.coeq₃Hom
-/

#print CategoryTheory.IsFiltered.coeq₃_condition₁ /-
theorem coeq₃_condition₁ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : f ≫ coeq₃Hom f g h = g ≫ coeq₃Hom f g h :=
  by rw [coeq₃_hom, reassoc_of (coeq_condition f g)]
#align category_theory.is_filtered.coeq₃_condition₁ CategoryTheory.IsFiltered.coeq₃_condition₁
-/

#print CategoryTheory.IsFiltered.coeq₃_condition₂ /-
theorem coeq₃_condition₂ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : g ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h :=
  by
  dsimp [coeq₃_hom]
  slice_lhs 2 4 => rw [← category.assoc, coeq_condition _ _]
  slice_rhs 2 4 => rw [← category.assoc, coeq_condition _ _]
  slice_lhs 1 3 => rw [← category.assoc, coeq_condition _ _]
  simp only [category.assoc]
#align category_theory.is_filtered.coeq₃_condition₂ CategoryTheory.IsFiltered.coeq₃_condition₂
-/

#print CategoryTheory.IsFiltered.coeq₃_condition₃ /-
theorem coeq₃_condition₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : f ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h :=
  Eq.trans (coeq₃_condition₁ f g h) (coeq₃_condition₂ f g h)
#align category_theory.is_filtered.coeq₃_condition₃ CategoryTheory.IsFiltered.coeq₃_condition₃
-/

#print CategoryTheory.IsFiltered.span /-
/-- For every span `j ⟵ i ⟶ j'`, there
   exists a cocone `j ⟶ k ⟵ j'` such that the square commutes. -/
theorem span {i j j' : C} (f : i ⟶ j) (f' : i ⟶ j') :
    ∃ (k : C) (g : j ⟶ k) (g' : j' ⟶ k), f ≫ g = f' ≫ g' :=
  let ⟨K, G, G', _⟩ := cocone_objs j j'
  let ⟨k, e, he⟩ := cocone_maps (f ≫ G) (f' ≫ G')
  ⟨k, G ≫ e, G' ≫ e, by simpa only [← category.assoc]⟩
#align category_theory.is_filtered.span CategoryTheory.IsFiltered.span
-/

#print CategoryTheory.IsFiltered.bowtie /-
/-- Given a "bowtie" of morphisms
```
 j₁   j₂
 |\  /|
 | \/ |
 | /\ |
 |/  \∣
 vv  vv
 k₁  k₂
```
in a filtered category, we can construct an object `s` and two morphisms from `k₁` and `k₂` to `s`,
making the resulting squares commute.
-/
theorem bowtie {j₁ j₂ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁) (g₂ : j₂ ⟶ k₂) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s), f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β :=
  by
  obtain ⟨t, k₁t, k₂t, ht⟩ := span f₁ g₁
  obtain ⟨s, ts, hs⟩ := cocone_maps (f₂ ≫ k₁t) (g₂ ≫ k₂t)
  simp_rw [category.assoc] at hs 
  exact ⟨s, k₁t ≫ ts, k₂t ≫ ts, by rw [reassoc_of ht], hs⟩
#align category_theory.is_filtered.bowtie CategoryTheory.IsFiltered.bowtie
-/

#print CategoryTheory.IsFiltered.tulip /-
/-- Given a "tulip" of morphisms
```
 j₁    j₂    j₃
 |\   / \   / |
 | \ /   \ /  |
 |  vv    vv  |
 \  k₁    k₂ /
  \         /
   \       /
    \     /
     \   /
      v v
       l
```
in a filtered category, we can construct an object `s` and three morphisms from `k₁`, `k₂` and `l`
to `s`, making the resulting squares commute.
-/
theorem tulip {j₁ j₂ j₃ k₁ k₂ l : C} (f₁ : j₁ ⟶ k₁) (f₂ : j₂ ⟶ k₁) (f₃ : j₂ ⟶ k₂) (f₄ : j₃ ⟶ k₂)
    (g₁ : j₁ ⟶ l) (g₂ : j₃ ⟶ l) :
    ∃ (s : C) (α : k₁ ⟶ s) (β : l ⟶ s) (γ : k₂ ⟶ s),
      f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = f₃ ≫ γ ∧ f₄ ≫ γ = g₂ ≫ β :=
  by
  obtain ⟨l', k₁l, k₂l, hl⟩ := span f₂ f₃
  obtain ⟨s, ls, l's, hs₁, hs₂⟩ := bowtie g₁ (f₁ ≫ k₁l) g₂ (f₄ ≫ k₂l)
  refine' ⟨s, k₁l ≫ l's, ls, k₂l ≫ l's, _, by rw [reassoc_of hl], _⟩ <;>
    simp only [hs₁, hs₂, category.assoc]
#align category_theory.is_filtered.tulip CategoryTheory.IsFiltered.tulip
-/

end SpecialShapes

end IsFiltered

#print CategoryTheory.IsCofilteredOrEmpty /-
/-- A category `is_cofiltered_or_empty` if
1. for every pair of objects there exists another object "to the left", and
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal.
-/
class IsCofilteredOrEmpty : Prop where
  cone_objs : ∀ X Y : C, ∃ (W : _) (f : W ⟶ X) (g : W ⟶ Y), True
  cone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (W : _) (h : W ⟶ X), h ≫ f = h ≫ g
#align category_theory.is_cofiltered_or_empty CategoryTheory.IsCofilteredOrEmpty
-/

#print CategoryTheory.IsCofiltered /-
/-- A category `is_cofiltered` if
1. for every pair of objects there exists another object "to the left",
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal, and
3. there exists some object.

See <https://stacks.math.columbia.edu/tag/04AZ>.
-/
class IsCofiltered extends IsCofilteredOrEmpty C : Prop where
  [Nonempty : Nonempty C]
#align category_theory.is_cofiltered CategoryTheory.IsCofiltered
-/

#print CategoryTheory.isCofilteredOrEmpty_of_semilatticeInf /-
instance (priority := 100) isCofilteredOrEmpty_of_semilatticeInf (α : Type u) [SemilatticeInf α] :
    IsCofilteredOrEmpty α
    where
  cone_objs X Y := ⟨X ⊓ Y, homOfLE inf_le_left, homOfLE inf_le_right, trivial⟩
  cone_maps X Y f g := ⟨X, 𝟙 _, by ext⟩
#align category_theory.is_cofiltered_or_empty_of_semilattice_inf CategoryTheory.isCofilteredOrEmpty_of_semilatticeInf
-/

#print CategoryTheory.isCofiltered_of_semilatticeInf_nonempty /-
instance (priority := 100) isCofiltered_of_semilatticeInf_nonempty (α : Type u) [SemilatticeInf α]
    [Nonempty α] : IsCofiltered α where
#align category_theory.is_cofiltered_of_semilattice_inf_nonempty CategoryTheory.isCofiltered_of_semilatticeInf_nonempty
-/

#print CategoryTheory.isCofilteredOrEmpty_of_directed_ge /-
instance (priority := 100) isCofilteredOrEmpty_of_directed_ge (α : Type u) [Preorder α]
    [IsDirected α (· ≥ ·)] : IsCofilteredOrEmpty α
    where
  cone_objs X Y :=
    let ⟨Z, hX, hY⟩ := exists_le_le X Y
    ⟨Z, homOfLE hX, homOfLE hY, trivial⟩
  cone_maps X Y f g := ⟨X, 𝟙 _, by simp⟩
#align category_theory.is_cofiltered_or_empty_of_directed_ge CategoryTheory.isCofilteredOrEmpty_of_directed_ge
-/

#print CategoryTheory.isCofiltered_of_directed_ge_nonempty /-
instance (priority := 100) isCofiltered_of_directed_ge_nonempty (α : Type u) [Preorder α]
    [IsDirected α (· ≥ ·)] [Nonempty α] : IsCofiltered α where
#align category_theory.is_cofiltered_of_directed_ge_nonempty CategoryTheory.isCofiltered_of_directed_ge_nonempty
-/

-- Sanity checks
example (α : Type u) [SemilatticeInf α] [OrderBot α] : IsCofiltered α := by infer_instance

example (α : Type u) [SemilatticeInf α] [OrderTop α] : IsCofiltered α := by infer_instance

instance : IsCofiltered (Discrete PUnit)
    where
  cone_objs X Y := ⟨⟨PUnit.unit⟩, ⟨⟨by decide⟩⟩, ⟨⟨by decide⟩⟩, trivial⟩
  cone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by decide⟩⟩, by decide⟩
  Nonempty := ⟨⟨PUnit.unit⟩⟩

namespace IsCofiltered

section AllowEmpty

variable {C} [IsCofilteredOrEmpty C]

theorem cone_objs : ∀ X Y : C, ∃ (W : _) (f : W ⟶ X) (g : W ⟶ Y), True :=
  IsCofilteredOrEmpty.cone_objs
#align category_theory.is_cofiltered.cone_objs CategoryTheory.IsCofiltered.cone_objs

theorem cone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ (W : _) (h : W ⟶ X), h ≫ f = h ≫ g :=
  IsCofilteredOrEmpty.cone_maps
#align category_theory.is_cofiltered.cone_maps CategoryTheory.IsCofiltered.cone_maps

#print CategoryTheory.IsCofiltered.min /-
/-- `min j j'` is an arbitrary choice of object to the left of both `j` and `j'`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def min (j j' : C) : C :=
  (cone_objs j j').some
#align category_theory.is_cofiltered.min CategoryTheory.IsCofiltered.min
-/

#print CategoryTheory.IsCofiltered.minToLeft /-
/-- `min_to_left j j'` is an arbitrary choice of morphism from `min j j'` to `j`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def minToLeft (j j' : C) : min j j' ⟶ j :=
  (cone_objs j j').choose_spec.some
#align category_theory.is_cofiltered.min_to_left CategoryTheory.IsCofiltered.minToLeft
-/

#print CategoryTheory.IsCofiltered.minToRight /-
/-- `min_to_right j j'` is an arbitrary choice of morphism from `min j j'` to `j'`,
whose existence is ensured by `is_cofiltered`.
-/
noncomputable def minToRight (j j' : C) : min j j' ⟶ j' :=
  (cone_objs j j').choose_spec.choose_spec.some
#align category_theory.is_cofiltered.min_to_right CategoryTheory.IsCofiltered.minToRight
-/

#print CategoryTheory.IsCofiltered.eq /-
/-- `eq f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of object
which admits a morphism `eq_hom f f' : eq f f' ⟶ j` such that
`eq_condition : eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
Its existence is ensured by `is_cofiltered`.
-/
noncomputable def eq {j j' : C} (f f' : j ⟶ j') : C :=
  (cone_maps f f').some
#align category_theory.is_cofiltered.eq CategoryTheory.IsCofiltered.eq
-/

#print CategoryTheory.IsCofiltered.eqHom /-
/-- `eq_hom f f'`, for morphisms `f f' : j ⟶ j'`, is an arbitrary choice of morphism
`eq_hom f f' : eq f f' ⟶ j` such that
`eq_condition : eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
Its existence is ensured by `is_cofiltered`.
-/
noncomputable def eqHom {j j' : C} (f f' : j ⟶ j') : eq f f' ⟶ j :=
  (cone_maps f f').choose_spec.some
#align category_theory.is_cofiltered.eq_hom CategoryTheory.IsCofiltered.eqHom
-/

#print CategoryTheory.IsCofiltered.eq_condition /-
/-- `eq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`eq_hom f f' ≫ f = eq_hom f f' ≫ f'`.
-/
@[simp, reassoc]
theorem eq_condition {j j' : C} (f f' : j ⟶ j') : eqHom f f' ≫ f = eqHom f f' ≫ f' :=
  (cone_maps f f').choose_spec.choose_spec
#align category_theory.is_cofiltered.eq_condition CategoryTheory.IsCofiltered.eq_condition
-/

#print CategoryTheory.IsCofiltered.cospan /-
/-- For every cospan `j ⟶ i ⟵ j'`,
 there exists a cone `j ⟵ k ⟶ j'` such that the square commutes. -/
theorem cospan {i j j' : C} (f : j ⟶ i) (f' : j' ⟶ i) :
    ∃ (k : C) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f' :=
  let ⟨K, G, G', _⟩ := cone_objs j j'
  let ⟨k, e, he⟩ := cone_maps (G ≫ f) (G' ≫ f')
  ⟨k, e ≫ G, e ≫ G', by simpa only [category.assoc] using he⟩
#align category_theory.is_cofiltered.cospan CategoryTheory.IsCofiltered.cospan
-/

#print CategoryTheory.Functor.ranges_directed /-
theorem CategoryTheory.Functor.ranges_directed (F : C ⥤ Type _) (j : C) :
    Directed (· ⊇ ·) fun f : Σ' i, i ⟶ j => Set.range (F.map f.2) := fun ⟨i, ij⟩ ⟨k, kj⟩ =>
  by
  let ⟨l, li, lk, e⟩ := cospan ij kj
  refine' ⟨⟨l, lk ≫ kj⟩, e ▸ _, _⟩ <;> simp_rw [F.map_comp] <;> apply Set.range_comp_subset_range
#align category_theory.functor.ranges_directed CategoryTheory.Functor.ranges_directed
-/

end AllowEmpty

section Nonempty

open CategoryTheory.Limits

variable {C} [IsCofiltered C]

#print CategoryTheory.IsCofiltered.inf_objs_exists /-
/-- Any finite collection of objects in a cofiltered category has an object "to the left".
-/
theorem inf_objs_exists (O : Finset C) : ∃ S : C, ∀ {X}, X ∈ O → Nonempty (S ⟶ X) := by classical
#align category_theory.is_cofiltered.inf_objs_exists CategoryTheory.IsCofiltered.inf_objs_exists
-/

variable (O : Finset C) (H : Finset (Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y))

#print CategoryTheory.IsCofiltered.inf_exists /-
/-- Given any `finset` of objects `{X, ...}` and
indexed collection of `finset`s of morphisms `{f, ...}` in `C`,
there exists an object `S`, with a morphism `T X : S ⟶ X` from each `X`,
such that the triangles commute: `T X ≫ f = T Y`, for `f : X ⟶ Y` in the `finset`.
-/
theorem inf_exists :
    ∃ (S : C) (T : ∀ {X : C}, X ∈ O → (S ⟶ X)),
      ∀ {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y},
        (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H → T mX ≫ f = T mY :=
  by classical
#align category_theory.is_cofiltered.inf_exists CategoryTheory.IsCofiltered.inf_exists
-/

#print CategoryTheory.IsCofiltered.inf /-
/-- An arbitrary choice of object "to the left"
of a finite collection of objects `O` and morphisms `H`,
making all the triangles commute.
-/
noncomputable def inf : C :=
  (inf_exists O H).some
#align category_theory.is_cofiltered.inf CategoryTheory.IsCofiltered.inf
-/

#print CategoryTheory.IsCofiltered.infTo /-
/-- The morphisms from `inf O H`.
-/
noncomputable def infTo {X : C} (m : X ∈ O) : inf O H ⟶ X :=
  (inf_exists O H).choose_spec.some m
#align category_theory.is_cofiltered.inf_to CategoryTheory.IsCofiltered.infTo
-/

#print CategoryTheory.IsCofiltered.infTo_commutes /-
/-- The triangles consisting of a morphism in `H` and the maps from `inf O H` commute.
-/
theorem infTo_commutes {X Y : C} (mX : X ∈ O) (mY : Y ∈ O) {f : X ⟶ Y}
    (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H) :
    infTo O H mX ≫ f = infTo O H mY :=
  (inf_exists O H).choose_spec.choose_spec mX mY mf
#align category_theory.is_cofiltered.inf_to_commutes CategoryTheory.IsCofiltered.infTo_commutes
-/

variable {J : Type w} [SmallCategory J] [FinCategory J]

#print CategoryTheory.IsCofiltered.cone_nonempty /-
/-- If we have `is_cofiltered C`, then for any functor `F : J ⥤ C` with `fin_category J`,
there exists a cone over `F`.
-/
theorem cone_nonempty (F : J ⥤ C) : Nonempty (Cone F) := by classical
#align category_theory.is_cofiltered.cone_nonempty CategoryTheory.IsCofiltered.cone_nonempty
-/

#print CategoryTheory.IsCofiltered.cone /-
/-- An arbitrary choice of cone over `F : J ⥤ C`, for `fin_category J` and `is_cofiltered C`.
-/
noncomputable def cone (F : J ⥤ C) : Cone F :=
  (cone_nonempty F).some
#align category_theory.is_cofiltered.cone CategoryTheory.IsCofiltered.cone
-/

variable {D : Type u₁} [Category.{v₁} D]

#print CategoryTheory.IsCofiltered.of_left_adjoint /-
/-- If `C` is cofiltered, and we have a functor `L : C ⥤ D` with a right adjoint,
then `D` is cofiltered.
-/
theorem of_left_adjoint {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : IsCofiltered D :=
  { cone_objs := fun X Y =>
      ⟨L.obj (min (R.obj X) (R.obj Y)), (h.homEquiv _ X).symm (minToLeft _ _),
        (h.homEquiv _ Y).symm (minToRight _ _), ⟨⟩⟩
    cone_maps := fun X Y f g =>
      ⟨L.obj (eq (R.map f) (R.map g)), (h.homEquiv _ _).symm (eqHom _ _), by
        rw [← h.hom_equiv_naturality_right_symm, ← h.hom_equiv_naturality_right_symm, eq_condition]⟩
    Nonempty := IsCofiltered.nonempty.map L.obj }
#align category_theory.is_cofiltered.of_left_adjoint CategoryTheory.IsCofiltered.of_left_adjoint
-/

#print CategoryTheory.IsCofiltered.of_isLeftAdjoint /-
/-- If `C` is cofiltered, and we have a left adjoint functor `L : C ⥤ D`, then `D` is cofiltered. -/
theorem of_isLeftAdjoint (L : C ⥤ D) [IsLeftAdjoint L] : IsCofiltered D :=
  of_left_adjoint (Adjunction.ofLeftAdjoint L)
#align category_theory.is_cofiltered.of_is_left_adjoint CategoryTheory.IsCofiltered.of_isLeftAdjoint
-/

#print CategoryTheory.IsCofiltered.of_equivalence /-
/-- Being cofiltered is preserved by equivalence of categories. -/
theorem of_equivalence (h : C ≌ D) : IsCofiltered D :=
  of_left_adjoint h.toAdjunction
#align category_theory.is_cofiltered.of_equivalence CategoryTheory.IsCofiltered.of_equivalence
-/

end Nonempty

end IsCofiltered

section Opposite

open Opposite

#print CategoryTheory.isCofiltered_op_of_isFiltered /-
instance isCofiltered_op_of_isFiltered [IsFiltered C] : IsCofiltered Cᵒᵖ
    where
  cone_objs X Y :=
    ⟨op (IsFiltered.max X.unop Y.unop), (IsFiltered.leftToMax _ _).op,
      (IsFiltered.rightToMax _ _).op, trivial⟩
  cone_maps X Y f g :=
    ⟨op (IsFiltered.coeq f.unop g.unop), (IsFiltered.coeqHom _ _).op,
      by
      rw [show f = f.unop.op by simp, show g = g.unop.op by simp, ← op_comp, ← op_comp]
      congr 1
      exact is_filtered.coeq_condition f.unop g.unop⟩
  Nonempty := ⟨op IsFiltered.nonempty.some⟩
#align category_theory.is_cofiltered_op_of_is_filtered CategoryTheory.isCofiltered_op_of_isFiltered
-/

#print CategoryTheory.isFiltered_op_of_isCofiltered /-
instance isFiltered_op_of_isCofiltered [IsCofiltered C] : IsFiltered Cᵒᵖ
    where
  cocone_objs X Y :=
    ⟨op (IsCofiltered.min X.unop Y.unop), (IsCofiltered.minToLeft X.unop Y.unop).op,
      (IsCofiltered.minToRight X.unop Y.unop).op, trivial⟩
  cocone_maps X Y f g :=
    ⟨op (IsCofiltered.eq f.unop g.unop), (IsCofiltered.eqHom f.unop g.unop).op,
      by
      rw [show f = f.unop.op by simp, show g = g.unop.op by simp, ← op_comp, ← op_comp]
      congr 1
      exact is_cofiltered.eq_condition f.unop g.unop⟩
  Nonempty := ⟨op IsCofiltered.nonempty.some⟩
#align category_theory.is_filtered_op_of_is_cofiltered CategoryTheory.isFiltered_op_of_isCofiltered
-/

end Opposite

section ULift

instance [IsFiltered C] : IsFiltered (ULift.{u₂} C) :=
  IsFiltered.of_equivalence ULift.equivalence

instance [IsCofiltered C] : IsCofiltered (ULift.{u₂} C) :=
  IsCofiltered.of_equivalence ULift.equivalence

instance [IsFiltered C] : IsFiltered (ULiftHom C) :=
  IsFiltered.of_equivalence ULiftHom.equiv

instance [IsCofiltered C] : IsCofiltered (ULiftHom C) :=
  IsCofiltered.of_equivalence ULiftHom.equiv

instance [IsFiltered C] : IsFiltered (AsSmall C) :=
  IsFiltered.of_equivalence AsSmall.equiv

instance [IsCofiltered C] : IsCofiltered (AsSmall C) :=
  IsCofiltered.of_equivalence AsSmall.equiv

end ULift

end CategoryTheory

