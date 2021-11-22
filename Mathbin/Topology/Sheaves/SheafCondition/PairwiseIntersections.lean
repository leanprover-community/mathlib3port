import Mathbin.Topology.Sheaves.Sheaf 
import Mathbin.CategoryTheory.Limits.Preserves.Basic 
import Mathbin.CategoryTheory.Category.Pairwise

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → opens X` provides a functor `diagram U : overlap ι ⥤ (opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `supr U`,
and in fact this is a limit cone.

A presheaf `F : presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `is_limit (F.map_cone (cone U))`, or
* `preserves_limit (diagram U) F`
-/


noncomputable theory

universe v u

open TopologicalSpace

open Top

open Opposite

open CategoryTheory

open CategoryTheory.Limits

namespace Top.Presheaf

variable{X : Top.{v}}

variable{C : Type u}[category.{v} C]

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_pairwise_intersections`).

A presheaf is a sheaf if `F` sends the cone `(pairwise.cocone U).op` to a limit cone.
(Recall `pairwise.cocone U` has cone point `supr U`, mapping down to the `U i` and the `U i ⊓ U j`.)
-/
def is_sheaf_pairwise_intersections (F : presheaf C X) : Prop :=
  ∀ ⦃ι : Type v⦄ U : ι → opens X, Nonempty (is_limit (F.map_cone (pairwise.cocone U).op))

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections`).

A presheaf is a sheaf if `F` preserves the limit of `pairwise.diagram U`.
(Recall `pairwise.diagram U` is the diagram consisting of the pairwise intersections
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `supr U`.)
-/
def is_sheaf_preserves_limit_pairwise_intersections (F : presheaf C X) : Prop :=
  ∀ ⦃ι : Type v⦄ U : ι → opens X, Nonempty (preserves_limit (pairwise.diagram U).op F)

/-!
The remainder of this file shows that these conditions are equivalent
to the usual sheaf condition.
-/


variable[has_products C]

namespace SheafConditionPairwiseIntersections

open CategoryTheory.Pairwise CategoryTheory.Pairwise.Hom

open SheafConditionEqualizerProducts

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_functor_obj (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens («expr↥ » X))
  (c : limits.cone ((diagram U).op ⋙ F)) : limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
  { x := c.X,
    π :=
      { app :=
          fun Z =>
            walking_parallel_pair.cases_on Z (pi.lift fun i : ι => c.π.app (op (single i)))
              (pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2))),
        naturality' :=
          fun Y Z f =>
            by 
              cases Y <;> cases Z <;> cases f
              ·
                ext i 
                dsimp 
                simp only [limit.lift_π, category.id_comp, fan.mk_π_app, CategoryTheory.Functor.map_id, category.assoc]
                dsimp 
                simp only [limit.lift_π, category.id_comp, fan.mk_π_app]
              ·
                ext ⟨i, j⟩
                dsimp [sheaf_condition_equalizer_products.left_res]
                simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc]
                have h := c.π.naturality (Quiver.Hom.op (hom.left i j))
                dsimp  at h 
                simpa using h
              ·
                ext ⟨i, j⟩
                dsimp [sheaf_condition_equalizer_products.right_res]
                simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc]
                have h := c.π.naturality (Quiver.Hom.op (hom.right i j))
                dsimp  at h 
                simpa using h
              ·
                ext i 
                dsimp 
                simp only [limit.lift_π, category.id_comp, fan.mk_π_app, CategoryTheory.Functor.map_id, category.assoc]
                dsimp 
                simp only [limit.lift_π, category.id_comp, fan.mk_π_app] } }

section 

attribute [local tidy] tactic.case_bash

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_functor (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens («expr↥ » X)) :
  limits.cone ((diagram U).op ⋙ F) ⥤ limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
  { obj := fun c => cone_equiv_functor_obj F U c,
    map :=
      fun c c' f =>
        { Hom := f.hom,
          w' :=
            fun j =>
              by 
                cases j <;>
                  ·
                    ext 
                    simp only [limits.fan.mk_π_app, limits.cone_morphism.w, limits.limit.lift_π, category.assoc,
                      cone_equiv_functor_obj_π_app] } }

end 

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_inverse_obj (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens («expr↥ » X))
  (c : limits.cone (sheaf_condition_equalizer_products.diagram F U)) : limits.cone ((diagram U).op ⋙ F) :=
  { x := c.X,
    π :=
      { app :=
          by 
            intro x 
            induction x using Opposite.rec 
            rcases x with (⟨i⟩ | ⟨i, j⟩)
            ·
              exact c.π.app walking_parallel_pair.zero ≫ pi.π _ i
            ·
              exact c.π.app walking_parallel_pair.one ≫ pi.π _ (i, j),
        naturality' :=
          by 
            intro x y f 
            induction x using Opposite.rec 
            induction y using Opposite.rec 
            have ef : f = f.unop.op := rfl 
            revert ef 
            generalize f.unop = f' 
            rintro rfl 
            rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
            ·
              dsimp 
              erw [F.map_id]
              simp 
            ·
              dsimp 
              simp only [category.id_comp, category.assoc]
              have h := c.π.naturality walking_parallel_pair_hom.left 
              dsimp [sheaf_condition_equalizer_products.left_res]  at h 
              simp only [category.id_comp] at h 
              have h' := h =≫ pi.π _ (i, j)
              rw [h']
              simp 
              rfl
            ·
              dsimp 
              simp only [category.id_comp, category.assoc]
              have h := c.π.naturality walking_parallel_pair_hom.right 
              dsimp [sheaf_condition_equalizer_products.right_res]  at h 
              simp only [category.id_comp] at h 
              have h' := h =≫ pi.π _ (j, i)
              rw [h']
              simp 
              rfl
            ·
              dsimp 
              erw [F.map_id]
              simp  } }

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_inverse (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens («expr↥ » X)) :
  limits.cone (sheaf_condition_equalizer_products.diagram F U) ⥤ limits.cone ((diagram U).op ⋙ F) :=
  { obj := fun c => cone_equiv_inverse_obj F U c,
    map :=
      fun c c' f =>
        { Hom := f.hom,
          w' :=
            by 
              intro x 
              induction x using Opposite.rec 
              rcases x with (⟨i⟩ | ⟨i, j⟩)
              ·
                dsimp 
                rw [←f.w walking_parallel_pair.zero, category.assoc]
              ·
                dsimp 
                rw [←f.w walking_parallel_pair.one, category.assoc] } }

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_unit_iso_app (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens («expr↥ » X))
  (c : cone ((diagram U).op ⋙ F)) :
  (𝟭 (cone ((diagram U).op ⋙ F))).obj c ≅ (cone_equiv_functor F U ⋙ cone_equiv_inverse F U).obj c :=
  { Hom :=
      { Hom := 𝟙 _,
        w' :=
          fun j =>
            by 
              induction j using Opposite.rec 
              rcases j with ⟨⟩ <;>
                ·
                  dsimp 
                  simp only [limits.fan.mk_π_app, category.id_comp, limits.limit.lift_π] },
    inv :=
      { Hom := 𝟙 _,
        w' :=
          fun j =>
            by 
              induction j using Opposite.rec 
              rcases j with ⟨⟩ <;>
                ·
                  dsimp 
                  simp only [limits.fan.mk_π_app, category.id_comp, limits.limit.lift_π] },
    hom_inv_id' :=
      by 
        ext 
        simp only [category.comp_id, limits.cone.category_comp_hom, limits.cone.category_id_hom],
    inv_hom_id' :=
      by 
        ext 
        simp only [category.comp_id, limits.cone.category_comp_hom, limits.cone.category_id_hom] }

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_unit_iso (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  𝟭 (limits.cone ((diagram U).op ⋙ F)) ≅ cone_equiv_functor F U ⋙ cone_equiv_inverse F U :=
  nat_iso.of_components (cone_equiv_unit_iso_app F U)
    (by 
      tidy)

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simps]
def cone_equiv_counit_iso (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  cone_equiv_inverse F U ⋙ cone_equiv_functor F U ≅ 𝟭 (limits.cone (sheaf_condition_equalizer_products.diagram F U)) :=
  nat_iso.of_components
    (fun c =>
      { Hom :=
          { Hom := 𝟙 _,
            w' :=
              by 
                rintro ⟨_ | _⟩
                ·
                  ext 
                  dsimp 
                  simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π]
                ·
                  ext ⟨i, j⟩
                  dsimp 
                  simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π] },
        inv :=
          { Hom := 𝟙 _,
            w' :=
              by 
                rintro ⟨_ | _⟩
                ·
                  ext 
                  dsimp 
                  simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π]
                ·
                  ext ⟨i, j⟩
                  dsimp 
                  simp only [category.id_comp, limits.fan.mk_π_app, limits.limit.lift_π] },
        hom_inv_id' :=
          by 
            ext 
            dsimp 
            simp only [category.comp_id],
        inv_hom_id' :=
          by 
            ext 
            dsimp 
            simp only [category.comp_id] })
    fun c d f =>
      by 
        ext 
        dsimp 
        simp only [category.comp_id, category.id_comp]

/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
def cone_equiv (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X) :
  limits.cone ((diagram U).op ⋙ F) ≌ limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
  { Functor := cone_equiv_functor F U, inverse := cone_equiv_inverse F U, unitIso := cone_equiv_unit_iso F U,
    counitIso := cone_equiv_counit_iso F U }

attribute [local reducible] sheaf_condition_equalizer_products.res sheaf_condition_equalizer_products.left_res

/--
If `sheaf_condition_equalizer_products.fork` is an equalizer,
then `F.map_cone (cone U)` is a limit cone.
-/
def is_limit_map_cone_of_is_limit_sheaf_condition_fork (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X)
  (P : is_limit (sheaf_condition_equalizer_products.fork F U)) : is_limit (F.map_cone (cocone U).op) :=
  is_limit.of_iso_limit ((is_limit.of_cone_equiv (cone_equiv F U).symm).symm P)
    { Hom :=
        { Hom := 𝟙 _,
          w' :=
            by 
              intro x 
              induction x using Opposite.rec 
              rcases x with ⟨⟩
              ·
                dsimp 
                simp 
                rfl
              ·
                dsimp 
                simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc]
                rw [←F.map_comp]
                rfl },
      inv :=
        { Hom := 𝟙 _,
          w' :=
            by 
              intro x 
              induction x using Opposite.rec 
              rcases x with ⟨⟩
              ·
                dsimp 
                simp 
                rfl
              ·
                dsimp 
                simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc]
                rw [←F.map_comp]
                rfl },
      hom_inv_id' :=
        by 
          ext 
          dsimp 
          simp only [category.comp_id],
      inv_hom_id' :=
        by 
          ext 
          dsimp 
          simp only [category.comp_id] }

/--
If `F.map_cone (cone U)` is a limit cone,
then `sheaf_condition_equalizer_products.fork` is an equalizer.
-/
def is_limit_sheaf_condition_fork_of_is_limit_map_cone (F : presheaf C X) ⦃ι : Type v⦄ (U : ι → opens X)
  (Q : is_limit (F.map_cone (cocone U).op)) : is_limit (sheaf_condition_equalizer_products.fork F U) :=
  is_limit.of_iso_limit ((is_limit.of_cone_equiv (cone_equiv F U)).symm Q)
    { Hom :=
        { Hom := 𝟙 _,
          w' :=
            by 
              rintro ⟨⟩
              ·
                dsimp 
                simp 
                rfl
              ·
                dsimp 
                ext ⟨i, j⟩
                simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc]
                rw [←F.map_comp]
                rfl },
      inv :=
        { Hom := 𝟙 _,
          w' :=
            by 
              rintro ⟨⟩
              ·
                dsimp 
                simp 
                rfl
              ·
                dsimp 
                ext ⟨i, j⟩
                simp only [limit.lift_π, limit.lift_π_assoc, category.id_comp, fan.mk_π_app, category.assoc]
                rw [←F.map_comp]
                rfl },
      hom_inv_id' :=
        by 
          ext 
          dsimp 
          simp only [category.comp_id],
      inv_hom_id' :=
        by 
          ext 
          dsimp 
          simp only [category.comp_id] }

end SheafConditionPairwiseIntersections

open SheafConditionPairwiseIntersections

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
theorem is_sheaf_iff_is_sheaf_pairwise_intersections (F : presheaf C X) :
  F.is_sheaf ↔ F.is_sheaf_pairwise_intersections :=
  Iff.intro (fun h ι U => ⟨is_limit_map_cone_of_is_limit_sheaf_condition_fork F U (h U).some⟩)
    fun h ι U => ⟨is_limit_sheaf_condition_fork_of_is_limit_map_cone F U (h U).some⟩

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
theorem is_sheaf_iff_is_sheaf_preserves_limit_pairwise_intersections (F : presheaf C X) :
  F.is_sheaf ↔ F.is_sheaf_preserves_limit_pairwise_intersections :=
  by 
    rw [is_sheaf_iff_is_sheaf_pairwise_intersections]
    split 
    ·
      intro h ι U 
      exact ⟨preserves_limit_of_preserves_limit_cone (pairwise.cocone_is_colimit U).op (h U).some⟩
    ·
      intro h ι U 
      haveI  := (h U).some 
      exact ⟨preserves_limit.preserves (pairwise.cocone_is_colimit U).op⟩

end Top.Presheaf

