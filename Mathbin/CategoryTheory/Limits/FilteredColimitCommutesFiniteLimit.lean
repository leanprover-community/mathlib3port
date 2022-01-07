import Mathbin.CategoryTheory.Limits.ColimitLimit
import Mathbin.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Finite
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathbin.CategoryTheory.Limits.Preserves.Filtered

/-!
# Filtered colimits commute with finite limits.

We show that for a functor `F : J × K ⥤ Type v`, when `J` is finite and `K` is filtered,
the universal morphism `colimit_limit_to_limit_colimit F` comparing the
colimit (over `K`) of the limits (over `J`) with the limit of the colimits is an isomorphism.

(In fact, to prove that it is injective only requires that `J` has finitely many objects.)

## References
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/


universe v u

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits.Types

open CategoryTheory.Limits.Types.FilteredColimit

namespace CategoryTheory.Limits

variable {J K : Type v} [small_category J] [small_category K]

variable (F : J × K ⥤ Type v)

open CategoryTheory.prod

variable [is_filtered K]

section

/-!
Injectivity doesn't need that we have finitely many morphisms in `J`,
only that there are finitely many objects.
-/


variable [Fintype J]

-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (X Y)
-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (X Y)
-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (X Y)
/-- This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
-/
theorem colimit_limit_to_limit_colimit_injective : Function.Injective (colimit_limit_to_limit_colimit F) := by
  classical
  intro x y h
  obtain ⟨kx, x, rfl⟩ := jointly_surjective' x
  obtain ⟨ky, y, rfl⟩ := jointly_surjective' y
  dsimp  at x y
  replace h := fun j => congr_argₓ (limit.π (curry.obj F ⋙ colim) j) h
  simp [colimit_eq_iff] at h
  let k := fun j => (h j).some
  let f : ∀ j, kx ⟶ k j := fun j => (h j).some_spec.some
  let g : ∀ j, ky ⟶ k j := fun j => (h j).some_spec.some_spec.some
  have w :
    ∀ j,
      F.map ((𝟙 j, f j) : (j, kx) ⟶ (j, k j)) (limit.π ((curry.obj (swap K J ⋙ F)).obj kx) j x) =
        F.map ((𝟙 j, g j) : (j, ky) ⟶ (j, k j)) (limit.π ((curry.obj (swap K J ⋙ F)).obj ky) j y) :=
    fun j => (h j).some_spec.some_spec.some_spec
  let O : Finset K := Finset.univ.Image k ∪ {kx, ky}
  have kxO : kx ∈ O :=
    finset.mem_union.mpr
      (Or.inr
        (by
          simp ))
  have kyO : ky ∈ O :=
    finset.mem_union.mpr
      (Or.inr
        (by
          simp ))
  have kjO : ∀ j, k j ∈ O := fun j =>
    finset.mem_union.mpr
      (Or.inl
        (by
          simp ))
  let H : Finset (Σ' (X : K) (Y : K) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    (Finset.univ.Image fun j : J =>
        ⟨kx, k j, kxO,
          finset.mem_union.mpr
            (Or.inl
              (by
                simp )),
          f j⟩) ∪
      Finset.univ.Image fun j : J =>
        ⟨ky, k j, kyO,
          finset.mem_union.mpr
            (Or.inl
              (by
                simp )),
          g j⟩
  obtain ⟨S, T, W⟩ := is_filtered.sup_exists O H
  have fH : ∀ j, (⟨kx, k j, kxO, kjO j, f j⟩ : Σ' (X : K) (Y : K) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H := fun j =>
    finset.mem_union.mpr
      (Or.inl
        (by
          simp only [true_andₓ, Finset.mem_univ, eq_self_iff_true, exists_prop_of_true, Finset.mem_image, heq_iff_eq]
          refine' ⟨j, rfl, _⟩
          simp only [heq_iff_eq]
          exact ⟨rfl, rfl, rfl⟩))
  have gH : ∀ j, (⟨ky, k j, kyO, kjO j, g j⟩ : Σ' (X : K) (Y : K) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) ∈ H := fun j =>
    finset.mem_union.mpr
      (Or.inr
        (by
          simp only [true_andₓ, Finset.mem_univ, eq_self_iff_true, exists_prop_of_true, Finset.mem_image, heq_iff_eq]
          refine' ⟨j, rfl, _⟩
          simp only [heq_iff_eq]
          exact ⟨rfl, rfl, rfl⟩))
  apply colimit_sound' (T kxO) (T kyO)
  ext
  simp only [functor.comp_map, limit.map_π_apply, curry.obj_map_app, swap_map]
  rw [← W _ _ (fH j)]
  rw [← W _ _ (gH j)]
  simp [w]

end

variable [fin_category J]

-- ././Mathport/Syntax/Translate/Basic.lean:626:6: warning: expanding binder group (X Y)
/-- This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
although with different names.
-/
theorem colimit_limit_to_limit_colimit_surjective : Function.Surjective (colimit_limit_to_limit_colimit F) := by
  classical
  intro x
  have z := fun j => jointly_surjective' (limit.π (curry.obj F ⋙ limits.colim) j x)
  let k : J → K := fun j => (z j).some
  let y : ∀ j, F.obj (j, k j) := fun j => (z j).some_spec.some
  have e : ∀ j, colimit.ι ((curry.obj F).obj j) (k j) (y j) = limit.π (curry.obj F ⋙ limits.colim) j x := fun j =>
    (z j).some_spec.some_spec
  clear_value k y
  clear z
  let k' : K := is_filtered.sup (finset.univ.image k) ∅
  have g : ∀ j, k j ⟶ k' := fun j =>
    is_filtered.to_sup (finset.univ.image k) ∅
      (by
        simp )
  clear_value k'
  have w :
    ∀ {j j' : J} f : j ⟶ j',
      colimit.ι ((curry.obj F).obj j') k' (F.map ((𝟙 j', g j') : (j', k j') ⟶ (j', k')) (y j')) =
        colimit.ι ((curry.obj F).obj j') k' (F.map ((f, g j) : (j, k j) ⟶ (j', k')) (y j)) :=
    by
    intro j j' f
    have t : (f, g j) = (((f, 𝟙 (k j)) : (j, k j) ⟶ (j', k j)) ≫ (𝟙 j', g j) : (j, k j) ⟶ (j', k')) := by
      simp only [id_comp, comp_id, prod_comp]
    erw [colimit.w_apply, t, functor_to_types.map_comp_apply, colimit.w_apply, e, ← limit.w_apply f, ← e]
    simp
  simp_rw [colimit_eq_iff]  at w
  let kf : ∀ {j j'} f : j ⟶ j', K := fun _ _ f => (w f).some
  let gf : ∀ {j j'} f : j ⟶ j', k' ⟶ kf f := fun _ _ f => (w f).some_spec.some
  let hf : ∀ {j j'} f : j ⟶ j', k' ⟶ kf f := fun _ _ f => (w f).some_spec.some_spec.some
  have wf :
    ∀ {j j'} f : j ⟶ j',
      F.map ((𝟙 j', g j' ≫ gf f) : (j', k j') ⟶ (j', kf f)) (y j') =
        F.map ((f, g j ≫ hf f) : (j, k j) ⟶ (j', kf f)) (y j) :=
    fun j j' f => by
    have q : ((curry.obj F).obj j').map (gf f) (F.map _ (y j')) = ((curry.obj F).obj j').map (hf f) (F.map _ (y j)) :=
      (w f).some_spec.some_spec.some_spec
    dsimp  at q
    simp_rw [← functor_to_types.map_comp_apply]  at q
    convert q <;> simp only [comp_id]
  clear_value kf gf hf
  clear w
  let O := (finset.univ.bUnion fun j => finset.univ.bUnion fun j' => finset.univ.image (@kf j j')) ∪ {k'}
  have kfO : ∀ {j j'} f : j ⟶ j', kf f ∈ O := fun j j' f =>
    finset.mem_union.mpr
      (Or.inl
        (by
          rw [Finset.mem_bUnion]
          refine' ⟨j, Finset.mem_univ j, _⟩
          rw [Finset.mem_bUnion]
          refine' ⟨j', Finset.mem_univ j', _⟩
          rw [Finset.mem_image]
          refine' ⟨f, Finset.mem_univ _, _⟩
          rfl))
  have k'O : k' ∈ O := finset.mem_union.mpr (Or.inr (finset.mem_singleton.mpr rfl))
  let H : Finset (Σ' (X : K) (Y : K) (mX : X ∈ O) (mY : Y ∈ O), X ⟶ Y) :=
    finset.univ.bUnion fun j : J =>
      finset.univ.bUnion fun j' : J =>
        finset.univ.bUnion fun f : j ⟶ j' => {⟨k', kf f, k'O, kfO f, gf f⟩, ⟨k', kf f, k'O, kfO f, hf f⟩}
  obtain ⟨k'', i', s'⟩ := is_filtered.sup_exists O H
  let i : ∀ {j j'} f : j ⟶ j', kf f ⟶ k'' := fun j j' f => i' (kfO f)
  have s : ∀ {j₁ j₂ j₃ j₄} f : j₁ ⟶ j₂ f' : j₃ ⟶ j₄, gf f ≫ i f = hf f' ≫ i f' := by
    intros
    rw [s', s']
    swap 2
    exact k'O
    swap 2
    · rw [Finset.mem_bUnion]
      refine' ⟨j₁, Finset.mem_univ _, _⟩
      rw [Finset.mem_bUnion]
      refine' ⟨j₂, Finset.mem_univ _, _⟩
      rw [Finset.mem_bUnion]
      refine' ⟨f, Finset.mem_univ _, _⟩
      simp only [true_orₓ, eq_self_iff_true, and_selfₓ, Finset.mem_insert, heq_iff_eq]
      
    · rw [Finset.mem_bUnion]
      refine' ⟨j₃, Finset.mem_univ _, _⟩
      rw [Finset.mem_bUnion]
      refine' ⟨j₄, Finset.mem_univ _, _⟩
      rw [Finset.mem_bUnion]
      refine' ⟨f', Finset.mem_univ _, _⟩
      simp only [eq_self_iff_true, or_trueₓ, and_selfₓ, Finset.mem_insert, Finset.mem_singleton, heq_iff_eq]
      
  clear_value i
  clear s' i' H kfO k'O O
  fconstructor
  · apply colimit.ι (curry.obj (swap K J ⋙ F) ⋙ limits.lim) k'' _
    dsimp
    ext
    swap
    · exact fun j => F.map (⟨𝟙 j, g j ≫ gf (𝟙 j) ≫ i (𝟙 j)⟩ : (j, k j) ⟶ (j, k'')) (y j)
      
    · dsimp
      simp only [← functor_to_types.map_comp_apply, prod_comp, id_comp, comp_id]
      calc
        F.map ((f, g j ≫ gf (𝟙 j) ≫ i (𝟙 j)) : (j, k j) ⟶ (j', k'')) (y j) =
            F.map ((f, g j ≫ hf f ≫ i f) : (j, k j) ⟶ (j', k'')) (y j) :=
          by
          rw
            [s (𝟙 j)
              f]_ =
            F.map ((𝟙 j', i f) : (j', kf f) ⟶ (j', k'')) (F.map ((f, g j ≫ hf f) : (j, k j) ⟶ (j', kf f)) (y j)) :=
          by
          rw [← functor_to_types.map_comp_apply, prod_comp, comp_id,
            assoc]_ =
            F.map ((𝟙 j', i f) : (j', kf f) ⟶ (j', k''))
              (F.map ((𝟙 j', g j' ≫ gf f) : (j', k j') ⟶ (j', kf f)) (y j')) :=
          by
          rw [← wf f]_ = F.map ((𝟙 j', g j' ≫ gf f ≫ i f) : (j', k j') ⟶ (j', k'')) (y j') := by
          rw [← functor_to_types.map_comp_apply, prod_comp, id_comp,
            assoc]_ = F.map ((𝟙 j', g j' ≫ gf (𝟙 j') ≫ i (𝟙 j')) : (j', k j') ⟶ (j', k'')) (y j') :=
          by
          rw [s f (𝟙 j'), ← s (𝟙 j') (𝟙 j')]
      
    
  · apply limit_ext
    intro j
    simp only [← e, colimit_eq_iff, curry.obj_obj_map, limit.π_mk, bifunctor.map_id_comp, id.def, types_comp_apply,
      limits.ι_colimit_limit_to_limit_colimit_π_apply]
    refine' ⟨k'', 𝟙 k'', g j ≫ gf (𝟙 j) ≫ i (𝟙 j), _⟩
    simp only [bifunctor.map_id_comp, types_comp_apply, bifunctor.map_id, types_id_apply]
    

instance colimit_limit_to_limit_colimit_is_iso : is_iso (colimit_limit_to_limit_colimit F) :=
  (is_iso_iff_bijective _).mpr ⟨colimit_limit_to_limit_colimit_injective F, colimit_limit_to_limit_colimit_surjective F⟩

instance colimit_limit_to_limit_colimit_cone_iso (F : J ⥤ K ⥤ Type v) :
    is_iso (colimit_limit_to_limit_colimit_cone F) := by
  have : is_iso (colimit_limit_to_limit_colimit_cone F).Hom := by
    dsimp only [colimit_limit_to_limit_colimit_cone]
    infer_instance
  apply cones.cone_iso_of_hom_iso

noncomputable instance filtered_colim_preserves_finite_limits_of_types :
    preserves_finite_limits (colim : (K ⥤ Type v) ⥤ _) :=
  ⟨fun J _ _ =>
    ⟨fun F =>
      ⟨fun c hc => by
        apply is_limit.of_iso_limit (limit.is_limit _)
        symm
        trans colim.map_cone (limit.cone F)
        exact functor.map_iso _ (hc.unique_up_to_iso (limit.is_limit F))
        exact as_iso (colimit_limit_to_limit_colimit_cone F)⟩⟩⟩

variable {C : Type u} [category.{v} C] [concrete_category.{v} C]

section

variable [has_limits_of_shape J C] [has_colimits_of_shape K C]

variable [reflects_limits_of_shape J (forget C)] [preserves_colimits_of_shape K (forget C)]

variable [preserves_limits_of_shape J (forget C)]

noncomputable instance filtered_colim_preserves_finite_limits : preserves_limits_of_shape J (colim : (K ⥤ C) ⥤ _) :=
  have : preserves_limits_of_shape J ((colim : (K ⥤ C) ⥤ _) ⋙ forget C) :=
    preserves_limits_of_shape_of_nat_iso (preserves_colimit_nat_iso _).symm
  preserves_limits_of_shape_of_reflects_of_preserves _ (forget C)

end

attribute [local instance] reflects_limits_of_shape_of_reflects_isomorphisms

noncomputable instance [preserves_finite_limits (forget C)] [preserves_filtered_colimits (forget C)]
    [has_finite_limits C] [has_colimits_of_shape K C] [reflects_isomorphisms (forget C)] :
    preserves_finite_limits (colim : (K ⥤ C) ⥤ _) :=
  ⟨fun _ _ _ => CategoryTheory.Limits.filteredColimPreservesFiniteLimits⟩

section

variable [has_limits_of_shape J C] [has_colimits_of_shape K C]

variable [reflects_limits_of_shape J (forget C)] [preserves_colimits_of_shape K (forget C)]

variable [preserves_limits_of_shape J (forget C)]

/-- A curried version of the fact that filtered colimits commute with finite limits. -/
noncomputable def colimit_limit_iso (F : J ⥤ K ⥤ C) : colimit (limit F) ≅ limit (colimit F.flip) :=
  (is_limit_of_preserves colim (limit.is_limit _)).conePointUniqueUpToIso (limit.is_limit _) ≪≫
    has_limit.iso_of_nat_iso (colimit_flip_iso_comp_colim _).symm

@[simp, reassoc]
theorem ι_colimit_limit_iso_limit_π (F : J ⥤ K ⥤ C) a b :
    colimit.ι (limit F) a ≫ (colimit_limit_iso F).Hom ≫ limit.π (colimit F.flip) b =
      (limit.π F b).app a ≫ (colimit.ι F.flip a).app b :=
  by
  dsimp [colimit_limit_iso]
  simp only [functor.map_cone_π_app, iso.symm_hom, limits.limit.cone_point_unique_up_to_iso_hom_comp_assoc,
    limits.limit.cone_π, limits.colimit.ι_map_assoc, limits.colimit_flip_iso_comp_colim_inv_app, assoc,
    limits.has_limit.iso_of_nat_iso_hom_π]
  congr 1
  simp only [← category.assoc, iso.comp_inv_eq, limits.colimit_obj_iso_colimit_comp_evaluation_ι_app_hom,
    limits.has_colimit.iso_of_nat_iso_ι_hom, nat_iso.of_components.hom_app]
  dsimp
  simp

end

end CategoryTheory.Limits

