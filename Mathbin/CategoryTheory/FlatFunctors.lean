import Mathbin.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathbin.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Bicones
import Mathbin.CategoryTheory.Limits.Comma
import Mathbin.CategoryTheory.Limits.Preserves.Finite
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Representably flat functors

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also known as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to avoid
confusion with other notions of flatness.

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preserves_finite_limits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preserves_finite_limits_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preserves_finite_limits_iff_flat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left_exact.
* `Lan_preserves_finite_limits_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_Lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preserves_finite_limits_iff_Lan_preserves_finite_limits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory

namespace StructuredArrowCone

open StructuredArrow

variable {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]

variable {J : Type v₁} [small_category J]

variable {K : J ⥤ C} (F : C ⥤ D) (c : cone K)

/-- Given a cone `c : cone K` and a map `f : X ⟶ c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point. This is the underlying diagram.
-/
@[simps]
def to_diagram : J ⥤ structured_arrow c.X K where
  obj := fun j => structured_arrow.mk (c.π.app j)
  map := fun j k g =>
    structured_arrow.hom_mk g
      (by
        simpa)

/-- Given a diagram of `structured_arrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps]
def diagram_to_cone {X : D} (G : J ⥤ structured_arrow X F) : cone (G ⋙ proj X F ⋙ F) :=
  { x, π := { app := fun j => (G.obj j).Hom } }

/-- Given a cone `c : cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
def to_cone {X : D} (f : X ⟶ F.obj c.X) : cone (to_diagram (F.map_cone c) ⋙ map f ⋙ pre _ K F) where
  x := mk f
  π :=
    { app := fun j => hom_mk (c.π.app j) rfl,
      naturality' := fun j k g => by
        ext
        dsimp
        simp }

end StructuredArrowCone

section RepresentablyFlat

variable {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

variable {E : Type u₃} [category.{v₃} E]

/-- A functor `F : C ⥤ D` is representably-flat functor if the comma category `(X/F)`
is cofiltered for each `X : C`.
-/
class representably_flat (F : C ⥤ D) : Prop where
  cofiltered : ∀ X : D, is_cofiltered (structured_arrow X F)

attribute [instance] representably_flat.cofiltered

attribute [local instance] is_cofiltered.nonempty

instance representably_flat.id : representably_flat (𝟭 C) := by
  constructor
  intro X
  have : Nonempty (structured_arrow X (𝟭 C)) := ⟨structured_arrow.mk (𝟙 _)⟩
  suffices is_cofiltered_or_empty (structured_arrow X (𝟭 C)) by
    skip
    constructor
  constructor
  · intro Y Z
    use structured_arrow.mk (𝟙 _)
    use
      structured_arrow.hom_mk Y.hom
        (by
          erw [functor.id_map, category.id_comp])
    use
      structured_arrow.hom_mk Z.hom
        (by
          erw [functor.id_map, category.id_comp])
    
  · intro Y Z f g
    use structured_arrow.mk (𝟙 _)
    use
      structured_arrow.hom_mk Y.hom
        (by
          erw [functor.id_map, category.id_comp])
    ext
    trans Z.hom <;> simp
    

instance representably_flat.comp (F : C ⥤ D) (G : D ⥤ E) [representably_flat F] [representably_flat G] :
    representably_flat (F ⋙ G) := by
  constructor
  intro X
  have : Nonempty (structured_arrow X (F ⋙ G)) := by
    have f₁ : structured_arrow X G := Nonempty.some inferInstance
    have f₂ : structured_arrow f₁.right F := Nonempty.some inferInstance
    exact ⟨structured_arrow.mk (f₁.hom ≫ G.map f₂.hom)⟩
  suffices is_cofiltered_or_empty (structured_arrow X (F ⋙ G)) by
    skip
    constructor
  constructor
  · intro Y Z
    let W := @is_cofiltered.min (structured_arrow X G) _ _ (structured_arrow.mk Y.hom) (structured_arrow.mk Z.hom)
    let Y' : W ⟶ _ := is_cofiltered.min_to_left _ _
    let Z' : W ⟶ _ := is_cofiltered.min_to_right _ _
    let W' :=
      @is_cofiltered.min (structured_arrow W.right F) _ _ (structured_arrow.mk Y'.right) (structured_arrow.mk Z'.right)
    let Y'' : W' ⟶ _ := is_cofiltered.min_to_left _ _
    let Z'' : W' ⟶ _ := is_cofiltered.min_to_right _ _
    use structured_arrow.mk (W.hom ≫ G.map W'.hom)
    use
      structured_arrow.hom_mk Y''.right
        (by
          simp [← G.map_comp])
    use
      structured_arrow.hom_mk Z''.right
        (by
          simp [← G.map_comp])
    
  · intro Y Z f g
    let W :=
      @is_cofiltered.eq (structured_arrow X G) _ _ (structured_arrow.mk Y.hom) (structured_arrow.mk Z.hom)
        (structured_arrow.hom_mk (F.map f.right) (structured_arrow.w f))
        (structured_arrow.hom_mk (F.map g.right) (structured_arrow.w g))
    let h : W ⟶ _ := is_cofiltered.eq_hom _ _
    let h_cond : h ≫ _ = h ≫ _ := is_cofiltered.eq_condition _ _
    let W' :=
      @is_cofiltered.eq (structured_arrow W.right F) _ _ (structured_arrow.mk h.right)
        (structured_arrow.mk (h.right ≫ F.map f.right)) (structured_arrow.hom_mk f.right rfl)
        (structured_arrow.hom_mk g.right (congr_argₓ comma_morphism.right h_cond).symm)
    let h' : W' ⟶ _ := is_cofiltered.eq_hom _ _
    let h'_cond : h' ≫ _ = h' ≫ _ := is_cofiltered.eq_condition _ _
    use structured_arrow.mk (W.hom ≫ G.map W'.hom)
    use
      structured_arrow.hom_mk h'.right
        (by
          simp [← G.map_comp])
    ext
    exact (congr_argₓ comma_morphism.right h'_cond : _)
    

end RepresentablyFlat

section HasLimit

variable {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]

instance (priority := 100) cofiltered_of_has_finite_limits [has_finite_limits C] : is_cofiltered C where
  cocone_objs := fun A B => ⟨limits.prod A B, limits.prod.fst, limits.prod.snd, trivialₓ⟩
  cocone_maps := fun A B f g => ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩
  Nonempty := ⟨⊤_ C⟩

theorem flat_of_preserves_finite_limits [has_finite_limits C] (F : C ⥤ D) [preserves_finite_limits F] :
    representably_flat F :=
  ⟨fun X => by
    have : has_finite_limits (structured_arrow X F) :=
      { out := fun J _ _ => by
          skip
          infer_instance }
    infer_instance⟩

namespace PreservesFiniteLimitsOfFlat

open StructuredArrow

open StructuredArrowCone

variable {J : Type v₁} [small_category J] [fin_category J] {K : J ⥤ C}

variable (F : C ⥤ D) [representably_flat F] {c : cone K} (hc : is_limit c) (s : cone (K ⋙ F))

include hc

/-- (Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` representably flat,
`s` can factor through `F.map_cone c`.
-/
noncomputable def lift : s.X ⟶ F.obj c.X :=
  let s' := is_cofiltered.cone (to_diagram s ⋙ structured_arrow.pre _ K F)
  s'.X.hom ≫
    (F.map <|
      hc.lift <|
        (cones.postcompose
              ({ app := fun X => 𝟙 _,
                naturality' := by
                  simp } :
                (to_diagram s ⋙ pre s.X K F) ⋙ proj s.X F ⟶ K)).obj <|
          (structured_arrow.proj s.X F).mapCone s')

theorem fac (x : J) : lift F hc s ≫ (F.map_cone c).π.app x = s.π.app x := by
  simpa [lift, ← functor.map_comp]

theorem uniq {K : J ⥤ C} {c : cone K} (hc : is_limit c) (s : cone (K ⋙ F)) (f₁ f₂ : s.X ⟶ F.obj c.X)
    (h₁ : ∀ j : J, f₁ ≫ (F.map_cone c).π.app j = s.π.app j) (h₂ : ∀ j : J, f₂ ≫ (F.map_cone c).π.app j = s.π.app j) :
    f₁ = f₂ := by
  let α₁ : to_diagram (F.map_cone c) ⋙ map f₁ ⟶ to_diagram s :=
    { app := fun X =>
        eq_to_hom
          (by
            simp [← h₁]),
      naturality' := fun _ _ _ => by
        ext
        simp }
  let α₂ : to_diagram (F.map_cone c) ⋙ map f₂ ⟶ to_diagram s :=
    { app := fun X =>
        eq_to_hom
          (by
            simp [← h₂]),
      naturality' := fun _ _ _ => by
        ext
        simp }
  let c₁ : cone (to_diagram s ⋙ pre s.X K F) :=
    (cones.postcompose (whisker_right α₁ (pre s.X K F) : _)).obj (to_cone F c f₁)
  let c₂ : cone (to_diagram s ⋙ pre s.X K F) :=
    (cones.postcompose (whisker_right α₂ (pre s.X K F) : _)).obj (to_cone F c f₂)
  let c₀ := is_cofiltered.cone (bicone_mk _ c₁ c₂)
  let g₁ : c₀.X ⟶ c₁.X := c₀.π.app bicone.left
  let g₂ : c₀.X ⟶ c₂.X := c₀.π.app bicone.right
  have : ∀ j : J, g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j := by
    intro j
    injection c₀.π.naturality (bicone_hom.left j) with _ e₁
    injection c₀.π.naturality (bicone_hom.right j) with _ e₂
    simpa using e₁.symm.trans e₂
  have : c.extend g₁.right = c.extend g₂.right := by
    unfold cone.extend
    congr 1
    ext x
    apply this
  have : g₁.right = g₂.right
  calc g₁.right = hc.lift (c.extend g₁.right) := by
      apply hc.uniq (c.extend _)
      tidy _ = hc.lift (c.extend g₂.right) := by
      congr
      exact this _ = g₂.right := by
      symm
      apply hc.uniq (c.extend _)
      tidy
  calc f₁ = 𝟙 _ ≫ f₁ := by
      simp _ = c₀.X.hom ≫ F.map g₁.right := g₁.w _ = c₀.X.hom ≫ F.map g₂.right := by
      rw [this]_ = 𝟙 _ ≫ f₂ := g₂.w.symm _ = f₂ := by
      simp

end PreservesFiniteLimitsOfFlat

/-- Representably flat functors preserve finite limits. -/
noncomputable def preserves_finite_limits_of_flat (F : C ⥤ D) [representably_flat F] : preserves_finite_limits F :=
  ⟨fun J _ _ =>
    ⟨fun K =>
      ⟨fun c hc =>
        { lift := preserves_finite_limits_of_flat.lift F hc, fac' := preserves_finite_limits_of_flat.fac F hc,
          uniq' := fun s m h => by
            apply preserves_finite_limits_of_flat.uniq F hc
            exact h
            exact preserves_finite_limits_of_flat.fac F hc s }⟩⟩⟩

/-- If `C` is finitely cocomplete, then `F : C ⥤ D` is representably flat iff it preserves
finite limits.
-/
noncomputable def preserves_finite_limits_iff_flat [has_finite_limits C] (F : C ⥤ D) :
    representably_flat F ≃ preserves_finite_limits F where
  toFun := fun _ => preserves_finite_limits_of_flat F
  invFun := fun _ => flat_of_preserves_finite_limits F
  left_inv := fun _ => proof_irrelₓ _ _
  right_inv := fun x => by
    cases x
    unfold preserves_finite_limits_of_flat
    congr

end HasLimit

section SmallCategory

variable {C D : Type u₁} [small_category C] [small_category D] (E : Type u₂) [category.{u₁} E]

/-- (Implementation)
The evaluation of `Lan F` at `X` is the colimit over the costructured arrows over `X`.
-/
noncomputable def Lan_evaluation_iso_colim (F : C ⥤ D) (X : D)
    [∀ X : D, has_colimits_of_shape (costructured_arrow F X) E] :
    Lan F ⋙ (evaluation D E).obj X ≅ (whiskering_left _ _ E).obj (costructured_arrow.proj F X) ⋙ colim :=
  nat_iso.of_components (fun G => colim.mapIso (iso.refl _))
    (by
      intro G H i
      ext
      simp only [functor.comp_map, colimit.ι_desc_assoc, functor.map_iso_refl, evaluation_obj_map,
        whiskering_left_obj_map, category.comp_id, Lan_map_app, category.assoc]
      erw [colimit.ι_pre_assoc (Lan.diagram F H X) (costructured_arrow.map j.hom), category.id_comp, category.comp_id,
        colimit.ι_map]
      cases j
      cases j_right
      congr
      rw [costructured_arrow.map_mk, category.id_comp, costructured_arrow.mk])

variable [concrete_category.{u₁} E] [has_limits E] [has_colimits E]

variable [reflects_limits (forget E)] [preserves_filtered_colimits (forget E)]

variable [preserves_limits (forget E)]

/-- If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable instance Lan_preserves_finite_limits_of_flat (F : C ⥤ D) [representably_flat F] :
    preserves_finite_limits (Lan F.op : _ ⥤ Dᵒᵖ ⥤ E) :=
  ⟨fun J _ _ => by
    skip
    apply preserves_limits_of_shape_of_evaluation (Lan F.op : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
    intro K
    have : is_filtered (costructured_arrow F.op K) :=
      is_filtered.of_equivalence (structured_arrow_op_equivalence F (unop K))
    exact preserves_limits_of_shape_of_nat_iso (Lan_evaluation_iso_colim _ _ _).symm⟩

instance Lan_flat_of_flat (F : C ⥤ D) [representably_flat F] : representably_flat (Lan F.op : _ ⥤ Dᵒᵖ ⥤ E) :=
  flat_of_preserves_finite_limits _

variable [has_finite_limits C]

noncomputable instance Lan_preserves_finite_limits_of_preserves_finite_limits (F : C ⥤ D) [preserves_finite_limits F] :
    preserves_finite_limits (Lan F.op : _ ⥤ Dᵒᵖ ⥤ E) := by
  have := flat_of_preserves_finite_limits F
  infer_instance

theorem flat_iff_Lan_flat (F : C ⥤ D) : representably_flat F ↔ representably_flat (Lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun H => inferInstance, fun H => by
    skip
    have := preserves_finite_limits_of_flat (Lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    have : preserves_finite_limits F := ⟨fun _ _ _ => preserves_limit_of_Lan_presesrves_limit _ _⟩
    apply flat_of_preserves_finite_limits⟩

/-- If `C` is finitely complete, then `F : C ⥤ D` preserves finite limits iff
`Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves finite limits.
-/
noncomputable def preserves_finite_limits_iff_Lan_preserves_finite_limits (F : C ⥤ D) :
    preserves_finite_limits F ≃ preserves_finite_limits (Lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁) where
  toFun := fun _ => inferInstance
  invFun := fun _ => ⟨fun _ _ _ => preserves_limit_of_Lan_presesrves_limit _ _⟩
  left_inv := fun x => by
    cases x
    unfold preserves_finite_limits_of_flat
    congr
  right_inv := fun x => by
    cases x
    unfold preserves_finite_limits_of_flat
    congr
    unfold CategoryTheory.lanPreservesFiniteLimitsOfPreservesFiniteLimits CategoryTheory.lanPreservesFiniteLimitsOfFlat
    congr

end SmallCategory

end CategoryTheory

