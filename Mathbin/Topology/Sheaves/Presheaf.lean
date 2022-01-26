import Mathbin.CategoryTheory.Limits.KanExtension
import Mathbin.CategoryTheory.Adjunction.Default
import Mathbin.Topology.Category.Top.Opens

/-!
# Presheaves on a topological space

We define `presheaf C X` simply as `(opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* `pushforward_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C`
with notation `f _* ℱ`
and for `ℱ : X.presheaf C` provide the natural isomorphisms
* `pushforward.id : (𝟙 X) _* ℱ ≅ ℱ`
* `pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
along with their `@[simp]` lemmas.

We also define the functors `pushforward` and `pullback` between the categories
`X.presheaf C` and `Y.presheaf C`, and provide their adjunction at
`pushforward_pullback_adjunction`.
-/


universe v u

open CategoryTheory

open TopologicalSpace

open Opposite

variable (C : Type u) [category.{v} C]

namespace Top

/-- The category of `C`-valued presheaves on a (bundled) topological space `X`. -/
@[nolint has_inhabited_instance]
def presheaf (X : Top.{v}) :=
  opens Xᵒᵖ ⥤ C deriving category

variable {C}

namespace Presheaf

/-- Pushforward a presheaf on `X` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `Y`. -/
def pushforward_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
  (opens.map f).op ⋙ ℱ

infixl:80 " _* " => pushforward_obj

@[simp]
theorem pushforward_obj_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) (U : opens Yᵒᵖ) :
    (f _* ℱ).obj U = ℱ.obj ((opens.map f).op.obj U) :=
  rfl

@[simp]
theorem pushforward_obj_map {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) {U V : opens Yᵒᵖ} (i : U ⟶ V) :
    (f _* ℱ).map i = ℱ.map ((opens.map f).op.map i) :=
  rfl

/-- An equality of continuous maps induces a natural isomorphism between the pushforwards of a presheaf
along those maps.
-/
def pushforward_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) : f _* ℱ ≅ g _* ℱ :=
  iso_whisker_right (nat_iso.op (opens.map_iso f g h).symm) ℱ

theorem pushforward_eq' {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) : f _* ℱ = g _* ℱ := by
  rw [h]

@[simp]
theorem pushforward_eq_hom_app {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) U :
    (pushforward_eq h ℱ).Hom.app U =
      ℱ.map
        (by
          dsimp [functor.op]
          apply Quiver.Hom.op
          apply eq_to_hom
          rw [h]) :=
  by
  simp [pushforward_eq]

theorem pushforward_eq'_hom_app {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) U :
    nat_trans.app (eq_to_hom (pushforward_eq' h ℱ)) U =
      ℱ.map
        (eq_to_hom
          (by
            rw [h])) :=
  by
  simpa

@[simp]
theorem pushforward_eq_rfl {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) U :
    (pushforward_eq (rfl : f = f) ℱ).Hom.app (op U) = 𝟙 _ := by
  dsimp [pushforward_eq]
  simp

theorem pushforward_eq_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : X.presheaf C) :
    ℱ.pushforward_eq h₁ = ℱ.pushforward_eq h₂ :=
  rfl

namespace Pushforward

variable {X : Top.{v}} (ℱ : X.presheaf C)

/-- The natural isomorphism between the pushforward of a presheaf along the identity continuous map
and the original presheaf. -/
def id : 𝟙 X _* ℱ ≅ ℱ :=
  iso_whisker_right (nat_iso.op (opens.map_id X).symm) ℱ ≪≫ functor.left_unitor _

theorem id_eq : 𝟙 X _* ℱ = ℱ := by
  unfold pushforward_obj
  rw [opens.map_id_eq]
  erw [functor.id_comp]

@[simp]
theorem id_hom_app' U p : (id ℱ).Hom.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) := by
  dsimp [id]
  simp

attribute [local tidy] tactic.op_induction'

@[simp]
theorem id_hom_app U : (id ℱ).Hom.app U = ℱ.map (eq_to_hom (opens.op_map_id_obj U)) := by
  tidy

@[simp]
theorem id_inv_app' U p : (id ℱ).inv.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) := by
  dsimp [id]
  simp

/-- The natural isomorphism between
the pushforward of a presheaf along the composition of two continuous maps and
the corresponding pushforward of a pushforward. -/
def comp {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
  iso_whisker_right (nat_iso.op (opens.map_comp f g).symm) ℱ

theorem comp_eq {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ = g _* (f _* ℱ) :=
  rfl

@[simp]
theorem comp_hom_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) U : (comp ℱ f g).Hom.app U = 𝟙 _ := by
  dsimp [comp]
  tidy

@[simp]
theorem comp_inv_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) U : (comp ℱ f g).inv.app U = 𝟙 _ := by
  dsimp [comp]
  tidy

end Pushforward

/-- A morphism of presheaves gives rise to a morphisms of the pushforwards of those presheaves.
-/
@[simps]
def pushforward_map {X Y : Top.{v}} (f : X ⟶ Y) {ℱ 𝒢 : X.presheaf C} (α : ℱ ⟶ 𝒢) : f _* ℱ ⟶ f _* 𝒢 where
  app := fun U => α.app _
  naturality' := fun U V i => by
    erw [α.naturality]
    rfl

open CategoryTheory.Limits

section Pullback

variable [has_colimits C]

noncomputable section

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf on `X`.

This is defined in terms of left Kan extensions, which is just a fancy way of saying
"take the colimits over the open sets whose preimage contains U".
-/
@[simps]
def pullback_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : Y.presheaf C) : X.presheaf C :=
  (Lan (opens.map f).op).obj ℱ

/-- Pulling back along continuous maps is functorial. -/
def pullback_map {X Y : Top.{v}} (f : X ⟶ Y) {ℱ 𝒢 : Y.presheaf C} (α : ℱ ⟶ 𝒢) : pullback_obj f ℱ ⟶ pullback_obj f 𝒢 :=
  (Lan (opens.map f).op).map α

/-- If `f '' U` is open, then `f⁻¹ℱ U ≅ ℱ (f '' U)`.  -/
@[simps]
def pullback_obj_obj_of_image_open {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : Y.presheaf C) (U : opens X) (H : IsOpen (f '' U)) :
    (pullback_obj f ℱ).obj (op U) ≅ ℱ.obj (op ⟨_, H⟩) := by
  let x : costructured_arrow (opens.map f).op (op U) :=
    { left := op ⟨f '' U, H⟩,
      Hom :=
        ((@hom_of_le _ _ _ ((opens.map f).obj ⟨_, H⟩) (set.image_preimage.le_u_l _)).op :
          op ((opens.map f).obj ⟨⇑f '' ↑U, H⟩) ⟶ op U) }
  have hx : is_terminal x :=
    { lift := fun s => by
        fapply costructured_arrow.hom_mk
        change op (unop _) ⟶ op (⟨_, H⟩ : opens _)
        refine' (hom_of_le _).op
        exact (Set.image_subset f s.X.hom.unop.le).trans (set.image_preimage.l_u_le ↑(unop s.X.left))
        simp }
  exact is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) (colimit_of_diagram_terminal hx _)

namespace Pullback

variable {X Y : Top.{v}} (ℱ : Y.presheaf C)

/-- The pullback along the identity is isomorphic to the original presheaf. -/
def id : pullback_obj (𝟙 _) ℱ ≅ ℱ :=
  nat_iso.of_components
    (fun U =>
      pullback_obj_obj_of_image_open (𝟙 _) ℱ (unop U)
          (by
            simpa using U.unop.2) ≪≫
        ℱ.map_iso
          (eq_to_iso
            (by
              simp )))
    fun U V i => by
    ext
    simp [-eq_to_hom_map, -eq_to_iso_map]
    erw [colimit.pre_desc_assoc]
    erw [colimit.ι_desc_assoc]
    erw [colimit.ι_desc_assoc]
    dsimp
    simp only [← ℱ.map_comp]
    congr

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:57:31: expecting tactic arg
theorem id_inv_app (U : opens Y) :
    (id ℱ).inv.app (op U) =
      colimit.ι (Lan.diagram (opens.map (𝟙 Y)).op ℱ (op U))
        (@costructured_arrow.mk _ _ _ _ _ (op U) _
          (eq_to_hom
            (by
              simp ))) :=
  by
  dsimp [id]
  simp [-eq_to_hom_map, -eq_to_iso_map]
  dsimp [colimit_of_diagram_terminal]
  delta' Lan.diagram
  refine' Eq.trans _ (category.id_comp _)
  rw [← ℱ.map_id]
  congr
  any_goals {
  }
  all_goals
    simp

end Pullback

end Pullback

variable (C)

/-- The pushforward functor.
-/
def pushforward {X Y : Top.{v}} (f : X ⟶ Y) : X.presheaf C ⥤ Y.presheaf C where
  obj := pushforward_obj f
  map := @pushforward_map _ _ X Y f

@[simp]
theorem pushforward_map_app' {X Y : Top.{v}} (f : X ⟶ Y) {ℱ 𝒢 : X.presheaf C} (α : ℱ ⟶ 𝒢) {U : opens Yᵒᵖ} :
    ((pushforward C f).map α).app U = α.app (op <| (opens.map f).obj U.unop) :=
  rfl

theorem id_pushforward {X : Top.{v}} : pushforward C (𝟙 X) = 𝟭 (X.presheaf C) := by
  apply CategoryTheory.Functor.ext
  · intros
    ext U
    have h := f.congr
    erw [h (opens.op_map_id_obj U)]
    simpa
    
  · intros
    apply pushforward.id_eq
    

section Iso

/-- A homeomorphism of spaces gives an equivalence of categories of presheaves. -/
@[simps]
def presheaf_equiv_of_iso {X Y : Top} (H : X ≅ Y) : X.presheaf C ≌ Y.presheaf C :=
  equivalence.congr_left (opens.map_map_iso H).symm.op

variable {C}

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def to_pushforward_of_iso {X Y : Top} (H : X ≅ Y) {ℱ : X.presheaf C} {𝒢 : Y.presheaf C} (α : H.hom _* ℱ ⟶ 𝒢) :
    ℱ ⟶ H.inv _* 𝒢 :=
  (presheaf_equiv_of_iso _ H).toAdjunction.homEquiv ℱ 𝒢 α

@[simp]
theorem to_pushforward_of_iso_app {X Y : Top} (H₁ : X ≅ Y) {ℱ : X.presheaf C} {𝒢 : Y.presheaf C} (H₂ : H₁.hom _* ℱ ⟶ 𝒢)
    (U : opens Xᵒᵖ) :
    (to_pushforward_of_iso H₁ H₂).app U =
      ℱ.map
          (eq_to_hom
            (by
              simp [opens.map, Set.preimage_preimage])) ≫
        H₂.app (op ((opens.map H₁.inv).obj (unop U))) :=
  by
  delta' to_pushforward_of_iso
  simp only [Equivₓ.to_fun_as_coe, nat_trans.comp_app, equivalence.equivalence_mk'_unit, eq_to_hom_map,
    presheaf_equiv_of_iso_unit_iso_hom_app_app, equivalence.to_adjunction, equivalence.equivalence_mk'_counit,
    presheaf_equiv_of_iso_inverse_map_app, adjunction.mk_of_unit_counit_hom_equiv_apply]
  congr

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def pushforward_to_of_iso {X Y : Top} (H₁ : X ≅ Y) {ℱ : Y.presheaf C} {𝒢 : X.presheaf C} (H₂ : ℱ ⟶ H₁.hom _* 𝒢) :
    H₁.inv _* ℱ ⟶ 𝒢 :=
  ((presheaf_equiv_of_iso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂

@[simp]
theorem pushforward_to_of_iso_app {X Y : Top} (H₁ : X ≅ Y) {ℱ : Y.presheaf C} {𝒢 : X.presheaf C} (H₂ : ℱ ⟶ H₁.hom _* 𝒢)
    (U : opens Xᵒᵖ) :
    (pushforward_to_of_iso H₁ H₂).app U =
      H₂.app (op ((opens.map H₁.inv).obj (unop U))) ≫
        𝒢.map
          (eq_to_hom
            (by
              simp [opens.map, Set.preimage_preimage])) :=
  by
  simpa [pushforward_to_of_iso, equivalence.to_adjunction]

end Iso

variable (C) [has_colimits C]

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `X`. -/
@[simps map_app]
def pullback {X Y : Top.{v}} (f : X ⟶ Y) : Y.presheaf C ⥤ X.presheaf C :=
  Lan (opens.map f).op

@[simp]
theorem pullback_obj_eq_pullback_obj {C} [category C] [has_colimits C] {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : Y.presheaf C) :
    (pullback C f).obj ℱ = pullback_obj f ℱ :=
  rfl

/-- The pullback and pushforward along a continuous map are adjoint to each other. -/
@[simps unit_app_app counit_app_app]
def pushforward_pullback_adjunction {X Y : Top.{v}} (f : X ⟶ Y) : pullback C f ⊣ pushforward C f :=
  Lan.adjunction _ _

/-- Pulling back along a homeomorphism is the same as pushing forward along its inverse. -/
def pullback_hom_iso_pushforward_inv {X Y : Top.{v}} (H : X ≅ Y) : pullback C H.hom ≅ pushforward C H.inv :=
  Adjunction.leftAdjointUniq (pushforward_pullback_adjunction C H.hom) (presheaf_equiv_of_iso C H.symm).toAdjunction

/-- Pulling back along the inverse of a homeomorphism is the same as pushing forward along it. -/
def pullback_inv_iso_pushforward_hom {X Y : Top.{v}} (H : X ≅ Y) : pullback C H.inv ≅ pushforward C H.hom :=
  Adjunction.leftAdjointUniq (pushforward_pullback_adjunction C H.inv) (presheaf_equiv_of_iso C H).toAdjunction

end Presheaf

end Top

