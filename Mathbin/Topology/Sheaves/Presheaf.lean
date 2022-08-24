/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro, Reid Barton, Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.KanExtension
import Mathbin.CategoryTheory.Adjunction.Default
import Mathbin.Topology.Category.Top.Opens

/-!
# Presheaves on a topological space

We define `presheaf C X` simply as `(opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* `pushforward_obj {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C`
with notation `f _* ℱ`
and for `ℱ : X.presheaf C` provide the natural isomorphisms
* `pushforward.id : (𝟙 X) _* ℱ ≅ ℱ`
* `pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
along with their `@[simp]` lemmas.

We also define the functors `pushforward` and `pullback` between the categories
`X.presheaf C` and `Y.presheaf C`, and provide their adjunction at
`pushforward_pullback_adjunction`.
-/


universe w v u

open CategoryTheory

open TopologicalSpace

open Opposite

variable (C : Type u) [Category.{v} C]

namespace Top

/-- The category of `C`-valued presheaves on a (bundled) topological space `X`. -/
@[nolint has_nonempty_instance]
def Presheaf (X : Top.{w}) :=
  (Opens X)ᵒᵖ ⥤ C deriving Category

variable {C}

namespace Presheaf

/-- Pushforward a presheaf on `X` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `Y`. -/
def pushforwardObj {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.Presheaf C) : Y.Presheaf C :=
  (Opens.map f).op ⋙ ℱ

-- mathport name: «expr _* »
infixl:80 " _* " => pushforwardObj

@[simp]
theorem pushforward_obj_obj {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.Presheaf C) (U : (Opens Y)ᵒᵖ) :
    (f _* ℱ).obj U = ℱ.obj ((Opens.map f).op.obj U) :=
  rfl

@[simp]
theorem pushforward_obj_map {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.Presheaf C) {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    (f _* ℱ).map i = ℱ.map ((Opens.map f).op.map i) :=
  rfl

/-- An equality of continuous maps induces a natural isomorphism between the pushforwards of a presheaf
along those maps.
-/
def pushforwardEq {X Y : Top.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) : f _* ℱ ≅ g _* ℱ :=
  isoWhiskerRight (NatIso.op (Opens.mapIso f g h).symm) ℱ

theorem pushforward_eq' {X Y : Top.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) : f _* ℱ = g _* ℱ := by
  rw [h]

@[simp]
theorem pushforward_eq_hom_app {X Y : Top.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) (U) :
    (pushforwardEq h ℱ).Hom.app U =
      ℱ.map
        (by
          dsimp' [functor.op]
          apply Quiver.Hom.op
          apply eq_to_hom
          rw [h]) :=
  by
  simp [pushforward_eq]

theorem pushforward_eq'_hom_app {X Y : Top.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) (U) :
    NatTrans.app (eqToHom (pushforward_eq' h ℱ)) U =
      ℱ.map
        (eqToHom
          (by
            rw [h])) :=
  by
  simpa [eq_to_hom_map]

@[simp]
theorem pushforward_eq_rfl {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.Presheaf C) (U) :
    (pushforwardEq (rfl : f = f) ℱ).Hom.app (op U) = 𝟙 _ := by
  dsimp' [pushforward_eq]
  simp

theorem pushforward_eq_eq {X Y : Top.{w}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : X.Presheaf C) :
    ℱ.pushforwardEq h₁ = ℱ.pushforwardEq h₂ :=
  rfl

namespace Pushforward

variable {X : Top.{w}} (ℱ : X.Presheaf C)

/-- The natural isomorphism between the pushforward of a presheaf along the identity continuous map
and the original presheaf. -/
def id : 𝟙 X _* ℱ ≅ ℱ :=
  isoWhiskerRight (NatIso.op (Opens.mapId X).symm) ℱ ≪≫ Functor.leftUnitor _

theorem id_eq : 𝟙 X _* ℱ = ℱ := by
  unfold pushforward_obj
  rw [opens.map_id_eq]
  erw [functor.id_comp]

@[simp]
theorem id_hom_app' (U) (p) : (id ℱ).Hom.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) := by
  dsimp' [id]
  simp

attribute [local tidy] tactic.op_induction'

@[simp]
theorem id_hom_app (U) : (id ℱ).Hom.app U = ℱ.map (eqToHom (Opens.op_map_id_obj U)) := by
  tidy

@[simp]
theorem id_inv_app' (U) (p) : (id ℱ).inv.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) := by
  dsimp' [id]
  simp

/-- The natural isomorphism between
the pushforward of a presheaf along the composition of two continuous maps and
the corresponding pushforward of a pushforward. -/
def comp {Y Z : Top.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
  isoWhiskerRight (NatIso.op (Opens.mapComp f g).symm) ℱ

theorem comp_eq {Y Z : Top.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ = g _* (f _* ℱ) :=
  rfl

@[simp]
theorem comp_hom_app {Y Z : Top.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (comp ℱ f g).Hom.app U = 𝟙 _ := by
  dsimp' [comp]
  tidy

@[simp]
theorem comp_inv_app {Y Z : Top.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (comp ℱ f g).inv.app U = 𝟙 _ := by
  dsimp' [comp]
  tidy

end Pushforward

/-- A morphism of presheaves gives rise to a morphisms of the pushforwards of those presheaves.
-/
@[simps]
def pushforwardMap {X Y : Top.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢) : f _* ℱ ⟶ f _* 𝒢 where
  app := fun U => α.app _
  naturality' := fun U V i => by
    erw [α.naturality]
    rfl

open CategoryTheory.Limits

section Pullback

variable [HasColimits C]

noncomputable section

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf on `X`.

This is defined in terms of left Kan extensions, which is just a fancy way of saying
"take the colimits over the open sets whose preimage contains U".
-/
@[simps]
def pullbackObj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) : X.Presheaf C :=
  (lan (Opens.map f).op).obj ℱ

/-- Pulling back along continuous maps is functorial. -/
def pullbackMap {X Y : Top.{v}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Presheaf C} (α : ℱ ⟶ 𝒢) : pullbackObj f ℱ ⟶ pullbackObj f 𝒢 :=
  (lan (Opens.map f).op).map α

/-- If `f '' U` is open, then `f⁻¹ℱ U ≅ ℱ (f '' U)`.  -/
@[simps]
def pullbackObjObjOfImageOpen {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) (U : Opens X) (H : IsOpen (f '' U)) :
    (pullbackObj f ℱ).obj (op U) ≅ ℱ.obj (op ⟨_, H⟩) := by
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

variable {X Y : Top.{v}} (ℱ : Y.Presheaf C)

/-- The pullback along the identity is isomorphic to the original presheaf. -/
def id : pullbackObj (𝟙 _) ℱ ≅ ℱ :=
  NatIso.ofComponents
    (fun U =>
      pullbackObjObjOfImageOpen (𝟙 _) ℱ (unop U)
          (by
            simpa using U.unop.2) ≪≫
        ℱ.mapIso
          (eqToIso
            (by
              simp )))
    fun U V i => by
    ext
    simp
    erw [colimit.pre_desc_assoc]
    erw [colimit.ι_desc_assoc]
    erw [colimit.ι_desc_assoc]
    dsimp'
    simp only [← ℱ.map_comp]
    congr

theorem id_inv_app (U : Opens Y) :
    (id ℱ).inv.app (op U) =
      colimit.ι (Lan.diagram (Opens.map (𝟙 Y)).op ℱ (op U))
        (@CostructuredArrow.mk _ _ _ _ _ (op U) _
          (eqToHom
            (by
              simp ))) :=
  by
  rw [← category.id_comp ((id ℱ).inv.app (op U)), ← nat_iso.app_inv, iso.comp_inv_eq]
  dsimp' [id]
  rw [colimit.ι_desc_assoc]
  dsimp'
  rw [← ℱ.map_comp, ← ℱ.map_id]
  rfl

end Pullback

end Pullback

variable (C)

/-- The pushforward functor.
-/
def pushforward {X Y : Top.{v}} (f : X ⟶ Y) : X.Presheaf C ⥤ Y.Presheaf C where
  obj := pushforwardObj f
  map := @pushforwardMap _ _ X Y f

@[simp]
theorem pushforward_map_app' {X Y : Top.{v}} (f : X ⟶ Y) {ℱ 𝒢 : X.Presheaf C} (α : ℱ ⟶ 𝒢) {U : (Opens Y)ᵒᵖ} :
    ((pushforward C f).map α).app U = α.app (op <| (Opens.map f).obj U.unop) :=
  rfl

theorem id_pushforward {X : Top.{v}} : pushforward C (𝟙 X) = 𝟭 (X.Presheaf C) := by
  apply CategoryTheory.Functor.ext
  · intros
    ext U
    have h := f.congr
    erw [h (opens.op_map_id_obj U)]
    simpa [eq_to_hom_map]
    
  · intros
    apply pushforward.id_eq
    

section Iso

/-- A homeomorphism of spaces gives an equivalence of categories of presheaves. -/
@[simps]
def presheafEquivOfIso {X Y : Top} (H : X ≅ Y) : X.Presheaf C ≌ Y.Presheaf C :=
  Equivalence.congrLeft (Opens.mapMapIso H).symm.op

variable {C}

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def toPushforwardOfIso {X Y : Top} (H : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C} (α : H.Hom _* ℱ ⟶ 𝒢) :
    ℱ ⟶ H.inv _* 𝒢 :=
  (presheafEquivOfIso _ H).toAdjunction.homEquiv ℱ 𝒢 α

@[simp]
theorem to_pushforward_of_iso_app {X Y : Top} (H₁ : X ≅ Y) {ℱ : X.Presheaf C} {𝒢 : Y.Presheaf C} (H₂ : H₁.Hom _* ℱ ⟶ 𝒢)
    (U : (Opens X)ᵒᵖ) :
    (toPushforwardOfIso H₁ H₂).app U =
      ℱ.map
          (eqToHom
            (by
              simp [opens.map, Set.preimage_preimage])) ≫
        H₂.app (op ((Opens.map H₁.inv).obj (unop U))) :=
  by
  delta' to_pushforward_of_iso
  simp only [Equivₓ.to_fun_as_coe, nat_trans.comp_app, equivalence.equivalence_mk'_unit, eq_to_hom_map, eq_to_hom_op,
    eq_to_hom_trans, presheaf_equiv_of_iso_unit_iso_hom_app_app, equivalence.to_adjunction,
    equivalence.equivalence_mk'_counit, presheaf_equiv_of_iso_inverse_map_app,
    adjunction.mk_of_unit_counit_hom_equiv_apply]
  congr

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def pushforwardToOfIso {X Y : Top} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C} (H₂ : ℱ ⟶ H₁.Hom _* 𝒢) :
    H₁.inv _* ℱ ⟶ 𝒢 :=
  ((presheafEquivOfIso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂

@[simp]
theorem pushforward_to_of_iso_app {X Y : Top} (H₁ : X ≅ Y) {ℱ : Y.Presheaf C} {𝒢 : X.Presheaf C} (H₂ : ℱ ⟶ H₁.Hom _* 𝒢)
    (U : (Opens X)ᵒᵖ) :
    (pushforwardToOfIso H₁ H₂).app U =
      H₂.app (op ((Opens.map H₁.inv).obj (unop U))) ≫
        𝒢.map
          (eqToHom
            (by
              simp [opens.map, Set.preimage_preimage])) :=
  by
  simpa [pushforward_to_of_iso, equivalence.to_adjunction]

end Iso

variable (C) [HasColimits C]

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `X`. -/
@[simps map_app]
def pullback {X Y : Top.{v}} (f : X ⟶ Y) : Y.Presheaf C ⥤ X.Presheaf C :=
  lan (Opens.map f).op

@[simp]
theorem pullback_obj_eq_pullback_obj {C} [Category C] [HasColimits C] {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : Y.Presheaf C) :
    (pullback C f).obj ℱ = pullbackObj f ℱ :=
  rfl

/-- The pullback and pushforward along a continuous map are adjoint to each other. -/
@[simps unit_app_app counit_app_app]
def pushforwardPullbackAdjunction {X Y : Top.{v}} (f : X ⟶ Y) : pullback C f ⊣ pushforward C f :=
  lan.adjunction _ _

/-- Pulling back along a homeomorphism is the same as pushing forward along its inverse. -/
def pullbackHomIsoPushforwardInv {X Y : Top.{v}} (H : X ≅ Y) : pullback C H.Hom ≅ pushforward C H.inv :=
  Adjunction.leftAdjointUniq (pushforwardPullbackAdjunction C H.Hom) (presheafEquivOfIso C H.symm).toAdjunction

/-- Pulling back along the inverse of a homeomorphism is the same as pushing forward along it. -/
def pullbackInvIsoPushforwardHom {X Y : Top.{v}} (H : X ≅ Y) : pullback C H.inv ≅ pushforward C H.Hom :=
  Adjunction.leftAdjointUniq (pushforwardPullbackAdjunction C H.inv) (presheafEquivOfIso C H).toAdjunction

end Presheaf

end Top

