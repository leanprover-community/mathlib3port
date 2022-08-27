/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathbin.CategoryTheory.Sites.Sheaf

/-!

# The plus construction for presheaves.

This file contains the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`
where `C` is endowed with a grothendieck topology `J`.

See <https://stacks.math.columbia.edu/tag/00W1> for details.

-/


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w} [Category.{max v u} D]

noncomputable section

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]

variable (P : Cᵒᵖ ⥤ D)

/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
def diagram (X : C) : (J.cover X)ᵒᵖ ⥤ D where
  obj := fun S => multiequalizer (S.unop.index P)
  map := fun S T f =>
    (multiequalizer.lift _ _ fun I => multiequalizer.ι (S.unop.index P) (I.map f.unop)) fun I =>
      multiequalizer.condition (S.unop.index P) (I.map f.unop)
  map_id' := fun S => by
    ext I
    cases I
    simpa
  map_comp' := fun S T W f g => by
    ext I
    simpa

/-- A helper definition used to define the morphisms for `plus`. -/
@[simps]
def diagramPullback {X Y : C} (f : X ⟶ Y) : J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X where
  app := fun S =>
    (multiequalizer.lift _ _ fun I => multiequalizer.ι (S.unop.index P) I.base) fun I =>
      multiequalizer.condition (S.unop.index P) I.base
  naturality' := fun S T f => by
    ext
    dsimp'
    simpa

/-- A natural transformation `P ⟶ Q` induces a natural transformation
between diagrams whose colimits define the values of `plus`. -/
@[simps]
def diagramNatTrans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) : J.diagram P X ⟶ J.diagram Q X where
  app := fun W =>
    multiequalizer.lift _ _ (fun i => multiequalizer.ι _ i ≫ η.app _)
      (by
        intro i
        erw [category.assoc, category.assoc, ← η.naturality, ← η.naturality, ← category.assoc, ← category.assoc,
          multiequalizer.condition]
        rfl)
  naturality' := fun _ _ _ => by
    dsimp'
    ext
    simpa

@[simp]
theorem diagram_nat_trans_id (X : C) (P : Cᵒᵖ ⥤ D) : J.diagramNatTrans (𝟙 P) X = 𝟙 (J.diagram P X) := by
  ext
  dsimp'
  simp only [multiequalizer.lift_ι, category.id_comp]
  erw [category.comp_id]

@[simp]
theorem diagram_nat_trans_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) :
    J.diagramNatTrans (η ≫ γ) X = J.diagramNatTrans η X ≫ J.diagramNatTrans γ X := by
  ext
  dsimp'
  simp

variable (D)

/-- `J.diagram P`, as a functor in `P`. -/
@[simps]
def diagramFunctor (X : C) : (Cᵒᵖ ⥤ D) ⥤ (J.cover X)ᵒᵖ ⥤ D where
  obj := fun P => J.diagram P X
  map := fun P Q η => J.diagramNatTrans η X
  map_id' := fun P => J.diagram_nat_trans_id _ _
  map_comp' := fun P Q R η γ => J.diagram_nat_trans_comp _ _ _

variable {D}

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

/-- The plus construction, associating a presheaf to any presheaf.
See `plus_functor` below for a functorial version. -/
def plusObj : Cᵒᵖ ⥤ D where
  obj := fun X => colimit (J.diagram P X.unop)
  map := fun X Y f => colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _
  map_id' := by
    intro X
    ext S
    dsimp'
    simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.comp_id]
    let e := S.unop.pullback_id
    dsimp' only [functor.op, pullback_obj]
    erw [← colimit.w _ e.inv.op, ← category.assoc]
    convert category.id_comp _
    ext I
    dsimp'
    simp only [multiequalizer.lift_ι, category.id_comp, category.assoc]
    dsimp' [cover.arrow.map, cover.arrow.base]
    cases I
    congr
    simp
  map_comp' := by
    intro X Y Z f g
    ext S
    dsimp'
    simp only [diagram_pullback_app, colimit.ι_pre_assoc, colimit.ι_pre, ι_colim_map_assoc, category.assoc]
    let e := S.unop.pullback_comp g.unop f.unop
    dsimp' only [functor.op, pullback_obj]
    erw [← colimit.w _ e.inv.op, ← category.assoc, ← category.assoc]
    congr 1
    ext I
    dsimp'
    simp only [multiequalizer.lift_ι, category.assoc]
    cases I
    dsimp' only [cover.arrow.base, cover.arrow.map]
    congr 2
    simp

/-- An auxiliary definition used in `plus` below. -/
def plusMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plusObj P ⟶ J.plusObj Q where
  app := fun X => colimMap (J.diagramNatTrans η X.unop)
  naturality' := by
    intro X Y f
    dsimp' [plus_obj]
    ext
    simp only [diagram_pullback_app, ι_colim_map, colimit.ι_pre_assoc, colimit.ι_pre, ι_colim_map_assoc, category.assoc]
    simp_rw [← category.assoc]
    congr 1
    ext
    dsimp'
    simpa

@[simp]
theorem plus_map_id (P : Cᵒᵖ ⥤ D) : J.plusMap (𝟙 P) = 𝟙 _ := by
  ext x : 2
  dsimp' only [plus_map, plus_obj]
  rw [J.diagram_nat_trans_id, nat_trans.id_app]
  ext
  dsimp'
  simp

@[simp]
theorem plus_map_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) : J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ := by
  ext : 2
  dsimp' only [plus_map]
  rw [J.diagram_nat_trans_comp]
  ext
  dsimp'
  simp

variable (D)

/-- The plus construction, a functor sending `P` to `J.plus_obj P`. -/
@[simps]
def plusFunctor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D where
  obj := fun P => J.plusObj P
  map := fun P Q η => J.plusMap η
  map_id' := fun _ => plus_map_id _ _
  map_comp' := fun _ _ _ _ _ => plus_map_comp _ _ _

variable {D}

/-- The canonical map from `P` to `J.plus.obj P`.
See `to_plus` for a functorial version. -/
def toPlus : P ⟶ J.plusObj P where
  app := fun X => Cover.toMultiequalizer (⊤ : J.cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤)
  naturality' := by
    intro X Y f
    dsimp' [plus_obj]
    delta' cover.to_multiequalizer
    simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.assoc]
    dsimp' only [functor.op, unop_op]
    let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
    rw [← colimit.w _ e.op, ← category.assoc, ← category.assoc, ← category.assoc]
    congr 1
    ext
    dsimp'
    simp only [multiequalizer.lift_ι, category.assoc]
    dsimp' [cover.arrow.base]
    simp

@[simp, reassoc]
theorem to_plus_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η := by
  ext
  dsimp' [to_plus, plus_map]
  delta' cover.to_multiequalizer
  simp only [ι_colim_map, category.assoc]
  simp_rw [← category.assoc]
  congr 1
  ext
  dsimp'
  simp

variable (D)

/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
def toPlusNatTrans : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D where
  app := fun P => J.toPlus P
  naturality' := fun _ _ _ => to_plus_naturality _ _

variable {D}

/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
@[simp]
theorem plus_map_to_plus : J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P) := by
  ext X S
  dsimp' [to_plus, plus_obj, plus_map]
  delta' cover.to_multiequalizer
  simp only [ι_colim_map]
  let e : S.unop ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
  simp_rw [← colimit.w _ e.op, ← category.assoc]
  congr 1
  ext I
  dsimp'
  simp only [diagram_pullback_app, colimit.ι_pre, multiequalizer.lift_ι, ι_colim_map_assoc, category.assoc]
  dsimp' only [functor.op]
  let ee : (J.pullback (I.map e).f).obj S.unop ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
  simp_rw [← colimit.w _ ee.op, ← category.assoc]
  congr 1
  ext II
  dsimp'
  simp only [limit.lift_π, multifork.of_ι_π_app, multiequalizer.lift_ι, category.assoc]
  dsimp' [multifork.of_ι]
  convert
    multiequalizer.condition (S.unop.index P)
      ⟨_, _, _, II.f, 𝟙 _, I.f, II.f ≫ I.f, I.hf, sieve.downward_closed _ I.hf _, by
        simp ⟩
  · cases I
    rfl
    
  · dsimp' [cover.index]
    erw [P.map_id, category.comp_id]
    rfl
    

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[":", expr ∀ X, is_iso ((J.to_plus P).app X)]]
-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[":", expr is_iso (colimit.ι (J.diagram P X.unop) (op «expr⊤»()))]]
-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[":", expr ∀ (S T : «expr ᵒᵖ»(J.cover X.unop)) (f : «expr ⟶ »(S, T)), is_iso ((J.diagram P X.unop).map f)]]
theorem is_iso_to_plus_of_is_sheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P) := by
  rw [presheaf.is_sheaf_iff_multiequalizer] at hP
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[\":\", expr ∀ X, is_iso ((J.to_plus P).app X)]]"
  · apply nat_iso.is_iso_of_is_iso_app
    
  intro X
  dsimp'
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[\":\", expr is_iso (colimit.ι (J.diagram P X.unop) (op «expr⊤»()))]]"
  · apply is_iso.comp_is_iso
    
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsufficesI #[[\":\", expr ∀ (S T : «expr ᵒᵖ»(J.cover X.unop)) (f : «expr ⟶ »(S, T)), is_iso ((J.diagram P X.unop).map f)]]"
  · apply is_iso_ι_of_is_initial (initial_op_of_terminal is_terminal_top)
    
  intro S T e
  have : S.unop.to_multiequalizer P ≫ (J.diagram P X.unop).map e = T.unop.to_multiequalizer P := by
    ext
    dsimp'
    simpa
  have : (J.diagram P X.unop).map e = inv (S.unop.to_multiequalizer P) ≫ T.unop.to_multiequalizer P := by
    simp [← this]
  rw [this]
  infer_instance

/-- The natural isomorphism between `P` and `P⁺` when `P` is a sheaf. -/
def isoToPlus (hP : Presheaf.IsSheaf J P) : P ≅ J.plusObj P :=
  letI := is_iso_to_plus_of_is_sheaf J P hP
  as_iso (J.to_plus P)

@[simp]
theorem iso_to_plus_hom (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).Hom = J.toPlus P :=
  rfl

/-- Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf. -/
def plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.plusObj P ⟶ Q :=
  J.plusMap η ≫ (J.isoToPlus Q hQ).inv

@[simp, reassoc]
theorem to_plus_plus_lift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.toPlus P ≫ J.plusLift η hQ = η :=
  by
  dsimp' [plus_lift]
  rw [← category.assoc]
  rw [iso.comp_inv_eq]
  dsimp' only [iso_to_plus, as_iso]
  rw [to_plus_naturality]

theorem plus_lift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.plusObj P ⟶ Q)
    (hγ : J.toPlus P ≫ γ = η) : γ = J.plusLift η hQ := by
  dsimp' only [plus_lift]
  rw [iso.eq_comp_inv, ← hγ, plus_map_comp]
  dsimp'
  simp

theorem plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) : η = γ := by
  have : γ = J.plus_lift (J.to_plus P ≫ γ) hQ := by
    apply plus_lift_unique
    rfl
  rw [this]
  apply plus_lift_unique
  exact h

@[simp]
theorem iso_to_plus_inv (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).inv = J.plusLift (𝟙 _) hP := by
  apply J.plus_lift_unique
  rw [iso.comp_inv_eq, category.id_comp]
  rfl

@[simp]
theorem plus_map_plus_lift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR := by
  apply J.plus_lift_unique
  rw [← category.assoc, ← J.to_plus_naturality, category.assoc, J.to_plus_plus_lift]

end CategoryTheory.GrothendieckTopology

