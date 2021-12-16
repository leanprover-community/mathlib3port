import Mathbin.CategoryTheory.Sites.Sheaf

/-!

# The plus construction for presheaves.

This file contains the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`
where `C` is endowed with a grothendieck topology `J`.

See https://stacks.math.columbia.edu/tag/00W1 for details.

-/


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w v u

variable {C : Type u} [category.{v} C] (J : grothendieck_topology C)

variable {D : Type w} [category.{max v u} D]

noncomputable section 

variable [∀ P : Cᵒᵖ ⥤ D X : C S : J.cover X, has_multiequalizer (S.index P)]

variable (P : Cᵒᵖ ⥤ D)

/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
def diagram (X : C) : J.cover Xᵒᵖ ⥤ D :=
  { obj := fun S => multiequalizer (S.unop.index P),
    map :=
      fun S T f =>
        (multiequalizer.lift _ _ fun I => multiequalizer.ι (S.unop.index P) (I.map f.unop))$
          fun I => multiequalizer.condition (S.unop.index P) (I.map f.unop),
    map_id' :=
      fun S =>
        by 
          ext I 
          cases I 
          simpa,
    map_comp' :=
      fun S T W f g =>
        by 
          ext I 
          simpa }

/-- A helper definition used to define the morphisms for `plus`. -/
@[simps]
def diagram_pullback {X Y : C} (f : X ⟶ Y) : J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X :=
  { app :=
      fun S =>
        (multiequalizer.lift _ _ fun I => multiequalizer.ι (S.unop.index P) I.base)$
          fun I => multiequalizer.condition (S.unop.index P) I.base,
    naturality' :=
      fun S T f =>
        by 
          ext 
          dsimp 
          simpa }

/-- A natural transformation `P ⟶ Q` induces a natural transformation
between diagrams whose colimits define the values of `plus`. -/
@[simps]
def diagram_nat_trans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) : J.diagram P X ⟶ J.diagram Q X :=
  { app :=
      fun W =>
        multiequalizer.lift _ _ (fun i => multiequalizer.ι _ i ≫ η.app _)
          (by 
            intro i 
            erw [category.assoc, category.assoc, ←η.naturality, ←η.naturality, ←category.assoc, ←category.assoc,
              multiequalizer.condition]
            rfl),
    naturality' :=
      fun _ _ _ =>
        by 
          dsimp 
          ext 
          simpa }

@[simp]
theorem diagram_nat_trans_id (X : C) (P : Cᵒᵖ ⥤ D) : J.diagram_nat_trans (𝟙 P) X = 𝟙 (J.diagram P X) :=
  by 
    ext 
    dsimp 
    simp only [multiequalizer.lift_ι, category.id_comp]
    erw [category.comp_id]

@[simp]
theorem diagram_nat_trans_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) :
  J.diagram_nat_trans (η ≫ γ) X = J.diagram_nat_trans η X ≫ J.diagram_nat_trans γ X :=
  by 
    ext 
    dsimp 
    simp 

variable [∀ X : C, has_colimits_of_shape (J.cover Xᵒᵖ) D]

/-- The plus construction, associating a presheaf to any presheaf.
See `plus_functor` below for a functorial version. -/
def plus_obj : Cᵒᵖ ⥤ D :=
  { obj := fun X => colimit (J.diagram P X.unop),
    map := fun X Y f => colim_map (J.diagram_pullback P f.unop) ≫ colimit.pre _ _,
    map_id' :=
      by 
        intro X 
        ext S 
        dsimp 
        simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.comp_id]
        let e := S.unop.pullback_id 
        dsimp only [functor.op, pullback_obj]
        erw [←colimit.w _ e.inv.op, ←category.assoc]
        convert category.id_comp _ 
        ext I 
        dsimp 
        simp only [multiequalizer.lift_ι, category.id_comp, category.assoc]
        dsimp [cover.arrow.map, cover.arrow.base]
        cases I 
        congr 
        simp ,
    map_comp' :=
      by 
        intro X Y Z f g 
        ext S 
        dsimp 
        simp only [diagram_pullback_app, colimit.ι_pre_assoc, colimit.ι_pre, ι_colim_map_assoc, category.assoc]
        let e := S.unop.pullback_comp g.unop f.unop 
        dsimp only [functor.op, pullback_obj]
        erw [←colimit.w _ e.inv.op, ←category.assoc, ←category.assoc]
        congr 1 
        ext I 
        dsimp 
        simp only [multiequalizer.lift_ι, category.assoc]
        cases I 
        dsimp only [cover.arrow.base, cover.arrow.map]
        congr 2
        simp  }

/-- An auxiliary definition used in `plus` below. -/
def plus_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plus_obj P ⟶ J.plus_obj Q :=
  { app := fun X => colim_map (J.diagram_nat_trans η X.unop),
    naturality' :=
      by 
        intro X Y f 
        dsimp [plus_obj]
        ext 
        simp only [diagram_pullback_app, ι_colim_map, colimit.ι_pre_assoc, colimit.ι_pre, ι_colim_map_assoc,
          category.assoc]
        simpRw [←category.assoc]
        congr 1 
        ext 
        dsimp 
        simpa }

@[simp]
theorem plus_map_id (P : Cᵒᵖ ⥤ D) : J.plus_map (𝟙 P) = 𝟙 _ :=
  by 
    ext x : 2
    dsimp only [plus_map, plus_obj]
    rw [J.diagram_nat_trans_id, nat_trans.id_app]
    ext 
    dsimp 
    simp 

@[simp]
theorem plus_map_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) : J.plus_map (η ≫ γ) = J.plus_map η ≫ J.plus_map γ :=
  by 
    ext : 2
    dsimp only [plus_map]
    rw [J.diagram_nat_trans_comp]
    ext 
    dsimp 
    simp 

variable (D)

/-- The plus construction, a functor sending `P` to `J.plus_obj P`. -/
@[simps]
def plus_functor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  { obj := fun P => J.plus_obj P, map := fun P Q η => J.plus_map η, map_id' := fun _ => plus_map_id _ _,
    map_comp' := fun _ _ _ _ _ => plus_map_comp _ _ _ }

variable {D}

/-- The canonical map from `P` to `J.plus.obj P`.
See `to_plus` for a functorial version. -/
def to_plus : P ⟶ J.plus_obj P :=
  { app := fun X => cover.to_multiequalizer (⊤ : J.cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤),
    naturality' :=
      by 
        intro X Y f 
        dsimp [plus_obj]
        delta' cover.to_multiequalizer 
        simp only [diagram_pullback_app, colimit.ι_pre, ι_colim_map_assoc, category.assoc]
        dsimp only [functor.op, unop_op]
        let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
        rw [←colimit.w _ e.op, ←category.assoc, ←category.assoc, ←category.assoc]
        congr 1 
        ext 
        dsimp 
        simp only [multiequalizer.lift_ι, category.assoc]
        dsimp [cover.arrow.base]
        simp  }

@[simp, reassoc]
theorem to_plus_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.to_plus Q = J.to_plus _ ≫ J.plus_map η :=
  by 
    ext 
    dsimp [to_plus, plus_map]
    delta' cover.to_multiequalizer 
    simp only [ι_colim_map, category.assoc]
    simpRw [←category.assoc]
    congr 1 
    ext 
    dsimp 
    simp 

variable (D)

/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
def to_plus_nat_trans : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plus_functor D :=
  { app := fun P => J.to_plus P, naturality' := fun _ _ _ => to_plus_naturality _ _ }

variable {D}

/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
@[simp]
theorem plus_map_to_plus : J.plus_map (J.to_plus P) = J.to_plus (J.plus_obj P) :=
  by 
    ext X S 
    dsimp [to_plus, plus_obj, plus_map]
    delta' cover.to_multiequalizer 
    simp only [ι_colim_map]
    let e : S.unop ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
    simpRw [←colimit.w _ e.op, ←category.assoc]
    congr 1 
    ext I 
    dsimp 
    simp only [diagram_pullback_app, colimit.ι_pre, multiequalizer.lift_ι, ι_colim_map_assoc, category.assoc]
    dsimp only [functor.op]
    let ee : (J.pullback (I.map e).f).obj S.unop ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
    simpRw [←colimit.w _ ee.op, ←category.assoc]
    congr 1 
    ext II 
    dsimp 
    simp only [limit.lift_π, multifork.of_ι_π_app, multiequalizer.lift_ι, category.assoc]
    dsimp [multifork.of_ι]
    convert
      multiequalizer.condition (S.unop.index P)
        ⟨_, _, _, II.f, 𝟙 _, I.f, II.f ≫ I.f, I.hf, sieve.downward_closed _ I.hf _,
          by 
            simp ⟩
    ·
      cases I 
      rfl
    ·
      dsimp [cover.index]
      erw [P.map_id, category.comp_id]
      rfl

theorem is_iso_to_plus_of_is_sheaf (hP : presheaf.is_sheaf J P) : is_iso (J.to_plus P) :=
  by 
    rw [presheaf.is_sheaf_iff_multiequalizer] at hP 
    skip 
    suffices  : ∀ X, is_iso ((J.to_plus P).app X)
    ·
      skip 
      apply nat_iso.is_iso_of_is_iso_app 
    intro X 
    dsimp 
    suffices  : is_iso (colimit.ι (J.diagram P X.unop) (op ⊤))
    ·
      skip 
      apply is_iso.comp_is_iso 
    suffices  : ∀ S T : J.cover X.unopᵒᵖ f : S ⟶ T, is_iso ((J.diagram P X.unop).map f)
    ·
      skip 
      apply is_iso_ι_of_is_initial (initial_op_of_terminal is_terminal_top)
    intro S T e 
    have  : S.unop.to_multiequalizer P ≫ (J.diagram P X.unop).map e = T.unop.to_multiequalizer P
    ·
      ·
        ext 
        dsimp 
        simpa 
    have  : (J.diagram P X.unop).map e = inv (S.unop.to_multiequalizer P) ≫ T.unop.to_multiequalizer P
    ·
      simp [←this]
    rw [this]
    infer_instance

/-- The natural isomorphism between `P` and `P⁺` when `P` is a sheaf. -/
def iso_to_plus (hP : presheaf.is_sheaf J P) : P ≅ J.plus_obj P :=
  by 
    let this' := is_iso_to_plus_of_is_sheaf J P hP <;> exact as_iso (J.to_plus P)

@[simp]
theorem iso_to_plus_hom (hP : presheaf.is_sheaf J P) : (J.iso_to_plus P hP).Hom = J.to_plus P :=
  rfl

/-- Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf. -/
def plus_lift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) : J.plus_obj P ⟶ Q :=
  J.plus_map η ≫ (J.iso_to_plus Q hQ).inv

@[simp, reassoc]
theorem to_plus_plus_lift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) :
  J.to_plus P ≫ J.plus_lift η hQ = η :=
  by 
    dsimp [plus_lift]
    rw [←category.assoc]
    rw [iso.comp_inv_eq]
    dsimp only [iso_to_plus, as_iso]
    rw [to_plus_naturality]

theorem plus_lift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) (γ : J.plus_obj P ⟶ Q)
  (hγ : J.to_plus P ≫ γ = η) : γ = J.plus_lift η hQ :=
  by 
    dsimp only [plus_lift]
    rw [iso.eq_comp_inv, ←hγ, plus_map_comp]
    dsimp 
    simp 

theorem plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plus_obj P ⟶ Q) (hQ : presheaf.is_sheaf J Q)
  (h : J.to_plus P ≫ η = J.to_plus P ≫ γ) : η = γ :=
  by 
    have  : γ = J.plus_lift (J.to_plus P ≫ γ) hQ
    ·
      apply plus_lift_unique 
      rfl 
    rw [this]
    apply plus_lift_unique 
    exact h

@[simp]
theorem iso_to_plus_inv (hP : presheaf.is_sheaf J P) : (J.iso_to_plus P hP).inv = J.plus_lift (𝟙 _) hP :=
  by 
    apply J.plus_lift_unique 
    rw [iso.comp_inv_eq, category.id_comp]
    rfl

@[simp]
theorem plus_map_plus_lift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : presheaf.is_sheaf J R) :
  J.plus_map η ≫ J.plus_lift γ hR = J.plus_lift (η ≫ γ) hR :=
  by 
    apply J.plus_lift_unique 
    rw [←category.assoc, ←J.to_plus_naturality, category.assoc, J.to_plus_plus_lift]

end CategoryTheory.GrothendieckTopology

