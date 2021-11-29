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

noncomputable theory

variable [∀ P : «expr ᵒᵖ» C ⥤ D X : C S : J.cover X, has_multiequalizer (S.index P)]

variable (P : «expr ᵒᵖ» C ⥤ D)

/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
def diagram (X : C) : «expr ᵒᵖ» (J.cover X) ⥤ D :=
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

variable [∀ X : C, has_colimits_of_shape («expr ᵒᵖ» (J.cover X)) D]

/-- The plus construction, associating a presheaf to any presheaf.
See `plus` below for a functorial version.
-/
@[simps]
def plus_obj : «expr ᵒᵖ» C ⥤ D :=
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
@[simps]
def plus_map {P Q : «expr ᵒᵖ» C ⥤ D} (η : P ⟶ Q) : J.plus_obj P ⟶ J.plus_obj Q :=
  { app :=
      fun X =>
        colim_map
          { app :=
              fun S =>
                multiequalizer.lift _ _ (fun I => multiequalizer.ι (S.unop.index P) I ≫ η.app (op I.Y))
                  (by 
                    intro I 
                    erw [category.assoc, category.assoc, ←η.naturality, ←η.naturality, ←category.assoc, ←category.assoc,
                      multiequalizer.condition]
                    rfl),
            naturality' :=
              fun S T e =>
                by 
                  dsimp 
                  ext 
                  simpa },
    naturality' :=
      by 
        intro X Y f 
        dsimp 
        ext 
        simp only [diagram_pullback_app, ι_colim_map, colimit.ι_pre_assoc, colimit.ι_pre, ι_colim_map_assoc,
          category.assoc]
        simpRw [←category.assoc]
        congr 1 
        ext 
        dsimp 
        simpa }

variable (D)

/-- The plus construction, a functor sending `P` to `J.plus_obj P`. -/
@[simps]
def plus_functor : («expr ᵒᵖ» C ⥤ D) ⥤ «expr ᵒᵖ» C ⥤ D :=
  { obj := fun P => J.plus_obj P, map := fun P Q η => J.plus_map η,
    map_id' :=
      by 
        intro P 
        ext 
        dsimp 
        simp only [ι_colim_map, category.comp_id]
        convert category.id_comp _ 
        ext 
        simp only [multiequalizer.lift_ι, category.id_comp]
        exact category.comp_id _,
    map_comp' :=
      by 
        intro P Q R η γ 
        ext 
        dsimp 
        simp only [ι_colim_map, ι_colim_map_assoc]
        rw [←category.assoc]
        congr 1 
        ext 
        dsimp 
        simp  }

variable {D}

/-- The canonical map from `P` to `J.plus.obj P`.
See `to_plus` for a functorial version. -/
@[simps]
def to_plus : P ⟶ J.plus_obj P :=
  { app := fun X => cover.to_multiequalizer (⊤ : J.cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤),
    naturality' :=
      by 
        intro X Y f 
        dsimp 
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

variable (D)

/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
def to_plus_nat_trans : 𝟭 («expr ᵒᵖ» C ⥤ D) ⟶ J.plus_functor D :=
  { app := fun P => J.to_plus P,
    naturality' :=
      by 
        intro P Q η 
        ext 
        dsimp 
        delta' cover.to_multiequalizer 
        simp only [ι_colim_map, category.assoc]
        simpRw [←category.assoc]
        congr 1 
        ext 
        dsimp 
        simp  }

variable {D}

/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
@[simp]
theorem plus_map_to_plus : J.plus_map (J.to_plus P) = J.to_plus (J.plus_obj P) :=
  by 
    ext X S 
    dsimp 
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

-- error in CategoryTheory.Sites.Plus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_iso_to_plus_of_is_sheaf (hP : presheaf.is_sheaf J P) : is_iso (J.to_plus P) :=
begin
  rw [expr presheaf.is_sheaf_iff_multiequalizer] ["at", ident hP],
  resetI,
  suffices [] [":", expr ∀ X, is_iso ((J.to_plus P).app X)],
  { resetI,
    apply [expr nat_iso.is_iso_of_is_iso_app] },
  intros [ident X],
  dsimp [] [] [] [],
  suffices [] [":", expr is_iso (colimit.ι (J.diagram P X.unop) (op «expr⊤»()))],
  { resetI,
    apply [expr is_iso.comp_is_iso] },
  suffices [] [":", expr ∀
   (S T : «expr ᵒᵖ»(J.cover X.unop))
   (f : «expr ⟶ »(S, T)), is_iso ((J.diagram P X.unop).map f)],
  { resetI,
    apply [expr is_iso_ι_of_is_initial (initial_op_of_terminal is_terminal_top)] },
  intros [ident S, ident T, ident e],
  have [] [":", expr «expr = »(«expr ≫ »(S.unop.to_multiequalizer P, (J.diagram P X.unop).map e), T.unop.to_multiequalizer P)] [],
  by { ext [] [] [],
    dsimp [] [] [] [],
    simpa [] [] [] [] [] [] },
  have [] [":", expr «expr = »((J.diagram P X.unop).map e, «expr ≫ »(inv (S.unop.to_multiequalizer P), T.unop.to_multiequalizer P))] [],
  by simp [] [] [] ["[", "<-", expr this, "]"] [] [],
  rw [expr this] [],
  apply_instance
end

-- error in CategoryTheory.Sites.Plus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The natural isomorphism between `P` and `P⁺` when `P` is a sheaf. -/
def iso_to_plus (hP : presheaf.is_sheaf J P) : «expr ≅ »(P, J.plus_obj P) :=
by letI [] [] [":=", expr is_iso_to_plus_of_is_sheaf J P hP]; exact [expr as_iso (J.to_plus P)]

/-- Lift a morphism `P ⟶ Q` to `P⁺ ⟶ Q` when `Q` is a sheaf. -/
def plus_lift {P Q : «expr ᵒᵖ» C ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) : J.plus_obj P ⟶ Q :=
  J.plus_map η ≫ (J.iso_to_plus Q hQ).inv

theorem to_plus_plus_lift {P Q : «expr ᵒᵖ» C ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) :
  J.to_plus P ≫ J.plus_lift η hQ = η :=
  by 
    dsimp [plus_lift]
    rw [←category.assoc]
    rw [iso.comp_inv_eq]
    dsimp only [iso_to_plus, as_iso]
    change (J.to_plus_nat_trans D).app _ ≫ _ = _ 
    erw [(J.to_plus_nat_trans D).naturality]
    rfl

theorem plus_lift_unique {P Q : «expr ᵒᵖ» C ⥤ D} (η : P ⟶ Q) (hQ : presheaf.is_sheaf J Q) (γ : J.plus_obj P ⟶ Q)
  (hγ : J.to_plus P ≫ γ = η) : γ = J.plus_lift η hQ :=
  by 
    dsimp only [plus_lift]
    symm 
    change (J.plus_functor D).map η ≫ _ = _ 
    rw [iso.comp_inv_eq, ←hγ, (J.plus_functor D).map_comp]
    dsimp only [iso_to_plus, as_iso]
    change _ = (𝟭 _).map γ ≫ (J.to_plus_nat_trans D).app _ 
    erw [(J.to_plus_nat_trans D).naturality]
    congr 1
    dsimp only [plus_functor, to_plus_nat_trans]
    rw [J.plus_map_to_plus P]

-- error in CategoryTheory.Sites.Plus: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem plus_hom_ext
{P Q : «expr ⥤ »(«expr ᵒᵖ»(C), D)}
(η γ : «expr ⟶ »(J.plus_obj P, Q))
(hQ : presheaf.is_sheaf J Q)
(h : «expr = »(«expr ≫ »(J.to_plus P, η), «expr ≫ »(J.to_plus P, γ))) : «expr = »(η, γ) :=
begin
  have [] [":", expr «expr = »(γ, J.plus_lift «expr ≫ »(J.to_plus P, γ) hQ)] [],
  { apply [expr plus_lift_unique],
    refl },
  rw [expr this] [],
  apply [expr plus_lift_unique],
  exact [expr h]
end

end CategoryTheory.GrothendieckTopology

