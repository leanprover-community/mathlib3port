import Mathbin.CategoryTheory.Monad.Adjunction
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Limits and colimits in the category of algebras

This file shows that the forgetful functor `forget T : algebra T ⥤ C` for a monad `T : C ⥤ C`
creates limits and creates any colimits which `T` preserves.
This is used to show that `algebra T` has any limits which `C` has, and any colimits which `C` has
and `T` preserves.
This is generalised to the case of a monadic functor `D ⥤ C`.

## TODO

Dualise for the category of coalgebras and comonadic left adjoints.
-/


namespace CategoryTheory

open Category

open CategoryTheory.Limits

universe v u v₁ v₂ u₁ u₂

namespace Monadₓ

variable {C : Type u₁} [category.{v₁} C]

variable {T : Monadₓ C}

variable {J : Type u} [category.{v} J]

namespace ForgetCreatesLimits

variable (D : J ⥤ algebra T) (c : cone (D ⋙ T.forget)) (t : is_limit c)

/-- (Impl) The natural transformation used to define the new cone -/
@[simps]
def γ : D ⋙ T.forget ⋙ ↑T ⟶ D ⋙ T.forget where
  app := fun j => (D.obj j).a

/-- (Impl) This new cone is used to construct the algebra structure -/
@[simps π_app]
def new_cone : cone (D ⋙ forget T) where
  x := T.obj c.X
  π := (functor.const_comp _ _ ↑T).inv ≫ whisker_right c.π T ≫ γ D

/-- The algebra structure which will be the apex of the new limit cone for `D`. -/
@[simps]
def cone_point : algebra T where
  a := c.X
  a := t.lift (new_cone D c)
  unit' :=
    t.hom_ext fun j => by
      rw [category.assoc, t.fac, new_cone_π_app, ← T.η.naturality_assoc, functor.id_map, (D.obj j).Unit]
      dsimp
      simp
  assoc' :=
    t.hom_ext fun j => by
      rw [category.assoc, category.assoc, t.fac (new_cone D c), new_cone_π_app, ← functor.map_comp_assoc,
        t.fac (new_cone D c), new_cone_π_app, ← T.μ.naturality_assoc, (D.obj j).assoc, functor.map_comp, category.assoc]
      rfl

/-- (Impl) Construct the lifted cone in `algebra T` which will be limiting. -/
@[simps]
def lifted_cone : cone D where
  x := cone_point D c t
  π :=
    { app := fun j => { f := c.π.app j },
      naturality' := fun X Y f => by
        ext1
        dsimp
        erw [c.w f]
        simp }

/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
def lifted_cone_is_limit : is_limit (lifted_cone D c t) where
  lift := fun s =>
    { f := t.lift ((forget T).mapCone s),
      h' :=
        t.hom_ext fun j => by
          dsimp
          rw [category.assoc, category.assoc, t.fac, new_cone_π_app, ← functor.map_comp_assoc, t.fac,
            functor.map_cone_π_app]
          apply (s.π.app j).h }
  uniq' := fun s m J => by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCone s) j] using congr_argₓ algebra.hom.f (J j)

end ForgetCreatesLimits

/-- The forgetful functor from the Eilenberg-Moore category creates limits. -/
noncomputable instance forget_creates_limits : creates_limits_of_size (forget T) where
  CreatesLimitsOfShape := fun J 𝒥 =>
    { CreatesLimit := fun D =>
        creates_limit_of_reflects_iso fun c t =>
          { liftedCone := forget_creates_limits.lifted_cone D c t,
            validLift := cones.ext (iso.refl _) fun j => (id_comp _).symm,
            makesLimit := forget_creates_limits.lifted_cone_is_limit _ _ _ } }

/-- `D ⋙ forget T` has a limit, then `D` has a limit. -/
theorem has_limit_of_comp_forget_has_limit (D : J ⥤ algebra T) [has_limit (D ⋙ forget T)] : has_limit D :=
  has_limit_of_created D (forget T)

namespace ForgetCreatesColimits

variable {D : J ⥤ algebra T} (c : cocone (D ⋙ forget T)) (t : is_colimit c)

/-- (Impl)
The natural transformation given by the algebra structure maps, used to construct a cocone `c` with
apex `colimit (D ⋙ forget T)`.
 -/
@[simps]
def γ : (D ⋙ forget T) ⋙ ↑T ⟶ D ⋙ forget T where
  app := fun j => (D.obj j).a

/-- (Impl)
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
@[simps]
def new_cocone : cocone ((D ⋙ forget T) ⋙ ↑T) where
  x := c.X
  ι := γ ≫ c.ι

variable [preserves_colimit (D ⋙ forget T) (T : C ⥤ C)]

/-- (Impl)
Define the map `λ : TL ⟶ L`, which will serve as the structure of the coalgebra on `L`, and
we will show is the colimiting object. We use the cocone constructed by `c` and the fact that
`T` preserves colimits to produce this morphism.
-/
@[reducible]
def lambda : ((T : C ⥤ C).mapCocone c).x ⟶ c.X :=
  (is_colimit_of_preserves _ t).desc (new_cocone c)

/-- (Impl) The key property defining the map `λ : TL ⟶ L`. -/
theorem commuting (j : J) : (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j :=
  (is_colimit_of_preserves _ t).fac (new_cocone c) j

variable [preserves_colimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]

/-- (Impl)
Construct the colimiting algebra from the map `λ : TL ⟶ L` given by `lambda`. We are required to
show it satisfies the two algebra laws, which follow from the algebra laws for the image of `D` and
our `commuting` lemma.
-/
@[simps]
def cocone_point : algebra T where
  a := c.X
  a := lambda c t
  unit' := by
    apply t.hom_ext
    intro j
    rw [show c.ι.app j ≫ T.η.app c.X ≫ _ = T.η.app (D.obj j).a ≫ _ ≫ _ from T.η.naturality_assoc _ _, commuting,
      algebra.unit_assoc (D.obj j)]
    dsimp
    simp
  assoc' := by
    refine' (is_colimit_of_preserves _ (is_colimit_of_preserves _ t)).hom_ext fun j => _
    rw [functor.map_cocone_ι_app, functor.map_cocone_ι_app,
      show (T : C ⥤ C).map ((T : C ⥤ C).map _) ≫ _ ≫ _ = _ from T.μ.naturality_assoc _ _, ← functor.map_comp_assoc,
      commuting, functor.map_comp, category.assoc, commuting]
    apply (D.obj j).assoc_assoc _

/-- (Impl) Construct the lifted cocone in `algebra T` which will be colimiting. -/
@[simps]
def lifted_cocone : cocone D where
  x := cocone_point c t
  ι :=
    { app := fun j => { f := c.ι.app j, h' := commuting _ _ _ },
      naturality' := fun A B f => by
        ext1
        dsimp
        rw [comp_id]
        apply c.w }

/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
def lifted_cocone_is_colimit : is_colimit (lifted_cocone c t) where
  desc := fun s =>
    { f := t.desc ((forget T).mapCocone s),
      h' :=
        (is_colimit_of_preserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [← functor.map_comp_assoc, ← category.assoc, t.fac, commuting, category.assoc, t.fac]
          apply algebra.hom.h }
  uniq' := fun s m J => by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_argₓ algebra.hom.f (J j)

end ForgetCreatesColimits

open ForgetCreatesColimits

/-- The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
noncomputable instance forget_creates_colimit (D : J ⥤ algebra T) [preserves_colimit (D ⋙ forget T) (T : C ⥤ C)]
    [preserves_colimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : creates_colimit D (forget T) :=
  creates_colimit_of_reflects_iso fun c t =>
    { liftedCocone :=
        { x := cocone_point c t,
          ι :=
            { app := fun j => { f := c.ι.app j, h' := commuting _ _ _ },
              naturality' := fun A B f => by
                ext1
                dsimp
                erw [comp_id, c.w] } },
      validLift :=
        cocones.ext (iso.refl _)
          (by
            tidy),
      makesColimit := lifted_cocone_is_colimit _ _ }

noncomputable instance forget_creates_colimits_of_shape [preserves_colimits_of_shape J (T : C ⥤ C)] :
    creates_colimits_of_shape J (forget T) where
  CreatesColimit := fun K => by
    infer_instance

noncomputable instance forget_creates_colimits [preserves_colimits_of_size.{v, u} (T : C ⥤ C)] :
    creates_colimits_of_size.{v, u} (forget T) where
  CreatesColimitsOfShape := fun J 𝒥₁ => by
    infer_instance

/-- For `D : J ⥤ algebra T`, `D ⋙ forget T` has a colimit, then `D` has a colimit provided colimits
of shape `J` are preserved by `T`.
-/
theorem forget_creates_colimits_of_monad_preserves [preserves_colimits_of_shape J (T : C ⥤ C)] (D : J ⥤ algebra T)
    [has_colimit (D ⋙ forget T)] : has_colimit D :=
  has_colimit_of_created D (forget T)

end Monadₓ

variable {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

variable {J : Type u} [category.{v} J]

instance comp_comparison_forget_has_limit (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit (F ⋙ R)] :
    has_limit ((F ⋙ monad.comparison (adjunction.of_right_adjoint R)) ⋙ monad.forget _) :=
  @has_limit_of_iso _ _ _ _ (F ⋙ R) _ _
    (iso_whisker_left F (monad.comparison_forget (adjunction.of_right_adjoint R)).symm)

instance comp_comparison_has_limit (F : J ⥤ D) (R : D ⥤ C) [monadic_right_adjoint R] [has_limit (F ⋙ R)] :
    has_limit (F ⋙ monad.comparison (adjunction.of_right_adjoint R)) :=
  monad.has_limit_of_comp_forget_has_limit (F ⋙ monad.comparison (adjunction.of_right_adjoint R))

/-- Any monadic functor creates limits. -/
noncomputable def monadic_creates_limits (R : D ⥤ C) [monadic_right_adjoint R] : creates_limits_of_size.{v, u} R :=
  creates_limits_of_nat_iso (monad.comparison_forget (adjunction.of_right_adjoint R))

/-- The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
noncomputable def monadic_creates_colimit_of_preserves_colimit (R : D ⥤ C) (K : J ⥤ D) [monadic_right_adjoint R]
    [preserves_colimit (K ⋙ R) (left_adjoint R ⋙ R)]
    [preserves_colimit ((K ⋙ R) ⋙ left_adjoint R ⋙ R) (left_adjoint R ⋙ R)] : creates_colimit K R := by
  apply creates_colimit_of_nat_iso (monad.comparison_forget (adjunction.of_right_adjoint R))
  apply CategoryTheory.compCreatesColimit _ _
  infer_instance
  let i : (K ⋙ monad.comparison (adjunction.of_right_adjoint R)) ⋙ monad.forget _ ≅ K ⋙ R :=
    functor.associator _ _ _ ≪≫ iso_whisker_left K (monad.comparison_forget (adjunction.of_right_adjoint R))
  apply CategoryTheory.Monad.forgetCreatesColimit _
  · dsimp
    refine' preserves_colimit_of_iso_diagram _ i.symm
    
  · dsimp
    refine' preserves_colimit_of_iso_diagram _ (iso_whisker_right i (left_adjoint R ⋙ R)).symm
    

/-- A monadic functor creates any colimits of shapes it preserves. -/
noncomputable def monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape (R : D ⥤ C) [monadic_right_adjoint R]
    [preserves_colimits_of_shape J R] : creates_colimits_of_shape J R :=
  have : preserves_colimits_of_shape J (left_adjoint R ⋙ R) := by
    apply CategoryTheory.Limits.compPreservesColimitsOfShape _ _
    apply (adjunction.left_adjoint_preserves_colimits (adjunction.of_right_adjoint R)).1
    infer_instance
  ⟨fun K => monadic_creates_colimit_of_preserves_colimit _ _⟩

/-- A monadic functor creates colimits if it preserves colimits. -/
noncomputable def monadic_creates_colimits_of_preserves_colimits (R : D ⥤ C) [monadic_right_adjoint R]
    [preserves_colimits_of_size.{v, u} R] : creates_colimits_of_size.{v, u} R where
  CreatesColimitsOfShape := fun J 𝒥₁ => monadic_creates_colimits_of_shape_of_preserves_colimits_of_shape _

section

theorem has_limit_of_reflective (F : J ⥤ D) (R : D ⥤ C) [has_limit (F ⋙ R)] [reflective R] : has_limit F :=
  have := monadic_creates_limits.{v, u} R
  has_limit_of_created F R

/-- If `C` has limits of shape `J` then any reflective subcategory has limits of shape `J`. -/
theorem has_limits_of_shape_of_reflective [has_limits_of_shape J C] (R : D ⥤ C) [reflective R] :
    has_limits_of_shape J D :=
  { HasLimit := fun F => has_limit_of_reflective F R }

/-- If `C` has limits then any reflective subcategory has limits. -/
theorem has_limits_of_reflective (R : D ⥤ C) [has_limits_of_size.{v, u} C] [reflective R] :
    has_limits_of_size.{v, u} D :=
  { HasLimitsOfShape := fun J 𝒥₁ => has_limits_of_shape_of_reflective R }

/-- If `C` has colimits of shape `J` then any reflective subcategory has colimits of shape `J`. -/
theorem has_colimits_of_shape_of_reflective (R : D ⥤ C) [reflective R] [has_colimits_of_shape J C] :
    has_colimits_of_shape J D :=
  { HasColimit := fun F => by
      let c := (left_adjoint R).mapCocone (colimit.cocone (F ⋙ R))
      let h := (adjunction.of_right_adjoint R).leftAdjointPreservesColimits.1
      let this' := @h J _
      let t : is_colimit c := is_colimit_of_preserves (left_adjoint R) (colimit.is_colimit _)
      apply has_colimit.mk ⟨_, (is_colimit.precompose_inv_equiv _ _).symm t⟩
      apply (iso_whisker_left F (as_iso (adjunction.of_right_adjoint R).counit) : _) ≪≫ F.right_unitor }

/-- If `C` has colimits then any reflective subcategory has colimits. -/
theorem has_colimits_of_reflective (R : D ⥤ C) [reflective R] [has_colimits_of_size.{v, u} C] :
    has_colimits_of_size.{v, u} D :=
  { HasColimitsOfShape := fun J 𝒥 => has_colimits_of_shape_of_reflective R }

/-- The reflector always preserves terminal objects. Note this in general doesn't apply to any other
limit.
-/
noncomputable def left_adjoint_preserves_terminal_of_reflective (R : D ⥤ C) [reflective R] :
    preserves_limits_of_shape (discrete.{v} Pempty) (left_adjoint R) where
  PreservesLimit := fun K => by
    let F := functor.empty.{v} D
    apply preserves_limit_of_iso_diagram _ (functor.empty_ext (F ⋙ R) _)
    fconstructor
    intro c h
    have : has_limit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
    have : has_limit F := has_limit_of_reflective F R
    apply is_limit_change_empty_cone D (limit.is_limit F)
    apply (as_iso ((adjunction.of_right_adjoint R).counit.app _)).symm.trans
    · apply (left_adjoint R).mapIso
      let this' := monadic_creates_limits.{v, v} R
      let this := (CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit F R).preserves
      apply (this (limit.is_limit F)).conePointUniqueUpToIso h
      
    infer_instance

end

end CategoryTheory

