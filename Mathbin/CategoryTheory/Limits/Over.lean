import Mathbin.CategoryTheory.Over 
import Mathbin.CategoryTheory.Adjunction.Opposites 
import Mathbin.CategoryTheory.Limits.Preserves.Basic 
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks 
import Mathbin.CategoryTheory.Limits.Creates 
import Mathbin.CategoryTheory.Limits.Comma

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : over X ⥤ C` creates colimits, and hence `over X` has
any colimits that `C` has (as well as the dual that `forget X : under X ⟶ C` creates limits).

Note that the folder `category_theory.limits.shapes.constructions.over` further shows that
`forget X : over X ⥤ C` creates connected limits (so `over X` has connected limits), and that
`over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.

TODO: If `C` has binary products, then `forget X : over X ⥤ C` has a right adjoint.
-/


noncomputable theory

universe v u

open CategoryTheory CategoryTheory.Limits

variable {J : Type v} [small_category J]

variable {C : Type u} [category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

instance has_colimit_of_has_colimit_comp_forget (F : J ⥤ over X) [i : has_colimit (F ⋙ forget X)] : has_colimit F :=
  @costructured_arrow.has_colimit _ _ _ _ i _

instance [has_colimits_of_shape J C] : has_colimits_of_shape J (over X) :=
  {  }

instance [has_colimits C] : has_colimits (over X) :=
  ⟨inferInstance⟩

instance creates_colimits : creates_colimits (forget X) :=
  costructured_arrow.creates_colimits

example [has_colimits C] : preserves_colimits (forget X) :=
  inferInstance

example : reflects_colimits (forget X) :=
  inferInstance

section 

variable [has_pullbacks C]

open Tactic

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `over Y ⥤ over X`,
by pulling back a morphism along `f`. -/
@[simps]
def pullback {X Y : C} (f : X ⟶ Y) : over Y ⥤ over X :=
  { obj := fun g => over.mk (pullback.snd : pullback g.hom f ⟶ X),
    map :=
      fun g h k =>
        over.hom_mk
          (pullback.lift (pullback.fst ≫ k.left) pullback.snd
            (by 
              simp [pullback.condition]))
          (by 
            tidy) }

/-- `over.map f` is left adjoint to `over.pullback f`. -/
def map_pullback_adj {A B : C} (f : A ⟶ B) : over.map f ⊣ pullback f :=
  adjunction.mk_of_hom_equiv
    { homEquiv :=
        fun g h =>
          { toFun := fun X => over.hom_mk (pullback.lift X.left g.hom (over.w X)) (pullback.lift_snd _ _ _),
            invFun :=
              fun Y =>
                by 
                  refine' over.hom_mk _ _ 
                  refine' Y.left ≫ pullback.fst 
                  dsimp 
                  rw [←over.w Y, category.assoc, pullback.condition, category.assoc]
                  rfl,
            left_inv :=
              fun X =>
                by 
                  ext 
                  dsimp 
                  simp ,
            right_inv :=
              fun Y =>
                by 
                  ext 
                  dsimp 
                  simp only [pullback.lift_fst]
                  dsimp 
                  rw [pullback.lift_snd, ←over.w Y]
                  rfl } }

/-- pullback (𝟙 A) : over A ⥤ over A is the identity functor. -/
def pullback_id {A : C} : pullback (𝟙 A) ≅ 𝟭 _ :=
  Adjunction.rightAdjointUniq (map_pullback_adj _) (adjunction.id.ofNatIsoLeft over.map_id.symm)

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullback_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  Adjunction.rightAdjointUniq (map_pullback_adj _)
    (((map_pullback_adj _).comp _ _ (map_pullback_adj _)).ofNatIsoLeft (over.map_comp _ _).symm)

instance pullback_is_right_adjoint {A B : C} (f : A ⟶ B) : is_right_adjoint (pullback f) :=
  ⟨_, map_pullback_adj f⟩

end 

end CategoryTheory.Over

namespace CategoryTheory.Under

instance has_limit_of_has_limit_comp_forget (F : J ⥤ under X) [i : has_limit (F ⋙ forget X)] : has_limit F :=
  @structured_arrow.has_limit _ _ _ _ i _

instance [has_limits_of_shape J C] : has_limits_of_shape J (under X) :=
  {  }

instance [has_limits C] : has_limits (under X) :=
  ⟨inferInstance⟩

instance creates_limits : creates_limits (forget X) :=
  structured_arrow.creates_limits

example [has_limits C] : preserves_limits (forget X) :=
  inferInstance

example : reflects_limits (forget X) :=
  inferInstance

section 

variable [has_pushouts C]

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `under X ⥤ under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) : under X ⥤ under Y :=
  { obj := fun g => under.mk (pushout.inr : Y ⟶ pushout g.hom f),
    map :=
      fun g h k =>
        under.hom_mk
          (pushout.desc (k.right ≫ pushout.inl) pushout.inr
            (by 
              simp [←pushout.condition]))
          (by 
            tidy) }

end 

end CategoryTheory.Under

