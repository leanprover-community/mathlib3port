import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `punit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/


open Opposite

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type v} [small_category C]

/-- 
The colimit cocone over `coyoneda.obj X`, with cocone point `punit`.
-/
@[simps]
def colimit_cocone (X : Cᵒᵖ) : cocone (coyoneda.obj X) :=
  { x := PUnit,
    ι :=
      { app := by
          tidy } }

/-- 
The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimit_cocone_is_colimit (X : Cᵒᵖ) : is_colimit (colimit_cocone X) :=
  { desc := fun s x => s.ι.app (unop X) (𝟙 _),
    fac' := fun s Y => by
      ext f
      convert congr_funₓ (s.w f).symm (𝟙 (unop X))
      simp ,
    uniq' := fun s m w => by
      ext ⟨⟩
      rw [← w]
      simp }

instance (X : Cᵒᵖ) : has_colimit (coyoneda.obj X) :=
  has_colimit.mk { Cocone := _, IsColimit := colimit_cocone_is_colimit X }

/-- 
The colimit of `coyoneda.obj X` is isomorphic to `punit`.
-/
noncomputable def colimit_coyoneda_iso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit :=
  colimit.iso_colimit_cocone { Cocone := _, IsColimit := colimit_cocone_is_colimit X }

end Coyoneda

variable {C : Type u} [category.{v} C]

open Limits

-- failed to format: format: uncaught backtrack exception
/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
  instance
    yoneda_preserves_limits
    ( X : C ) : preserves_limits ( yoneda . obj X )
    where
      PreservesLimitsOfShape
        J 𝒥
        :=
        by
          exact
            {
              PreservesLimit
                :=
                fun
                  K
                    =>
                    {
                      preserves
                        :=
                        fun
                          c t
                            =>
                            {
                              lift
                                    :=
                                    fun
                                      s x
                                        =>
                                        Quiver.Hom.unop
                                          ( t.lift ⟨ op X , fun j => ( s.π.app j x ) . op , fun j₁ j₂ α => _ ⟩ )
                                  ,
                                fac' := fun s j => funext $ fun x => Quiver.Hom.op_inj ( t.fac _ _ ) ,
                                uniq'
                                  :=
                                  fun
                                    s m w
                                      =>
                                      funext
                                        $
                                        fun
                                          x
                                            =>
                                            by
                                              refine' Quiver.Hom.op_inj ( t.uniq ⟨ op X , _ , _ ⟩ _ fun j => _ )
                                                · dsimp simp [ ← s.w α ]
                                                · exact Quiver.Hom.unop_inj ( congr_funₓ ( w j ) x )
                              }
                      }
              }

-- failed to format: format: uncaught backtrack exception
/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
  instance
    coyoneda_preserves_limits
    ( X : C ᵒᵖ ) : preserves_limits ( coyoneda . obj X )
    where
      PreservesLimitsOfShape
        J 𝒥
        :=
        by
          exact
            {
              PreservesLimit
                :=
                fun
                  K
                    =>
                    {
                      preserves
                        :=
                        fun
                          c t
                            =>
                            {
                              lift
                                    :=
                                    fun
                                      s x
                                        =>
                                        t.lift
                                          ⟨ unop X , fun j => s.π.app j x , fun j₁ j₂ α => by dsimp simp [ ← s.w α ] ⟩
                                  ,
                                fac' := fun s j => funext $ fun x => t.fac _ _ ,
                                uniq'
                                  :=
                                  fun
                                    s m w
                                      =>
                                      funext
                                        $
                                        fun
                                          x => by refine' t.uniq ⟨ unop X , _ ⟩ _ fun j => _ exact congr_funₓ ( w j ) x
                              }
                      }
              }

/--  The yoneda embeddings jointly reflect limits. -/
def yoneda_jointly_reflects_limits (J : Type v) [small_category J] (K : J ⥤ Cᵒᵖ) (c : cone K)
    (t : ∀ X : C, is_limit ((yoneda.obj X).mapCone c)) : is_limit c :=
  let s' : ∀ s : cone K, cone (K ⋙ yoneda.obj s.X.unop) := fun s =>
    ⟨PUnit, fun j _ => (s.π.app j).unop, fun j₁ j₂ α => funext $ fun _ => Quiver.Hom.op_inj (s.w α).symm⟩
  { lift := fun s => ((t s.X.unop).lift (s' s) PUnit.unit).op,
    fac' := fun s j => Quiver.Hom.unop_inj (congr_funₓ ((t s.X.unop).fac (s' s) j) PUnit.unit),
    uniq' := fun s m w => by
      apply Quiver.Hom.unop_inj
      suffices (fun x : PUnit => m.unop) = (t s.X.unop).lift (s' s)by
        apply congr_funₓ this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      ext
      exact Quiver.Hom.op_inj (w j) }

/--  The coyoneda embeddings jointly reflect limits. -/
def coyoneda_jointly_reflects_limits (J : Type v) [small_category J] (K : J ⥤ C) (c : cone K)
    (t : ∀ X : Cᵒᵖ, is_limit ((coyoneda.obj X).mapCone c)) : is_limit c :=
  let s' : ∀ s : cone K, cone (K ⋙ coyoneda.obj (op s.X)) := fun s =>
    ⟨PUnit, fun j _ => s.π.app j, fun j₁ j₂ α => funext $ fun _ => (s.w α).symm⟩
  { lift := fun s => (t (op s.X)).lift (s' s) PUnit.unit, fac' := fun s j => congr_funₓ ((t _).fac (s' s) j) PUnit.unit,
    uniq' := fun s m w => by
      suffices (fun x : PUnit => m) = (t _).lift (s' s)by
        apply congr_funₓ this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      ext
      exact w j }

variable {D : Type u} [small_category D]

instance yoneda_functor_preserves_limits : preserves_limits (@yoneda D _) := by
  apply preserves_limits_of_evaluation
  intro K
  change preserves_limits (coyoneda.obj K)
  infer_instance

instance coyoneda_functor_preserves_limits : preserves_limits (@coyoneda D _) := by
  apply preserves_limits_of_evaluation
  intro K
  change preserves_limits (yoneda.obj K)
  infer_instance

instance yoneda_functor_reflects_limits : reflects_limits (@yoneda D _) :=
  limits.fully_faithful_reflects_limits _

instance coyoneda_functor_reflects_limits : reflects_limits (@coyoneda D _) :=
  limits.fully_faithful_reflects_limits _

end CategoryTheory

