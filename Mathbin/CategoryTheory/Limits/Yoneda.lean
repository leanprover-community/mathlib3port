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

variable{C : Type v}[small_category C]

/--
The colimit cocone over `coyoneda.obj X`, with cocone point `punit`.
-/
@[simps]
def colimit_cocone (X : «expr ᵒᵖ» C) : cocone (coyoneda.obj X) :=
  { x := PUnit,
    ι :=
      { app :=
          by 
            tidy } }

/--
The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimit_cocone_is_colimit (X : «expr ᵒᵖ» C) : is_colimit (colimit_cocone X) :=
  { desc := fun s x => s.ι.app (unop X) (𝟙 _),
    fac' :=
      fun s Y =>
        by 
          ext f 
          convert congr_funₓ (s.w f).symm (𝟙 (unop X))
          simp ,
    uniq' :=
      fun s m w =>
        by 
          ext ⟨⟩
          rw [←w]
          simp  }

instance  (X : «expr ᵒᵖ» C) : has_colimit (coyoneda.obj X) :=
  has_colimit.mk { Cocone := _, IsColimit := colimit_cocone_is_colimit X }

/--
The colimit of `coyoneda.obj X` is isomorphic to `punit`.
-/
noncomputable def colimit_coyoneda_iso (X : «expr ᵒᵖ» C) : colimit (coyoneda.obj X) ≅ PUnit :=
  colimit.iso_colimit_cocone { Cocone := _, IsColimit := colimit_cocone_is_colimit X }

end Coyoneda

variable{C : Type u}[category.{v} C]

open Limits

/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
instance yoneda_preserves_limits (X : C) : preserves_limits (yoneda.obj X) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun K =>
                  { preserves :=
                      fun c t =>
                        { lift :=
                            fun s x => Quiver.Hom.unop (t.lift ⟨op X, fun j => (s.π.app j x).op, fun j₁ j₂ α => _⟩),
                          fac' := fun s j => funext$ fun x => Quiver.Hom.op_inj (t.fac _ _),
                          uniq' :=
                            fun s m w =>
                              funext$
                                fun x =>
                                  by 
                                    refine' Quiver.Hom.op_inj (t.uniq ⟨op X, _, _⟩ _ fun j => _)
                                    ·
                                      dsimp 
                                      simp [←s.w α]
                                    ·
                                      exact Quiver.Hom.unop_inj (congr_funₓ (w j) x) } } } }

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
instance coyoneda_preserves_limits (X : «expr ᵒᵖ» C) : preserves_limits (coyoneda.obj X) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { PreservesLimit :=
                fun K =>
                  { preserves :=
                      fun c t =>
                        { lift :=
                            fun s x =>
                              t.lift
                                ⟨unop X, fun j => s.π.app j x,
                                  fun j₁ j₂ α =>
                                    by 
                                      dsimp 
                                      simp [←s.w α]⟩,
                          fac' := fun s j => funext$ fun x => t.fac _ _,
                          uniq' :=
                            fun s m w =>
                              funext$
                                fun x =>
                                  by 
                                    refine' t.uniq ⟨unop X, _⟩ _ fun j => _ 
                                    exact congr_funₓ (w j) x } } } }

-- error in CategoryTheory.Limits.Yoneda: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The yoneda embeddings jointly reflect limits. -/
def yoneda_jointly_reflects_limits
(J : Type v)
[small_category J]
(K : «expr ⥤ »(J, «expr ᵒᵖ»(C)))
(c : cone K)
(t : ∀ X : C, is_limit ((yoneda.obj X).map_cone c)) : is_limit c :=
let s' : ∀
    s : cone K, cone «expr ⋙ »(K, yoneda.obj s.X.unop) := λ
    s, ⟨punit, λ j _, (s.π.app j).unop, λ j₁ j₂ α, «expr $ »(funext, λ _, quiver.hom.op_inj (s.w α).symm)⟩ in
{ lift := λ s, ((t s.X.unop).lift (s' s) punit.star).op,
  fac' := λ s j, quiver.hom.unop_inj (congr_fun ((t s.X.unop).fac (s' s) j) punit.star),
  uniq' := λ s m w, begin
    apply [expr quiver.hom.unop_inj],
    suffices [] [":", expr «expr = »(λ x : punit, m.unop, (t s.X.unop).lift (s' s))],
    { apply [expr congr_fun this punit.star] },
    apply [expr (t _).uniq (s' s) _ (λ j, _)],
    ext [] [] [],
    exact [expr quiver.hom.op_inj (w j)]
  end }

-- error in CategoryTheory.Limits.Yoneda: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The coyoneda embeddings jointly reflect limits. -/
def coyoneda_jointly_reflects_limits
(J : Type v)
[small_category J]
(K : «expr ⥤ »(J, C))
(c : cone K)
(t : ∀ X : «expr ᵒᵖ»(C), is_limit ((coyoneda.obj X).map_cone c)) : is_limit c :=
let s' : ∀
    s : cone K, cone «expr ⋙ »(K, coyoneda.obj (op s.X)) := λ
    s, ⟨punit, λ j _, s.π.app j, λ j₁ j₂ α, «expr $ »(funext, λ _, (s.w α).symm)⟩ in
{ lift := λ s, (t (op s.X)).lift (s' s) punit.star,
  fac' := λ s j, congr_fun ((t _).fac (s' s) j) punit.star,
  uniq' := λ s m w, begin
    suffices [] [":", expr «expr = »(λ x : punit, m, (t _).lift (s' s))],
    { apply [expr congr_fun this punit.star] },
    apply [expr (t _).uniq (s' s) _ (λ j, _)],
    ext [] [] [],
    exact [expr w j]
  end }

variable{D : Type u}[small_category D]

instance yoneda_functor_preserves_limits : preserves_limits (@yoneda D _) :=
  by 
    apply preserves_limits_of_evaluation 
    intro K 
    change preserves_limits (coyoneda.obj K)
    infer_instance

instance coyoneda_functor_preserves_limits : preserves_limits (@coyoneda D _) :=
  by 
    apply preserves_limits_of_evaluation 
    intro K 
    change preserves_limits (yoneda.obj K)
    infer_instance

instance yoneda_functor_reflects_limits : reflects_limits (@yoneda D _) :=
  limits.fully_faithful_reflects_limits _

instance coyoneda_functor_reflects_limits : reflects_limits (@coyoneda D _) :=
  limits.fully_faithful_reflects_limits _

end CategoryTheory

