/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.monad.monadicity
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Reflexive
import Mathbin.CategoryTheory.Monad.Coequalizer
import Mathbin.CategoryTheory.Monad.Limits

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a right adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers`
* `G` creates `G`-split coequalizers, see
  `category_theory.monad.monadic_of_creates_G_split_coequalizers`
  (The converse of this is also shown, see
   `category_theory.monad.creates_G_split_coequalizers_of_monadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms`

## Tags

Beck, monadicity, descent

## TODO

Dualise to show comonadicity theorems.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace MonadicityInternal

section

-- We use these parameters and notations to simplify the statements of internal constructions
-- here.
parameter {C : Type u₁}{D : Type u₂}

parameter [Category.{v₁} C][Category.{v₁} D]

parameter {G : D ⥤ C}[IsRightAdjoint G]

-- mathport name: exprF
-- An unfortunate consequence of the local notation is that it is only recognised if there is an
-- extra space after the reference.
local notation "F" => leftAdjoint G

-- mathport name: expradj
local notation "adj" => Adjunction.ofRightAdjoint G

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_reflexive (A : adj.toMonad.Algebra) :
    IsReflexivePair (F.map A.a) (adj.counit.app (F.obj A.a)) :=
  by
  apply IsReflexivePair.mk' (F.map (adj.unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    exact congr_arg (fun _ => F.map _) A.unit
  · rw [adj.left_triangle_components]
    rfl
#align category_theory.monad.monadicity_internal.main_pair_reflexive CategoryTheory.Monad.MonadicityInternal.main_pair_reflexive

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_G_split (A : adj.toMonad.Algebra) :
    G.IsSplitPair (F.map A.a) (adj.counit.app (F.obj A.a))
    where splittable := ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩
#align category_theory.monad.monadicity_internal.main_pair_G_split CategoryTheory.Monad.MonadicityInternal.main_pair_G_split

/-- The object function for the left adjoint to the comparison functor. -/
def comparisonLeftAdjointObj (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)
#align category_theory.monad.monadicity_internal.comparison_left_adjoint_obj CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointObj

/--
We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
@[simps]
def comparisonLeftAdjointHomEquiv (A : adj.toMonad.Algebra) (B : D)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    (comparison_left_adjoint_obj A ⟶ B) ≃ (A ⟶ (comparison adj).obj B) :=
  calc
    (comparison_left_adjoint_obj A ⟶ B) ≃ { f : F.obj A.a ⟶ B // _ } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.a ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } :=
      by
      refine' (adj.homEquiv _ _).subtypeEquiv _
      intro f
      rw [← (adj.homEquiv _ _).injective.eq_iff, Adjunction.homEquiv_naturality_left,
        adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp]
      dsimp
      rw [adj.right_triangle_components_assoc, ← G.map_comp, F.map_comp, Category.assoc,
        adj.counit_naturality, adj.left_triangle_components_assoc]
      apply eq_comm
    _ ≃ (A ⟶ (comparison adj).obj B) :=
      { toFun := fun g =>
          { f := _
            h' := g.prop }
        invFun := fun f => ⟨f.f, f.h⟩
        left_inv := fun g => by ext; rfl
        right_inv := fun f => by ext; rfl }
    
#align category_theory.monad.monadicity_internal.comparison_left_adjoint_hom_equiv CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointHomEquiv

/-- Construct the adjunction to the comparison functor.
-/
def leftAdjointComparison
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    adj.toMonad.Algebra ⥤ D :=
  by
  refine'
    @adjunction.left_adjoint_of_equiv _ _ _ _ (comparison adj) (fun A => comparisonLeftAdjointObj A)
      (fun A B => _) _
  · apply comparisonLeftAdjointHomEquiv
  · intro A B B' g h
    ext1
    dsimp [comparisonLeftAdjointHomEquiv]
    rw [← adj.homEquiv_naturality_right, Category.assoc]
#align category_theory.monad.monadicity_internal.left_adjoint_comparison CategoryTheory.Monad.MonadicityInternal.leftAdjointComparison

/-- Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
-/
@[simps counit]
def comparisonAdjunction
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    left_adjoint_comparison ⊣ comparison adj :=
  Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.monad.monadicity_internal.comparison_adjunction CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction

theorem comparisonAdjunction_unit_f_aux
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))]
    (A : adj.toMonad.Algebra) :
    (comparison_adjunction.unit.app A).f =
      adj.homEquiv A.a _ (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.a))) :=
  congr_arg (adj.homEquiv _ _) (Category.comp_id _)
#align category_theory.monad.monadicity_internal.comparison_adjunction_unit_f_aux CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f_aux

/-- This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
@[simps x]
def unitCofork (A : adj.toMonad.Algebra) [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    Cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj A.a))) :=
  Cofork.ofπ (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.a))))
    (by
      change _ = G.map _ ≫ _
      rw [← G.map_comp, coequalizer.condition, G.map_comp])
#align category_theory.monad.monadicity_internal.unit_cofork CategoryTheory.Monad.MonadicityInternal.unitCofork

@[simp]
theorem unitCofork_π (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] :
    (unit_cofork A).π = G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.a))) :=
  rfl
#align category_theory.monad.monadicity_internal.unit_cofork_π CategoryTheory.Monad.MonadicityInternal.unitCofork_π

theorem comparisonAdjunction_unit_f
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))]
    (A : adj.toMonad.Algebra) :
    (comparison_adjunction.unit.app A).f = (beckCoequalizer A).desc (unit_cofork A) :=
  by
  apply Limits.Cofork.IsColimit.hom_ext (beckCoequalizer A)
  rw [Cofork.IsColimit.π_desc]
  dsimp only [beckCofork_π, unitCofork_π]
  rw [comparisonAdjunction_unit_f_aux, ← adj.homEquiv_naturality_left A.a, coequalizer.condition,
    adj.homEquiv_naturality_right, adj.homEquiv_unit, Category.assoc]
  apply adj.right_triangle_components_assoc
#align category_theory.monad.monadicity_internal.comparison_adjunction_unit_f CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f

/-- The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
@[simps]
def counitCofork (B : D) :
    Cofork (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B))) :=
  Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)
#align category_theory.monad.monadicity_internal.counit_cofork CategoryTheory.Monad.MonadicityInternal.counitCofork

/-- The unit cofork is a colimit provided `G` preserves it.  -/
def unitColimitOfPreservesCoequalizer (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))]
    [PreservesColimit (parallelPair (F.map A.a) (adj.counit.app (F.obj A.a))) G] :
    IsColimit (unit_cofork A) :=
  isColimitOfHasCoequalizerOfPreservesColimit G _ _
#align category_theory.monad.monadicity_internal.unit_colimit_of_preserves_coequalizer CategoryTheory.Monad.MonadicityInternal.unitColimitOfPreservesCoequalizer

/-- The counit cofork is a colimit provided `G` reflects it. -/
def counitCoequalizerOfReflectsCoequalizer (B : D)
    [ReflectsColimit
        (parallelPair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B)))) G] :
    IsColimit (counit_cofork B) :=
  isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))
#align category_theory.monad.monadicity_internal.counit_coequalizer_of_reflects_coequalizer CategoryTheory.Monad.MonadicityInternal.counitCoequalizerOfReflectsCoequalizer

theorem comparisonAdjunction_counit_app
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.a))] (B : D) :
    comparison_adjunction.counit.app B = colimit.desc _ (counit_cofork B) :=
  by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ =
      coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp
#align category_theory.monad.monadicity_internal.comparison_adjunction_counit_app CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_counit_app

end

end MonadicityInternal

open CategoryTheory.Adjunction

open MonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable (G : D ⥤ C)

/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadic_of_creates_G_split_coequalizers`.
-/
def createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
    [G.IsSplitPair f g] : CreatesColimit (parallelPair f g) G :=
  by
  apply monadicCreatesColimitOfPreservesColimit _ _
  infer_instance
  · apply preservesColimitOfIsoDiagram _ (diagramIsoParallelPair.{v₁} _).symm
    dsimp
    infer_instance
  · apply preservesColimitOfIsoDiagram _ (diagramIsoParallelPair.{v₁} _).symm
    dsimp
    infer_instance
#align category_theory.monad.creates_G_split_coequalizers_of_monadic CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic

variable [IsRightAdjoint G]

section BeckMonadicity

/-- To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `C` has them.
-/
def monadicOfHasPreservesReflectsGSplitCoequalizers
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G] :
    MonadicRightAdjoint G :=
  by
  let L : (Adjunction.ofRightAdjoint G).toMonad.Algebra ⥤ D := leftAdjointComparison
  letI i : IsRightAdjoint (comparison (ofRightAdjoint G)) := ⟨_, comparisonAdjunction⟩
  constructor
  let this :
    ∀ X : (ofRightAdjoint G).toMonad.Algebra,
      IsIso ((ofRightAdjoint (comparison (ofRightAdjoint G))).unit.app X) :=
    by
    intro X
    apply isIso_of_reflects_iso _ (Monad.forget (ofRightAdjoint G).toMonad)
    · change IsIso (comparison_adjunction.unit.app X).f
      rw [comparisonAdjunction_unit_f]
      change
        IsIso
          (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
              (unitColimitOfPreservesCoequalizer X)).hom
      refine' IsIso.of_iso (IsColimit.coconePointUniqueUpToIso _ _)
  let this : ∀ Y : D, IsIso ((ofRightAdjoint (comparison (ofRightAdjoint G))).counit.app Y) :=
    by
    intro Y
    change IsIso (comparison_adjunction.counit.app Y)
    rw [comparisonAdjunction_counit_app]
    change IsIso (IsColimit.coconePointUniqueUpToIso _ _).hom
    infer_instance
    apply counitCoequalizerOfReflectsCoequalizer _
    letI :
      G.is_split_pair ((leftAdjoint G).map (G.map ((Adjunction.ofRightAdjoint G).counit.app Y)))
        ((Adjunction.ofRightAdjoint G).counit.app ((leftAdjoint G).obj (G.obj Y))) :=
      MonadicityInternal.main_pair_G_split ((comparison (Adjunction.ofRightAdjoint G)).obj Y)
    infer_instance
  exact Adjunction.isRightAdjointToIsEquivalence
#align category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers

/--
Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
This is the converse of `creates_G_split_of_monadic`.
-/
def monadicOfCreatesGSplitCoequalizers
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G] :
    MonadicRightAdjoint G :=
  by
  let this : ∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], HasColimit (parallelPair f g ⋙ G) :=
    by
    intro A B f g i
    apply hasColimitOfIso (diagramIsoParallelPair.{v₁} _)
    change HasCoequalizer (G.map f) (G.map g)
    infer_instance
  apply monadicOfHasPreservesReflectsGSplitCoequalizers _
  · infer_instance
  · intro A B f g i
    apply hasColimitOfCreated (parallelPair f g) G
  · intro A B f g i
    infer_instance
  · intro A B f g i
    infer_instance
#align category_theory.monad.monadic_of_creates_G_split_coequalizers CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers

/-- An alternate version of Beck's monadicity theorem. If `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
def monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [ReflectsIsomorphisms G]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G] :
    MonadicRightAdjoint G :=
  by
  apply monadicOfHasPreservesReflectsGSplitCoequalizers _
  · infer_instance
  · assumption
  · assumption
  · intro A B f g i
    apply reflectsColimitOfReflectsIsomorphisms
#align category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms

end BeckMonadicity

section ReflexiveMonadicity

variable [HasReflexiveCoequalizers D] [ReflectsIsomorphisms G]

variable [∀ ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G]

/-- Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : MonadicRightAdjoint G :=
  by
  let L : (Adjunction.ofRightAdjoint G).toMonad.Algebra ⥤ D := leftAdjointComparison
  letI i : IsRightAdjoint (comparison (Adjunction.ofRightAdjoint G)) := ⟨_, comparisonAdjunction⟩
  constructor
  let this :
    ∀ X : (Adjunction.ofRightAdjoint G).toMonad.Algebra,
      IsIso ((Adjunction.ofRightAdjoint (comparison (Adjunction.ofRightAdjoint G))).unit.app X) :=
    by
    intro X
    apply isIso_of_reflects_iso _ (Monad.forget (Adjunction.ofRightAdjoint G).toMonad)
    · change IsIso (comparison_adjunction.unit.app X).f
      rw [comparisonAdjunction_unit_f]
      change
        IsIso
          (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
              (unitColimitOfPreservesCoequalizer X)).hom
      apply IsIso.of_iso (IsColimit.coconePointUniqueUpToIso _ _)
  let this :
    ∀ Y : D, IsIso ((ofRightAdjoint (comparison (Adjunction.ofRightAdjoint G))).counit.app Y) :=
    by
    intro Y
    change IsIso (comparison_adjunction.counit.app Y)
    rw [comparisonAdjunction_counit_app]
    change IsIso (IsColimit.coconePointUniqueUpToIso _ _).hom
    infer_instance
    apply counitCoequalizerOfReflectsCoequalizer _
    apply reflectsColimitOfReflectsIsomorphisms
  exact Adjunction.isRightAdjointToIsEquivalence
#align category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms

end ReflexiveMonadicity

end Monad

end CategoryTheory

