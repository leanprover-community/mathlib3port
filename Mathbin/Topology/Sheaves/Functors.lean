import Mathbin.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# functors between categories of sheaves

Show that the pushforward of a sheaf is a sheaf, and define
the pushforward functor from the category of C-valued sheaves
on X to that of sheaves on Y, given a continuous map between
topological spaces X and Y.

TODO: pullback for presheaves and sheaves
-/


noncomputable theory

universe v u u₁

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

variable {C : Type u₁} [category.{v} C]

variable {X Y : Top.{v}} (f : X ⟶ Y)

variable ⦃ι : Type v⦄ {U : ι → opens Y}

namespace Top

namespace Presheaf.SheafConditionPairwiseIntersections

theorem map_diagram : pairwise.diagram U ⋙ opens.map f = pairwise.diagram ((opens.map f).obj ∘ U) :=
  by 
    apply functor.hext 
    abstract obj_eq 
      intro i 
      cases i <;> rfl 
    intro i j g 
    apply Subsingleton.helimₓ 
    iterate 2 
      rw [map_diagram.obj_eq]

theorem map_cocone : HEq ((opens.map f).mapCocone (pairwise.cocone U)) (pairwise.cocone ((opens.map f).obj ∘ U)) :=
  by 
    unfold functor.map_cocone cocones.functoriality 
    dsimp 
    congr 
    iterate 2 
      rw [map_diagram]
      rw [opens.map_supr]
    apply Subsingleton.helimₓ 
    rw [map_diagram, opens.map_supr]
    apply proof_irrel_heq

theorem pushforward_sheaf_of_sheaf {F : presheaf C X} (h : F.is_sheaf_pairwise_intersections) :
  (f _* F).IsSheafPairwiseIntersections :=
  fun ι U =>
    by 
      convert h ((opens.map f).obj ∘ U) using 2
      rw [←map_diagram]
      rfl 
      change HEq (F.map_cone ((opens.map f).mapCocone _).op) _ 
      congr 
      iterate 2 
        rw [map_diagram]
      apply map_cocone

end Presheaf.SheafConditionPairwiseIntersections

namespace Sheaf

open Presheaf

variable [has_products C]

/--
The pushforward of a sheaf (by a continuous map) is a sheaf.
-/
theorem pushforward_sheaf_of_sheaf {F : presheaf C X} (h : F.is_sheaf) : (f _* F).IsSheaf :=
  by 
    rw [is_sheaf_iff_is_sheaf_pairwise_intersections] at h⊢ <;>
      exact sheaf_condition_pairwise_intersections.pushforward_sheaf_of_sheaf f h

/--
The pushforward functor.
-/
def pushforward (f : X ⟶ Y) : X.sheaf C ⥤ Y.sheaf C :=
  { obj := fun ℱ => ⟨f _* ℱ.1, pushforward_sheaf_of_sheaf f ℱ.2⟩, map := fun _ _ => pushforward_map f }

end Sheaf

end Top

