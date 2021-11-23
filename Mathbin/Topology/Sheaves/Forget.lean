import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products 
import Mathbin.Topology.Sheaves.Sheaf

/-!
# Checking the sheaf condition on the underlying presheaf of types.

If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices
to check it on the underlying sheaf of types.

## References
* https://stacks.math.columbia.edu/tag/0073
-/


noncomputable theory

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

namespace Top

namespace Presheaf

namespace SheafCondition

open SheafConditionEqualizerProducts

universe v u₁ u₂

variable{C : Type u₁}[category.{v} C][has_limits C]

variable{D : Type u₂}[category.{v} D][has_limits D]

variable(G : C ⥤ D)[preserves_limits G]

variable{X : Top.{v}}(F : presheaf C X)

variable{ι : Type v}(U : ι → opens X)

attribute [local reducible] diagram left_res right_res

/--
When `G` preserves limits, the sheaf condition diagram for `F` composed with `G` is
naturally isomorphic to the sheaf condition diagram for `F ⋙ G`.
-/
def diagram_comp_preserves_limits : diagram F U ⋙ G ≅ diagram (F ⋙ G) U :=
  by 
    fapply nat_iso.of_components 
    rintro ⟨j⟩
    exact preserves_product.iso _ _ 
    exact preserves_product.iso _ _ 
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    ·
      ext 
      simp 
      dsimp 
      simp 
    ·
      ext 
      simp only [limit.lift_π, functor.comp_map, map_lift_pi_comparison, fan.mk_π_app, preserves_product.iso_hom,
        parallel_pair_map_left, functor.map_comp, category.assoc]
      dsimp 
      simp 
    ·
      ext 
      simp only [limit.lift_π, functor.comp_map, parallel_pair_map_right, fan.mk_π_app, preserves_product.iso_hom,
        map_lift_pi_comparison, functor.map_comp, category.assoc]
      dsimp 
      simp 
    ·
      ext 
      simp 
      dsimp 
      simp 

attribute [local reducible] res

/--
When `G` preserves limits, the image under `G` of the sheaf condition fork for `F`
is the sheaf condition fork for `F ⋙ G`,
postcomposed with the inverse of the natural isomorphism `diagram_comp_preserves_limits`.
-/
def map_cone_fork :
  G.map_cone (fork F U) ≅ (cones.postcompose (diagram_comp_preserves_limits G F U).inv).obj (fork (F ⋙ G) U) :=
  cones.ext (iso.refl _)
    fun j =>
      by 
        dsimp 
        simp [diagram_comp_preserves_limits]
        cases j <;> dsimp
        ·
          rw [iso.eq_comp_inv]
          ext 
          simp 
          dsimp 
          simp 
        ·
          rw [iso.eq_comp_inv]
          ext 
          simp 
          dsimp 
          simp only [limit.lift_π, fan.mk_π_app, ←G.map_comp, limit.lift_π_assoc, fan.mk_π_app]

end SheafCondition

universe v u₁ u₂

open SheafCondition SheafConditionEqualizerProducts

variable{C : Type u₁}[category.{v} C]{D : Type u₂}[category.{v} D]

variable(G : C ⥤ D)

variable[reflects_isomorphisms G]

variable[has_limits C][has_limits D][preserves_limits G]

variable{X : Top.{v}}(F : presheaf C X)

-- error in Topology.Sheaves.Forget: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices to check it on the underlying sheaf of types.

Another useful example is the forgetful functor `TopCommRing ⥤ Top`.

See https://stacks.math.columbia.edu/tag/0073.
In fact we prove a stronger version with arbitrary complete target category.
-/ theorem is_sheaf_iff_is_sheaf_comp : «expr ↔ »(presheaf.is_sheaf F, presheaf.is_sheaf «expr ⋙ »(F, G)) :=
begin
  split,
  { intros [ident S, ident ι, ident U],
    obtain ["⟨", ident t₁, "⟩", ":=", expr S U],
    have [ident t₂] [] [":=", expr @preserves_limit.preserves _ _ _ _ _ _ _ G _ _ t₁],
    have [ident t₃] [] [":=", expr is_limit.of_iso_limit t₂ (map_cone_fork G F U)],
    have [ident t₄] [] [":=", expr is_limit.postcompose_inv_equiv _ _ t₃],
    exact [expr ⟨t₄⟩] },
  { intros [ident S, ident ι, ident U],
    refine [expr ⟨_⟩],
    let [ident f] [] [":=", expr equalizer.lift _ (w F U)],
    suffices [] [":", expr is_iso (G.map f)],
    { resetI,
      haveI [] [":", expr is_iso f] [":=", expr is_iso_of_reflects_iso f G],
      apply [expr is_limit.of_iso_limit (limit.is_limit _)],
      apply [expr iso.symm],
      fapply [expr cones.ext],
      exact [expr as_iso f],
      rintro ["⟨", "_", "|", "_", "⟩"]; { dsimp [] ["[", expr f, "]"] [] [],
        simp [] [] [] [] [] [] } },
    { let [ident c] [] [":=", expr fork «expr ⋙ »(F, G) U],
      obtain ["⟨", ident hc, "⟩", ":=", expr S U],
      let [ident d] [] [":=", expr G.map_cone (equalizer.fork (left_res F U) (right_res F U))],
      have [ident hd] [":", expr is_limit d] [":=", expr preserves_limit.preserves (limit.is_limit _)],
      let [ident d'] [] [":=", expr (cones.postcompose (diagram_comp_preserves_limits G F U).hom).obj d],
      have [ident hd'] [":", expr is_limit d'] [":=", expr (is_limit.postcompose_hom_equiv (diagram_comp_preserves_limits G F U) d).symm hd],
      let [ident f'] [":", expr «expr ⟶ »(c, d')] [":=", expr fork.mk_hom (G.map f) (begin
          dsimp ["only"] ["[", expr c, ",", expr d, ",", expr d', ",", expr f, ",", expr diagram_comp_preserves_limits, ",", expr res, "]"] [] [],
          dunfold [ident fork.ι] [],
          ext1 [] [ident j],
          dsimp [] [] [] [],
          simp [] [] ["only"] ["[", expr category.assoc, ",", "<-", expr functor.map_comp_assoc, ",", expr equalizer.lift_ι, ",", expr map_lift_pi_comparison_assoc, "]"] [] [],
          dsimp [] ["[", expr res, "]"] [] [],
          simp [] [] [] [] [] []
        end)],
      haveI [] [":", expr is_iso f'] [":=", expr is_limit.hom_is_iso hc hd' f'],
      exact [expr is_iso.of_iso ((cones.forget _).map_iso (as_iso f'))] } }
end

/-!
As an example, we now have everything we need to check the sheaf condition
for a presheaf of commutative rings, merely by checking the sheaf condition
for the underlying sheaf of types.
```
import algebra.category.CommRing.limits
example (X : Top) (F : presheaf CommRing X) (h : presheaf.is_sheaf (F ⋙ (forget CommRing))) :
  F.is_sheaf :=
(is_sheaf_iff_is_sheaf_comp (forget CommRing) F).mpr h
```
-/


end Presheaf

end Top

