import Mathbin.Topology.Category.Profinite.Default 
import Mathbin.Topology.StoneCech 
import Mathbin.CategoryTheory.Preadditive.Projective

/-!
# Profinite sets have enough projectives

In this file we show that `Profinite` has enough projectives.

## Main results

Let `X` be a profinite set.

* `Profinite.projective_ultrafilter`: the space `ultrafilter X` is a projective object
* `Profinite.projective_presentation`: the natural map `ultrafilter X → X`
  is a projective presentation

-/


noncomputable theory

universe u v w

open CategoryTheory Function

namespace Profinite

-- error in Topology.Category.Profinite.Projective: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance projective_ultrafilter (X : Type u) : projective «expr $ »(of, ultrafilter X) :=
{ factors := λ Y Z f g hg, begin
    rw [expr epi_iff_surjective] ["at", ident hg],
    obtain ["⟨", ident g', ",", ident hg', "⟩", ":=", expr hg.has_right_inverse],
    let [ident t] [":", expr X → Y] [":=", expr «expr ∘ »(g', «expr ∘ »(f, (pure : X → ultrafilter X)))],
    let [ident h] [":", expr ultrafilter X → Y] [":=", expr ultrafilter.extend t],
    have [ident hh] [":", expr continuous h] [":=", expr continuous_ultrafilter_extend _],
    use [expr ⟨h, hh⟩],
    apply [expr faithful.map_injective (forget Profinite)],
    simp [] [] ["only"] ["[", expr forget_map_eq_coe, ",", expr continuous_map.coe_mk, ",", expr coe_comp, "]"] [] [],
    refine [expr dense_range_pure.equalizer (g.continuous.comp hh) f.continuous _],
    rw ["[", expr comp.assoc, ",", expr ultrafilter_extend_extends, ",", "<-", expr comp.assoc, ",", expr hg'.comp_eq_id, ",", expr comp.left_id, "]"] []
  end }

/-- For any profinite `X`, the natural map `ultrafilter X → X` is a projective presentation. -/
def projective_presentation (X : Profinite.{u}) : projective_presentation X :=
  { P := of$ Ultrafilter X, f := ⟨_, continuous_ultrafilter_extend id⟩,
    Projective := Profinite.projective_ultrafilter X,
    Epi :=
      concrete_category.epi_of_surjective _$
        fun x => ⟨(pure x : Ultrafilter X), congr_funₓ (ultrafilter_extend_extends (𝟙 X)) x⟩ }

instance : enough_projectives Profinite.{u} :=
  { presentation := fun X => ⟨projective_presentation X⟩ }

end Profinite

