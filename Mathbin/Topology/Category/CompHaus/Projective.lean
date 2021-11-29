import Mathbin.Topology.Category.CompHaus.Default 
import Mathbin.Topology.StoneCech 
import Mathbin.CategoryTheory.Preadditive.Projective

/-!
# CompHaus has enough projectives

In this file we show that `CompHaus` has enough projectives.

## Main results

Let `X` be a compact Hausdorff space.

* `CompHaus.projective_ultrafilter`: the space `ultrafilter X` is a projective object
* `CompHaus.projective_presentation`: the natural map `ultrafilter X → X`
  is a projective presentation

## Reference

See [miraglia2006introduction] Chapter 21 for a proof that `CompHaus` has enough projectives.

-/


noncomputable theory

open CategoryTheory Function

namespace CompHaus

-- error in Topology.Category.CompHaus.Projective: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance projective_ultrafilter (X : Type*) : projective «expr $ »(of, ultrafilter X) :=
{ factors := λ Y Z f g hg, begin
    rw [expr epi_iff_surjective] ["at", ident hg],
    obtain ["⟨", ident g', ",", ident hg', "⟩", ":=", expr hg.has_right_inverse],
    let [ident t] [":", expr X → Y] [":=", expr «expr ∘ »(g', «expr ∘ »(f, (pure : X → ultrafilter X)))],
    let [ident h] [":", expr ultrafilter X → Y] [":=", expr ultrafilter.extend t],
    have [ident hh] [":", expr continuous h] [":=", expr continuous_ultrafilter_extend _],
    use [expr ⟨h, hh⟩],
    apply [expr faithful.map_injective (forget CompHaus)],
    simp [] [] ["only"] ["[", expr forget_map_eq_coe, ",", expr continuous_map.coe_mk, ",", expr coe_comp, "]"] [] [],
    convert [] [expr dense_range_pure.equalizer (g.continuous.comp hh) f.continuous _] [],
    rw ["[", expr comp.assoc, ",", expr ultrafilter_extend_extends, ",", "<-", expr comp.assoc, ",", expr hg'.comp_eq_id, ",", expr comp.left_id, "]"] []
  end }

/-- For any compact Hausdorff space `X`,
  the natural map `ultrafilter X → X` is a projective presentation. -/
def projective_presentation (X : CompHaus) : projective_presentation X :=
  { P := of$ Ultrafilter X, f := ⟨_, continuous_ultrafilter_extend id⟩, Projective := CompHaus.projective_ultrafilter X,
    Epi :=
      concrete_category.epi_of_surjective _$
        fun x => ⟨(pure x : Ultrafilter X), congr_funₓ (ultrafilter_extend_extends (𝟙 X)) x⟩ }

instance : enough_projectives CompHaus :=
  { presentation := fun X => ⟨projective_presentation X⟩ }

end CompHaus

