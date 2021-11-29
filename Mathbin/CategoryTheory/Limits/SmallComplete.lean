import Mathbin.CategoryTheory.Limits.Shapes.Products 
import Mathbin.SetTheory.Cardinal

/-!
# Any small complete category is a preorder

We show that any small category which has all (small) limits is a preorder: In particular, we show
that if a small category `C` in universe `u` has products of size `u`, then for any `X Y : C`
there is at most one morphism `X ⟶ Y`.
Note that in Lean, a preorder category is strictly one where the morphisms are in `Prop`, so
we instead show that the homsets are subsingleton.

## References

* https://ncatlab.org/nlab/show/complete+small+category#in_classical_logic

## Tags

small complete, preorder, Freyd
-/


namespace CategoryTheory

open Category Limits

open_locale Cardinal

universe u

variable {C : Type u} [small_category C] [has_products C]

-- error in CategoryTheory.Limits.SmallComplete: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A small category with products is a thin category.

in Lean, a preorder category is one where the morphisms are in Prop, which is weaker than the usual
notion of a preorder/thin category which says that each homset is subsingleton; we show the latter
rather than providing a `preorder C` instance.
-/ instance {X Y : C} : subsingleton «expr ⟶ »(X, Y) :=
⟨λ r s, begin
   classical,
   by_contra [ident r_ne_s],
   have [ident z] [":", expr «expr ≤ »((2 : cardinal), «expr#»() «expr ⟶ »(X, Y))] [],
   { rw [expr cardinal.two_le_iff] [],
     exact [expr ⟨_, _, r_ne_s⟩] },
   let [ident md] [] [":=", expr «exprΣ , »((Z W : C), «expr ⟶ »(Z, W))],
   let [ident α] [] [":=", expr «expr#»() md],
   apply [expr not_le_of_lt (cardinal.cantor α)],
   let [ident yp] [":", expr C] [":=", expr «expr∏ »(λ f : md, Y)],
   transitivity [expr «expr#»() «expr ⟶ »(X, yp)],
   { apply [expr le_trans (cardinal.power_le_power_right z)],
     rw [expr cardinal.power_def] [],
     apply [expr le_of_eq],
     rw [expr cardinal.eq] [],
     refine [expr ⟨⟨pi.lift, λ f k, «expr ≫ »(f, pi.π _ k), _, _⟩⟩],
     { intros [ident f],
       ext [] [ident k] [],
       simp [] [] [] [] [] [] },
     { intros [ident f],
       ext [] [] [],
       simp [] [] [] [] [] [] } },
   { apply [expr cardinal.mk_le_of_injective _],
     { intro [ident f],
       exact [expr ⟨_, _, f⟩] },
     { rintro [ident f, ident g, ident k],
       cases [expr k] [],
       refl } }
 end⟩

end CategoryTheory

