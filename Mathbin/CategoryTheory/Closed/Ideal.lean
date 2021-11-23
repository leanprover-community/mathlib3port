import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts 
import Mathbin.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts 
import Mathbin.CategoryTheory.Monad.Limits 
import Mathbin.CategoryTheory.Adjunction.FullyFaithful 
import Mathbin.CategoryTheory.Adjunction.Reflective 
import Mathbin.CategoryTheory.Closed.Cartesian 
import Mathbin.CategoryTheory.Subterminal

/-!
# Exponential ideals

An exponential ideal of a cartesian closed category `C` is a subcategory `D ⊆ C` such that for any
`B : D` and `A : C`, the exponential `A ⟹ B` is in `D`: resembling ring theoretic ideals. We
define the notion here for inclusion functors `i : D ⥤ C` rather than explicit subcategories to
preserve the principle of equivalence.

We additionally show that if `C` is cartesian closed and `i : D ⥤ C` is a reflective functor, the
following are equivalent.
* The left adjoint to `i` preserves binary (equivalently, finite) products.
* `i` is an exponential ideal.
-/


universe v₁ v₂ u₁ u₂

noncomputable theory

namespace CategoryTheory

open Limits Category

section Ideal

variable{C : Type u₁}{D : Type u₂}[category.{v₁} C][category.{v₁} D]{i : D ⥤ C}

variable(i)[has_finite_products C][cartesian_closed C]

/--
The subcategory `D` of `C` expressed as an inclusion functor is an *exponential ideal* if
`B ∈ D` implies `A ⟹ B ∈ D` for all `A`.
-/
class exponential_ideal : Prop where 
  exp_closed : ∀ {B}, B ∈ i.ess_image → ∀ A, (A ⟹ B) ∈ i.ess_image

/--
To show `i` is an exponential ideal it suffices to show that `A ⟹ iB` is "in" `D` for any `A` in
`C` and `B` in `D`.
-/
theorem exponential_ideal.mk' (h : ∀ B : D A : C, (A ⟹ i.obj B) ∈ i.ess_image) : exponential_ideal i :=
  ⟨fun B hB A =>
      by 
        rcases hB with ⟨B', ⟨iB'⟩⟩
        exact functor.ess_image.of_iso ((exp A).mapIso iB') (h B' A)⟩

/-- The entire category viewed as a subcategory is an exponential ideal. -/
instance  : exponential_ideal (𝟭 C) :=
  exponential_ideal.mk' _ fun B A => ⟨_, ⟨iso.refl _⟩⟩

open CartesianClosed

/-- The subcategory of subterminal objects is an exponential ideal. -/
instance  : exponential_ideal (subterminal_inclusion C) :=
  by 
    apply exponential_ideal.mk' 
    intro B A 
    refine' ⟨⟨A ⟹ B.1, fun Z g h => _⟩, ⟨iso.refl _⟩⟩
    exact uncurry_injective (B.2 (cartesian_closed.uncurry g) (cartesian_closed.uncurry h))

-- error in CategoryTheory.Closed.Ideal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `D` is a reflective subcategory, the property of being an exponential ideal is equivalent to
the presence of a natural isomorphism `i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A`, that is:
`(A ⟹ iB) ≅ i L (A ⟹ iB)`, naturally in `B`.
The converse is given in `exponential_ideal.mk_of_iso`.
-/
def exponential_ideal_reflective
(A : C)
[reflective i]
[exponential_ideal i] : «expr ≅ »(«expr ⋙ »(i, «expr ⋙ »(exp A, «expr ⋙ »(left_adjoint i, i))), «expr ⋙ »(i, exp A)) :=
begin
  symmetry,
  apply [expr nat_iso.of_components _ _],
  { intro [ident X],
    haveI [] [] [":=", expr (exponential_ideal.exp_closed (i.obj_mem_ess_image X) A).unit_is_iso],
    apply [expr as_iso ((adjunction.of_right_adjoint i).unit.app «expr ⟹ »(A, i.obj X))] },
  { simp [] [] [] [] [] [] }
end

/--
Given a natural isomorphism `i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A`, we can show `i`
is an exponential ideal.
-/
theorem exponential_ideal.mk_of_iso [reflective i] (h : ∀ A : C, i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A) :
  exponential_ideal i :=
  by 
    apply exponential_ideal.mk' 
    intro B A 
    exact ⟨_, ⟨(h A).app B⟩⟩

end Ideal

section 

variable{C : Type u₁}{D : Type u₂}[category.{v₁} C][category.{v₁} D]

variable(i : D ⥤ C)

theorem reflective_products [has_finite_products C] [reflective i] : has_finite_products D :=
  ⟨fun J 𝒥₁ 𝒥₂ =>
      by 
        exact has_limits_of_shape_of_reflective i⟩

attribute [local instance] reflective_products

open CartesianClosed

variable[has_finite_products C][reflective i][cartesian_closed C]

-- error in CategoryTheory.Closed.Ideal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If the reflector preserves binary products, the subcategory is an exponential ideal.
This is the converse of `preserves_binary_products_of_exponential_ideal`.
-/
@[priority 10]
instance exponential_ideal_of_preserves_binary_products
[preserves_limits_of_shape (discrete walking_pair) (left_adjoint i)] : exponential_ideal i :=
begin
  let [ident ir] [] [":=", expr adjunction.of_right_adjoint i],
  let [ident L] [":", expr «expr ⥤ »(C, D)] [":=", expr left_adjoint i],
  let [ident η] [":", expr «expr ⟶ »(«expr𝟭»() C, «expr ⋙ »(L, i))] [":=", expr ir.unit],
  let [ident ε] [":", expr «expr ⟶ »(«expr ⋙ »(i, L), «expr𝟭»() D)] [":=", expr ir.counit],
  apply [expr exponential_ideal.mk'],
  intros [ident B, ident A],
  let [ident q] [":", expr «expr ⟶ »(i.obj (L.obj «expr ⟹ »(A, i.obj B)), «expr ⟹ »(A, i.obj B))] [],
  apply [expr cartesian_closed.curry (ir.hom_equiv _ _ _)],
  apply [expr «expr ≫ »(_, (ir.hom_equiv _ _).symm ((ev A).app (i.obj B)))],
  refine [expr «expr ≫ »(prod_comparison L A _, «expr ≫ »(limits.prod.map («expr𝟙»() _) (ε.app _), inv (prod_comparison _ _ _)))],
  have [] [":", expr «expr = »(«expr ≫ »(η.app «expr ⟹ »(A, i.obj B), q), «expr𝟙»() «expr ⟹ »(A, i.obj B))] [],
  { dsimp [] [] [] [],
    rw ["[", "<-", expr curry_natural_left, ",", expr curry_eq_iff, ",", expr uncurry_id_eq_ev, ",", "<-", expr ir.hom_equiv_naturality_left, ",", expr ir.hom_equiv_apply_eq, ",", expr assoc, ",", expr assoc, ",", expr prod_comparison_natural_assoc, ",", expr L.map_id, ",", "<-", expr prod.map_id_comp_assoc, ",", expr ir.left_triangle_components, ",", expr prod.map_id_id, ",", expr id_comp, "]"] [],
    apply [expr is_iso.hom_inv_id_assoc] },
  haveI [] [":", expr split_mono (η.app «expr ⟹ »(A, i.obj B))] [":=", expr ⟨_, this⟩],
  apply [expr mem_ess_image_of_unit_split_mono]
end

variable[exponential_ideal i]

-- error in CategoryTheory.Closed.Ideal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself cartesian closed.
-/ def cartesian_closed_of_reflective : cartesian_closed D :=
{ closed := λ
  B, { is_adj := { right := «expr ⋙ »(i, «expr ⋙ »(exp (i.obj B), left_adjoint i)),
      adj := begin
        apply [expr adjunction.restrict_fully_faithful i i (exp.adjunction (i.obj B))],
        { symmetry,
          apply [expr nat_iso.of_components _ _],
          { intro [ident X],
            haveI [] [] [":=", expr adjunction.right_adjoint_preserves_limits (adjunction.of_right_adjoint i)],
            apply [expr as_iso (prod_comparison i B X)] },
          { intros [ident X, ident Y, ident f],
            dsimp [] [] [] [],
            rw [expr prod_comparison_natural] [],
            simp [] [] [] [] [] [] } },
        { apply [expr (exponential_ideal_reflective i _).symm] }
      end } } }

attribute [-instance] CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit
  CategoryTheory.preservesLimitOfShapeOfCreatesLimitsOfShapeAndHasLimitsOfShape

-- error in CategoryTheory.Closed.Ideal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
We construct a bijection between morphisms `L(A ⨯ B) ⟶ X` and morphisms `LA ⨯ LB ⟶ X`.
This bijection has two key properties:
* It is natural in `X`: See `bijection_natural`.
* When `X = LA ⨯ LB`, then the backwards direction sends the identity morphism to the product
  comparison morphism: See `bijection_symm_apply_id`.

Together these help show that `L` preserves binary products. This should be considered
*internal implementation* towards `preserves_binary_products_of_exponential_ideal`.
-/
noncomputable
def bijection
(A B : C)
(X : D) : «expr ≃ »(«expr ⟶ »((left_adjoint i).obj «expr ⨯ »(A, B), X), «expr ⟶ »(«expr ⨯ »((left_adjoint i).obj A, (left_adjoint i).obj B), X)) :=
calc
  «expr ≃ »(_, «expr ⟶ »(«expr ⨯ »(A, B), i.obj X)) : (adjunction.of_right_adjoint i).hom_equiv _ _
  «expr ≃ »(..., «expr ⟶ »(«expr ⨯ »(B, A), i.obj X)) : (limits.prod.braiding _ _).hom_congr (iso.refl _)
  «expr ≃ »(..., «expr ⟶ »(A, «expr ⟹ »(B, i.obj X))) : (exp.adjunction _).hom_equiv _ _
  «expr ≃ »(..., «expr ⟶ »(i.obj ((left_adjoint i).obj A), «expr ⟹ »(B, i.obj X))) : unit_comp_partial_bijective _ (exponential_ideal.exp_closed (i.obj_mem_ess_image _) _)
  «expr ≃ »(..., «expr ⟶ »(«expr ⨯ »(B, i.obj ((left_adjoint i).obj A)), i.obj X)) : ((exp.adjunction _).hom_equiv _ _).symm
  «expr ≃ »(..., «expr ⟶ »(«expr ⨯ »(i.obj ((left_adjoint i).obj A), B), i.obj X)) : (limits.prod.braiding _ _).hom_congr (iso.refl _)
  «expr ≃ »(..., «expr ⟶ »(B, «expr ⟹ »(i.obj ((left_adjoint i).obj A), i.obj X))) : (exp.adjunction _).hom_equiv _ _
  «expr ≃ »(..., «expr ⟶ »(i.obj ((left_adjoint i).obj B), «expr ⟹ »(i.obj ((left_adjoint i).obj A), i.obj X))) : unit_comp_partial_bijective _ (exponential_ideal.exp_closed (i.obj_mem_ess_image _) _)
  «expr ≃ »(..., «expr ⟶ »(«expr ⨯ »(i.obj ((left_adjoint i).obj A), i.obj ((left_adjoint i).obj B)), i.obj X)) : ((exp.adjunction _).hom_equiv _ _).symm
  «expr ≃ »(..., «expr ⟶ »(i.obj «expr ⨯ »((left_adjoint i).obj A, (left_adjoint i).obj B), i.obj X)) : begin
    apply [expr iso.hom_congr _ (iso.refl _)],
    haveI [] [":", expr preserves_limits i] [":=", expr (adjunction.of_right_adjoint i).right_adjoint_preserves_limits],
    exact [expr (preserves_limit_pair.iso _ _ _).symm]
  end
  «expr ≃ »(..., «expr ⟶ »(«expr ⨯ »((left_adjoint i).obj A, (left_adjoint i).obj B), X)) : (equiv_of_fully_faithful _).symm

theorem bijection_symm_apply_id (A B : C) : (bijection i A B _).symm (𝟙 _) = prod_comparison _ _ _ :=
  by 
    dsimp [bijection]
    rw [comp_id, comp_id, comp_id, i.map_id, comp_id, unit_comp_partial_bijective_symm_apply,
      unit_comp_partial_bijective_symm_apply, uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_curry,
      prod.lift_map_assoc, comp_id, prod.lift_map_assoc, comp_id, prod.comp_lift_assoc, prod.lift_snd,
      prod.lift_fst_assoc, prod.lift_fst_comp_snd_comp, ←adjunction.eq_hom_equiv_apply, adjunction.hom_equiv_unit,
      iso.comp_inv_eq, assoc, preserves_limit_pair.iso_hom]
    apply prod.hom_ext
    ·
      rw [limits.prod.map_fst, assoc, assoc, prod_comparison_fst, ←i.map_comp, prod_comparison_fst]
      apply (adjunction.of_right_adjoint i).Unit.naturality
    ·
      rw [limits.prod.map_snd, assoc, assoc, prod_comparison_snd, ←i.map_comp, prod_comparison_snd]
      apply (adjunction.of_right_adjoint i).Unit.naturality

theorem bijection_natural (A B : C) (X X' : D) (f : (left_adjoint i).obj (A ⨯ B) ⟶ X) (g : X ⟶ X') :
  bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g :=
  by 
    dsimp [bijection]
    apply i.map_injective 
    rw [i.image_preimage, i.map_comp, i.image_preimage, comp_id, comp_id, comp_id, comp_id, comp_id, comp_id,
      adjunction.hom_equiv_naturality_right, ←assoc, curry_natural_right _ (i.map g),
      unit_comp_partial_bijective_natural, uncurry_natural_right, ←assoc, curry_natural_right,
      unit_comp_partial_bijective_natural, uncurry_natural_right, assoc]

/--
The bijection allows us to show that `prod_comparison L A B` is an isomorphism, where the inverse
is the forward map of the identity morphism.
-/
theorem prod_comparison_iso (A B : C) : is_iso (prod_comparison (left_adjoint i) A B) :=
  ⟨⟨bijection i _ _ _ (𝟙 _),
      by 
        rw [←(bijection i _ _ _).Injective.eq_iff, bijection_natural, ←bijection_symm_apply_id, Equiv.apply_symm_apply,
          id_comp],
      by 
        rw [←bijection_natural, id_comp, ←bijection_symm_apply_id, Equiv.apply_symm_apply]⟩⟩

attribute [local instance] prod_comparison_iso

/--
If a reflective subcategory is an exponential ideal, then the reflector preserves binary products.
This is the converse of `exponential_ideal_of_preserves_binary_products`.
-/
noncomputable def preserves_binary_products_of_exponential_ideal :
  preserves_limits_of_shape (discrete walking_pair) (left_adjoint i) :=
  { PreservesLimit :=
      fun K =>
        by 
          apply limits.preserves_limit_of_iso_diagram _ (diagram_iso_pair K).symm 
          apply preserves_limit_pair.of_iso_prod_comparison }

-- error in CategoryTheory.Closed.Ideal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If a reflective subcategory is an exponential ideal, then the reflector preserves finite products.
-/
noncomputable
def preserves_finite_products_of_exponential_ideal
(J : Type*)
[fintype J] : preserves_limits_of_shape (discrete J) (left_adjoint i) :=
begin
  letI [] [] [":=", expr preserves_binary_products_of_exponential_ideal i],
  letI [] [] [":=", expr left_adjoint_preserves_terminal_of_reflective i],
  apply [expr preserves_finite_products_of_preserves_binary_and_terminal (left_adjoint i) J]
end

end 

end CategoryTheory

