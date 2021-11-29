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

namespace Monadₓ

open Limits

noncomputable theory

namespace MonadicityInternal

section 

parameter {C : Type u₁}{D : Type u₂}

parameter [category.{v₁} C][category.{v₁} D]

parameter {G : D ⥤ C}[is_right_adjoint G]

local notation "F" => left_adjoint G

local notation "adj" => adjunction.of_right_adjoint G

/--
The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_reflexive (A : adj.toMonad.Algebra) : is_reflexive_pair (F.map A.a) (adj.counit.app (F.obj A.A)) :=
  by 
    apply is_reflexive_pair.mk' (F.map (adj.Unit.app _)) _ _
    ·
      rw [←F.map_comp, ←F.map_id]
      exact congr_argₓ (fun _ => F.map _) A.unit
    ·
      rw [adj.left_triangle_components]
      rfl

/--
The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
instance main_pair_G_split (A : adj.toMonad.Algebra) : G.is_split_pair (F.map A.a) (adj.counit.app (F.obj A.A)) :=
  { splittable := ⟨_, _, ⟨beck_split_coequalizer A⟩⟩ }

/-- The object function for the left adjoint to the comparison functor. -/
def comparison_left_adjoint_obj (A : adj.toMonad.Algebra) [has_coequalizer (F.map A.a) (adj.counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)

/--
We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
@[simps]
def comparison_left_adjoint_hom_equiv (A : adj.toMonad.Algebra) (B : D)
  [has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
  (comparison_left_adjoint_obj A ⟶ B) ≃ (A ⟶ (comparison adj).obj B) :=
  calc (comparison_left_adjoint_obj A ⟶ B) ≃ { f : F.obj A.A ⟶ B // _ } :=
    cofork.is_colimit.hom_iso (colimit.is_colimit _) B 
    _ ≃ { g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } :=
    by 
      refine' (adj.homEquiv _ _).subtypeEquiv _ 
      intro f 
      rw [←(adj.homEquiv _ _).Injective.eq_iff, adjunction.hom_equiv_naturality_left, adj.hom_equiv_unit,
        adj.hom_equiv_unit, G.map_comp]
      dsimp 
      rw [adj.right_triangle_components_assoc, ←G.map_comp, F.map_comp, category.assoc, adj.counit_naturality,
        adj.left_triangle_components_assoc]
      apply eq_comm 
    _ ≃ (A ⟶ (comparison adj).obj B) :=
    { toFun := fun g => { f := _, h' := g.prop }, invFun := fun f => ⟨f.f, f.h⟩,
      left_inv :=
        fun g =>
          by 
            ext 
            rfl,
      right_inv :=
        fun f =>
          by 
            ext 
            rfl }
    

/--
Construct the adjunction to the comparison functor.
-/
def left_adjoint_comparison [∀ A : adj.toMonad.Algebra, has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
  adj.toMonad.Algebra ⥤ D :=
  by 
    refine'
      @adjunction.left_adjoint_of_equiv _ _ _ _ (comparison adj) (fun A => comparison_left_adjoint_obj A) (fun A B => _)
        _
    ·
      apply comparison_left_adjoint_hom_equiv
    ·
      intro A B B' g h 
      ext1 
      dsimp [comparison_left_adjoint_hom_equiv]
      rw [←adj.hom_equiv_naturality_right, category.assoc]

/--
Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
-/
@[simps counit]
def comparison_adjunction [∀ A : adj.toMonad.Algebra, has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
  left_adjoint_comparison ⊣ comparison adj :=
  adjunction.adjunction_of_equiv_left _ _

theorem comparison_adjunction_unit_f_aux
  [∀ A : adj.toMonad.Algebra, has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] (A : adj.toMonad.Algebra) :
  (comparison_adjunction.unit.app A).f = adj.homEquiv A.A _ (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  congr_argₓ (adj.homEquiv _ _) (category.comp_id _)

/--
This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
@[simps]
def unit_cofork (A : adj.toMonad.Algebra) [has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
  cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj A.A))) :=
  cofork.of_π (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))))
    (by 
      change _ = G.map _ ≫ _ 
      rw [←G.map_comp, coequalizer.condition, G.map_comp])

theorem comparison_adjunction_unit_f
  [∀ A : adj.toMonad.Algebra, has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] (A : adj.toMonad.Algebra) :
  (comparison_adjunction.unit.app A).f = (beck_coequalizer A).desc (unit_cofork A) :=
  by 
    apply limits.cofork.is_colimit.hom_ext (beck_coequalizer A)
    rw [is_colimit.fac]
    dsimp only [cofork.π_eq_app_one, beck_cofork_ι_app, unit_cofork_ι_app]
    rw [comparison_adjunction_unit_f_aux, ←adj.hom_equiv_naturality_left A.a, coequalizer.condition,
      adj.hom_equiv_naturality_right, adj.hom_equiv_unit, category.assoc]
    apply adj.right_triangle_components_assoc

/--
The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
@[simps]
def counit_cofork (B : D) : cofork (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B))) :=
  cofork.of_π (adj.counit.app B) (adj.counit_naturality _)

/-- The unit cofork is a colimit provided `G` preserves it.  -/
def unit_colimit_of_preserves_coequalizer (A : adj.toMonad.Algebra)
  [has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
  [preserves_colimit (parallel_pair (F.map A.a) (adj.counit.app (F.obj A.A))) G] : is_colimit (unit_cofork A) :=
  is_colimit_of_has_coequalizer_of_preserves_colimit G _ _

/-- The counit cofork is a colimit provided `G` reflects it. -/
def counit_coequalizer_of_reflects_coequalizer (B : D)
  [reflects_colimit (parallel_pair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B)))) G] :
  is_colimit (counit_cofork B) :=
  is_colimit_of_is_colimit_cofork_map G _ (beck_coequalizer ((comparison adj).obj B))

theorem comparison_adjunction_counit_app
  [∀ A : adj.toMonad.Algebra, has_coequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] (B : D) :
  comparison_adjunction.counit.app B = colimit.desc _ (counit_cofork B) :=
  by 
    apply coequalizer.hom_ext 
    change
      coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ = coequalizer.π _ _ ≫ coequalizer.desc _ _ 
    simp 

end 

end MonadicityInternal

open CategoryTheory.Adjunction

open MonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [category.{v₁} C] [category.{v₁} D]

variable (G : D ⥤ C)

/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadic_of_creates_G_split_coequalizers`.
-/
def creates_G_split_coequalizers_of_monadic [monadic_right_adjoint G] ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g] :
  creates_colimit (parallel_pair f g) G :=
  by 
    apply monadic_creates_colimit_of_preserves_colimit _ _ 
    infer_instance
    ·
      apply preserves_colimit_of_iso_diagram _ (diagram_iso_parallel_pair _).symm 
      dsimp 
      infer_instance
    ·
      apply preserves_colimit_of_iso_diagram _ (diagram_iso_parallel_pair _).symm 
      dsimp 
      infer_instance

variable [is_right_adjoint G]

section BeckMonadicity

-- error in CategoryTheory.Monad.Monadicity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `C` has them.
-/
def monadic_of_has_preserves_reflects_G_split_coequalizers
[∀ {{A B}} (f g : «expr ⟶ »(A, B)) [G.is_split_pair f g], has_coequalizer f g]
[∀ {{A B}} (f g : «expr ⟶ »(A, B)) [G.is_split_pair f g], preserves_colimit (parallel_pair f g) G]
[∀
 {{A B}}
 (f g : «expr ⟶ »(A, B))
 [G.is_split_pair f g], reflects_colimit (parallel_pair f g) G] : monadic_right_adjoint G :=
begin
  let [ident L] [":", expr «expr ⥤ »((adjunction.of_right_adjoint G).to_monad.algebra, D)] [":=", expr left_adjoint_comparison],
  letI [ident i] [":", expr is_right_adjoint (comparison (of_right_adjoint G))] [":=", expr ⟨_, comparison_adjunction⟩],
  constructor,
  let [] [":", expr ∀
   X : (of_right_adjoint G).to_monad.algebra, is_iso ((of_right_adjoint (comparison (of_right_adjoint G))).unit.app X)] [],
  { intro [ident X],
    apply [expr is_iso_of_reflects_iso _ (monad.forget (of_right_adjoint G).to_monad)],
    { change [expr is_iso (comparison_adjunction.unit.app X).f] [] [],
      rw [expr comparison_adjunction_unit_f] [],
      change [expr is_iso (is_colimit.cocone_point_unique_up_to_iso (beck_coequalizer X) (unit_colimit_of_preserves_coequalizer X)).hom] [] [],
      refine [expr is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _)] } },
  let [] [":", expr ∀ Y : D, is_iso ((of_right_adjoint (comparison (of_right_adjoint G))).counit.app Y)] [],
  { intro [ident Y],
    change [expr is_iso (comparison_adjunction.counit.app Y)] [] [],
    rw [expr comparison_adjunction_counit_app] [],
    change [expr is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).hom] [] [],
    apply_instance,
    apply [expr counit_coequalizer_of_reflects_coequalizer _],
    letI [] [":", expr G.is_split_pair ((left_adjoint G).map (G.map ((adjunction.of_right_adjoint G).counit.app Y))) ((adjunction.of_right_adjoint G).counit.app ((left_adjoint G).obj (G.obj Y)))] [":=", expr monadicity_internal.main_pair_G_split ((comparison (adjunction.of_right_adjoint G)).obj Y)],
    apply_instance },
  exactI [expr adjunction.is_right_adjoint_to_is_equivalence]
end

-- error in CategoryTheory.Monad.Monadicity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
This is the converse of `creates_G_split_of_monadic`.
-/
def monadic_of_creates_G_split_coequalizers
[∀
 {{A B}}
 (f g : «expr ⟶ »(A, B))
 [G.is_split_pair f g], creates_colimit (parallel_pair f g) G] : monadic_right_adjoint G :=
begin
  letI [] [":", expr ∀
   {{A B}}
   (f g : «expr ⟶ »(A, B))
   [G.is_split_pair f g], has_colimit «expr ⋙ »(parallel_pair f g, G)] [],
  { introsI [ident A, ident B, ident f, ident g, ident i],
    apply [expr has_colimit_of_iso (diagram_iso_parallel_pair.{v₁} _)],
    change [expr has_coequalizer (G.map f) (G.map g)] [] [],
    apply_instance },
  apply [expr monadic_of_has_preserves_reflects_G_split_coequalizers _],
  { apply_instance },
  { introsI [ident A, ident B, ident f, ident g, ident i],
    apply [expr has_colimit_of_created (parallel_pair f g) G] },
  { introsI [ident A, ident B, ident f, ident g, ident i],
    apply_instance },
  { introsI [ident A, ident B, ident f, ident g, ident i],
    apply_instance }
end

/--
An alternate version of Beck's monadicity theorem. If `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
def monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms [reflects_isomorphisms G]
  [∀ ⦃A B⦄ f g : A ⟶ B [G.is_split_pair f g], has_coequalizer f g]
  [∀ ⦃A B⦄ f g : A ⟶ B [G.is_split_pair f g], preserves_colimit (parallel_pair f g) G] : monadic_right_adjoint G :=
  by 
    apply monadic_of_has_preserves_reflects_G_split_coequalizers _
    ·
      infer_instance
    ·
      assumption
    ·
      assumption
    ·
      intros A B f g i 
      apply reflects_colimit_of_reflects_isomorphisms

end BeckMonadicity

section ReflexiveMonadicity

variable [has_reflexive_coequalizers D] [reflects_isomorphisms G]

variable [∀ ⦃A B⦄ f g : A ⟶ B [is_reflexive_pair f g], preserves_colimit (parallel_pair f g) G]

-- error in CategoryTheory.Monad.Monadicity: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/ def monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms : monadic_right_adjoint G :=
begin
  let [ident L] [":", expr «expr ⥤ »((adjunction.of_right_adjoint G).to_monad.algebra, D)] [":=", expr left_adjoint_comparison],
  letI [ident i] [":", expr is_right_adjoint (comparison (adjunction.of_right_adjoint G))] [":=", expr ⟨_, comparison_adjunction⟩],
  constructor,
  let [] [":", expr ∀
   X : (adjunction.of_right_adjoint G).to_monad.algebra, is_iso ((adjunction.of_right_adjoint (comparison (adjunction.of_right_adjoint G))).unit.app X)] [],
  { intro [ident X],
    apply [expr is_iso_of_reflects_iso _ (monad.forget (adjunction.of_right_adjoint G).to_monad)],
    { change [expr is_iso (comparison_adjunction.unit.app X).f] [] [],
      rw [expr comparison_adjunction_unit_f] [],
      change [expr is_iso (is_colimit.cocone_point_unique_up_to_iso (beck_coequalizer X) (unit_colimit_of_preserves_coequalizer X)).hom] [] [],
      apply [expr is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _)] } },
  let [] [":", expr ∀ Y : D, is_iso ((of_right_adjoint (comparison (adjunction.of_right_adjoint G))).counit.app Y)] [],
  { intro [ident Y],
    change [expr is_iso (comparison_adjunction.counit.app Y)] [] [],
    rw [expr comparison_adjunction_counit_app] [],
    change [expr is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).hom] [] [],
    apply_instance,
    apply [expr counit_coequalizer_of_reflects_coequalizer _],
    apply [expr reflects_colimit_of_reflects_isomorphisms] },
  exactI [expr adjunction.is_right_adjoint_to_is_equivalence]
end

end ReflexiveMonadicity

end Monadₓ

end CategoryTheory

