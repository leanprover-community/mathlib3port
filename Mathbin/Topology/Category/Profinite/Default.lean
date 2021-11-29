import Mathbin.Topology.Category.CompHaus.Default 
import Mathbin.Topology.Connected 
import Mathbin.Topology.SubsetProperties 
import Mathbin.Topology.LocallyConstant.Basic 
import Mathbin.CategoryTheory.Adjunction.Reflective 
import Mathbin.CategoryTheory.Monad.Limits 
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono 
import Mathbin.CategoryTheory.Fintype

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. finite coproducts
2. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/


universe u

open CategoryTheory

/-- The type of profinite topological spaces. -/
structure Profinite where 
  toCompHaus : CompHaus
  [IsTotallyDisconnected : TotallyDisconnectedSpace to_CompHaus]

namespace Profinite

/--
Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] : Profinite :=
  ⟨⟨⟨X⟩⟩⟩

instance  : Inhabited Profinite :=
  ⟨Profinite.of Pempty⟩

instance category : category Profinite :=
  induced_category.category to_CompHaus

instance concrete_category : concrete_category Profinite :=
  induced_category.concrete_category _

instance has_forget₂ : has_forget₂ Profinite Top :=
  induced_category.has_forget₂ _

instance  : CoeSort Profinite (Type _) :=
  ⟨fun X => X.to_CompHaus⟩

instance  {X : Profinite} : TotallyDisconnectedSpace X :=
  X.is_totally_disconnected

example  {X : Profinite} : CompactSpace X :=
  inferInstance

example  {X : Profinite} : T2Space X :=
  inferInstance

@[simp]
theorem coe_to_CompHaus {X : Profinite} : (X.to_CompHaus : Type _) = X :=
  rfl

@[simp]
theorem coe_id (X : Profinite) : (𝟙 X : X → X) = id :=
  rfl

@[simp]
theorem coe_comp {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = (g ∘ f) :=
  rfl

end Profinite

-- error in Topology.Category.Profinite.Default: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler full
/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps #[], derive #["[", expr full, ",", expr faithful, "]"]]
def Profinite_to_CompHaus : «expr ⥤ »(Profinite, CompHaus) :=
induced_functor _

-- error in Topology.Category.Profinite.Default: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler full
/-- The fully faithful embedding of `Profinite` in `Top`. This is definitionally the same as the
obvious composite. -/
@[simps #[], derive #["[", expr full, ",", expr faithful, "]"]]
def Profinite.to_Top : «expr ⥤ »(Profinite, Top) :=
forget₂ _ _

@[simp]
theorem Profinite.to_CompHaus_to_Top : profiniteToCompHaus ⋙ compHausToTop = Profinite.toTop :=
  rfl

section Profinite

attribute [local instance] connectedComponentSetoid

/--
(Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} :=
  { toCompHaus :=
      { toTop := Top.of (ConnectedComponents X), IsCompact := Quotientₓ.compact_space,
        is_hausdorff := ConnectedComponents.t2 },
    IsTotallyDisconnected := ConnectedComponents.totally_disconnected_space }

/--
(Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
  (CompHaus.toProfiniteObj X ⟶ Y) ≃ X ⟶ profiniteToCompHaus.obj Y :=
  { toFun := fun f => { toFun := f.1 ∘ Quotientₓ.mk, continuous_to_fun := Continuous.comp f.2 continuous_quotient_mk },
    invFun :=
      fun g =>
        { toFun := Continuous.connectedComponentsLift g.2,
          continuous_to_fun := Continuous.connected_components_lift_continuous g.2 },
    left_inv := fun f => ContinuousMap.ext$ fun x => Quotientₓ.induction_on x$ fun a => rfl,
    right_inv := fun f => ContinuousMap.ext$ fun x => rfl }

/--
The connected_components functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHaus.toProfinite : CompHaus ⥤ Profinite :=
  adjunction.left_adjoint_of_equiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl

theorem CompHaus.to_Profinite_obj' (X : CompHaus) : «expr↥ » (CompHaus.toProfinite.obj X) = ConnectedComponents X :=
  rfl

/-- Finite types are given the discrete topology. -/
def Fintypeₓ.discreteTopology (A : Fintypeₓ) : TopologicalSpace A :=
  ⊥

section DiscreteTopology

attribute [local instance] Fintypeₓ.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps]
def Fintypeₓ.toProfinite : Fintypeₓ ⥤ Profinite :=
  { obj := fun A => Profinite.of A, map := fun _ _ f => ⟨f⟩ }

end DiscreteTopology

end Profinite

namespace Profinite

/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`Top.limit_cone`. -/
def limit_cone {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) : limits.cone F :=
  { x :=
      { toCompHaus := (CompHaus.limitCone (F ⋙ profiniteToCompHaus)).x,
        IsTotallyDisconnected :=
          by 
            change TotallyDisconnectedSpace («expr↥ » { u:∀ (j : J), F.obj j | _ })
            exact Subtype.totally_disconnected_space },
    π := { app := (CompHaus.limitCone (F ⋙ profiniteToCompHaus)).π.app } }

/-- The limit cone `Profinite.limit_cone F` is indeed a limit cone. -/
def limit_cone_is_limit {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) : limits.is_limit (limit_cone F) :=
  { lift := fun S => (CompHaus.limitConeIsLimit (F ⋙ profiniteToCompHaus)).lift (profiniteToCompHaus.mapCone S),
    uniq' := fun S m h => (CompHaus.limitConeIsLimit _).uniq (profiniteToCompHaus.mapCone S) _ h }

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
def to_Profinite_adj_to_CompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  adjunction.adjunction_of_equiv_left _ _

/-- The category of profinite sets is reflective in the category of compact hausdroff spaces -/
instance to_CompHaus.reflective : reflective profiniteToCompHaus :=
  { toIsRightAdjoint := ⟨CompHaus.toProfinite, Profinite.toProfiniteAdjToCompHaus⟩ }

noncomputable instance to_CompHaus.creates_limits : creates_limits profiniteToCompHaus :=
  monadic_creates_limits _

noncomputable instance to_Top.reflective : reflective Profinite.toTop :=
  reflective.comp profiniteToCompHaus compHausToTop

noncomputable instance to_Top.creates_limits : creates_limits Profinite.toTop :=
  monadic_creates_limits _

instance has_limits : limits.has_limits Profinite :=
  has_limits_of_has_limits_creates_limits Profinite.toTop

instance has_colimits : limits.has_colimits Profinite :=
  has_colimits_of_reflective profiniteToCompHaus

noncomputable instance forget_preserves_limits : limits.preserves_limits (forget Profinite) :=
  by 
    apply limits.comp_preserves_limits Profinite.toTop (forget Top)

variable{X Y : Profinite.{u}}(f : X ⟶ Y)

/-- Any morphism of profinite spaces is a closed map. -/
theorem IsClosedMap : IsClosedMap f :=
  CompHaus.is_closed_map _

-- error in Topology.Category.Profinite.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
theorem is_iso_of_bijective (bij : function.bijective f) : is_iso f :=
begin
  haveI [] [] [":=", expr CompHaus.is_iso_of_bijective (Profinite_to_CompHaus.map f) bij],
  exact [expr is_iso_of_fully_faithful Profinite_to_CompHaus _]
end

-- error in Topology.Category.Profinite.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
noncomputable
def iso_of_bijective (bij : function.bijective f) : «expr ≅ »(X, Y) :=
by letI [] [] [":=", expr Profinite.is_iso_of_bijective f bij]; exact [expr as_iso f]

instance forget_reflects_isomorphisms : reflects_isomorphisms (forget Profinite) :=
  ⟨by 
      intros A B f hf <;> exact Profinite.is_iso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩

/-- Construct an isomorphism from a homeomorphism. -/
@[simps Hom inv]
def iso_of_homeo (f : X ≃ₜ Y) : X ≅ Y :=
  { Hom := ⟨f, f.continuous⟩, inv := ⟨f.symm, f.symm.continuous⟩,
    hom_inv_id' :=
      by 
        ext x 
        exact f.symm_apply_apply x,
    inv_hom_id' :=
      by 
        ext x 
        exact f.apply_symm_apply x }

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeo_of_iso (f : X ≅ Y) : X ≃ₜ Y :=
  { toFun := f.hom, invFun := f.inv,
    left_inv :=
      fun x =>
        by 
          change (f.hom ≫ f.inv) x = x 
          rw [iso.hom_inv_id, coe_id, id.def],
    right_inv :=
      fun x =>
        by 
          change (f.inv ≫ f.hom) x = x 
          rw [iso.inv_hom_id, coe_id, id.def],
    continuous_to_fun := f.hom.continuous, continuous_inv_fun := f.inv.continuous }

/-- The equivalence between isomorphisms in `Profinite` and homeomorphisms
of topological spaces. -/
@[simps]
def iso_equiv_homeo : (X ≅ Y) ≃ (X ≃ₜ Y) :=
  { toFun := homeo_of_iso, invFun := iso_of_homeo,
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rfl }

-- error in Topology.Category.Profinite.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem epi_iff_surjective {X Y : Profinite.{u}} (f : «expr ⟶ »(X, Y)) : «expr ↔ »(epi f, function.surjective f) :=
begin
  split,
  { contrapose ["!"] [],
    rintros ["⟨", ident y, ",", ident hy, "⟩", ident hf],
    let [ident C] [] [":=", expr set.range f],
    have [ident hC] [":", expr is_closed C] [":=", expr (is_compact_range f.continuous).is_closed],
    let [ident U] [] [":=", expr «expr ᶜ»(C)],
    have [ident hU] [":", expr is_open U] [":=", expr is_open_compl_iff.mpr hC],
    have [ident hyU] [":", expr «expr ∈ »(y, U)] [],
    { refine [expr set.mem_compl _],
      rintro ["⟨", ident y', ",", ident hy', "⟩"],
      exact [expr hy y' hy'] },
    have [ident hUy] [":", expr «expr ∈ »(U, nhds y)] [":=", expr hU.mem_nhds hyU],
    obtain ["⟨", ident V, ",", ident hV, ",", ident hyV, ",", ident hVU, "⟩", ":=", expr is_topological_basis_clopen.mem_nhds_iff.mp hUy],
    classical,
    letI [] [":", expr topological_space «expr $ »(ulift.{u}, fin 2)] [":=", expr «expr⊥»()],
    let [ident Z] [] [":=", expr of «expr $ »(ulift.{u}, fin 2)],
    let [ident g] [":", expr «expr ⟶ »(Y, Z)] [":=", expr ⟨(locally_constant.of_clopen hV).map ulift.up, locally_constant.continuous _⟩],
    let [ident h] [":", expr «expr ⟶ »(Y, Z)] [":=", expr ⟨λ _, ⟨1⟩, continuous_const⟩],
    have [ident H] [":", expr «expr = »(h, g)] [],
    { rw ["<-", expr cancel_epi f] [],
      ext [] [ident x] [],
      dsimp [] ["[", expr locally_constant.of_clopen, "]"] [] [],
      rw [expr if_neg] [],
      { refl },
      refine [expr mt (λ α, hVU α) _],
      simp [] [] ["only"] ["[", expr set.mem_range_self, ",", expr not_true, ",", expr not_false_iff, ",", expr set.mem_compl_eq, "]"] [] [] },
    apply_fun [expr λ e, (e y).down] ["at", ident H] [],
    dsimp [] ["[", expr locally_constant.of_clopen, "]"] [] ["at", ident H],
    rw [expr if_pos hyV] ["at", ident H],
    exact [expr top_ne_bot H] },
  { rw ["<-", expr category_theory.epi_iff_surjective] [],
    apply [expr faithful_reflects_epi (forget Profinite)] }
end

-- error in Topology.Category.Profinite.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mono_iff_injective {X Y : Profinite.{u}} (f : «expr ⟶ »(X, Y)) : «expr ↔ »(mono f, function.injective f) :=
begin
  split,
  { intro [ident h],
    haveI [] [":", expr limits.preserves_limits Profinite_to_CompHaus] [":=", expr infer_instance],
    haveI [] [":", expr mono (Profinite_to_CompHaus.map f)] [":=", expr infer_instance],
    rwa ["<-", expr CompHaus.mono_iff_injective] [] },
  { rw ["<-", expr category_theory.mono_iff_injective] [],
    apply [expr faithful_reflects_mono (forget Profinite)] }
end

end Profinite

