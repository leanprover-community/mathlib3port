import Mathbin.Topology.Category.Top.OpenNhds 
import Mathbin.Topology.Sheaves.Presheaf 
import Mathbin.Topology.Sheaves.SheafCondition.UniqueGluing 
import Mathbin.CategoryTheory.Limits.Types 
import Mathbin.CategoryTheory.Limits.Preserves.Filtered 
import Mathbin.Tactic.Elementwise

/-!
# Stalks

For a presheaf `F` on a topological space `X`, valued in some category `C`, the *stalk* of `F`
at the point `x : X` is defined as the colimit of the following functor

(nhds x)ᵒᵖ ⥤ (opens X)ᵒᵖ ⥤ C

where the functor on the left is the inclusion of categories and the functor on the right is `F`.
For an open neighborhood `U` of `x`, we define the map `F.germ x : F.obj (op U) ⟶ F.stalk x` as the
canonical morphism into this colimit.

Taking stalks is functorial: For every point `x : X` we define a functor `stalk_functor C x`,
sending presheaves on `X` to objects of `C`. Furthermore, for a map `f : X ⟶ Y` between
topological spaces, we define `stalk_pushforward` as the induced map on the stalks
`(f _* ℱ).stalk (f x) ⟶ ℱ.stalk x`.

Some lemmas about stalks and germs only hold for certain classes of concrete categories. A basic
property of forgetful functors of categories of algebraic structures (like `Mon`, `CommRing`,...)
is that they preserve filtered colimits. Since stalks are filtered colimits, this ensures that
the stalks of presheaves valued in these categories behave exactly as for `Type`-valued presheaves.
For example, in `germ_exist` we prove that in such a category, every element of the stalk is the
germ of a section.

Furthermore, if we require the forgetful functor to reflect isomorphisms and preserve limits (as
is the case for most algebraic structures), we have access to the unique gluing API and can prove
further properties. Most notably, in `is_iso_iff_stalk_functor_map_iso`, we prove that in such
a category, a morphism of sheaves is an isomorphism if and only if all of its stalk maps are
isomorphisms.

See also the definition of "algebraic structures" in the stacks project:
https://stacks.math.columbia.edu/tag/007L

-/


noncomputable theory

universe v u v' u'

open CategoryTheory

open Top

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

variable{C : Type u}[category.{v} C]

variable[has_colimits.{v} C]

variable{X Y Z : Top.{v}}

namespace Top.Presheaf

variable(C)

/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalk_functor (x : X) : X.presheaf C ⥤ C :=
  (whiskering_left _ _ C).obj (open_nhds.inclusion x).op ⋙ colim

variable{C}

/--
The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.presheaf C) (x : X) : C :=
  (stalk_functor C x).obj ℱ

@[simp]
theorem stalk_functor_obj (ℱ : X.presheaf C) (x : X) : (stalk_functor C x).obj ℱ = ℱ.stalk x :=
  rfl

/--
The germ of a section of a presheaf over an open at a point of that open.
-/
def germ (F : X.presheaf C) {U : opens X} (x : U) : F.obj (op U) ⟶ stalk F x :=
  colimit.ι ((open_nhds.inclusion x.1).op ⋙ F) (op ⟨U, x.2⟩)

@[simp, elementwise]
theorem germ_res (F : X.presheaf C) {U V : opens X} (i : U ⟶ V) (x : U) : F.map i.op ≫ germ F x = germ F (i x : V) :=
  let i' : (⟨U, x.2⟩ : open_nhds x.1) ⟶ ⟨V, (i x : V).2⟩ := i 
  colimit.w ((open_nhds.inclusion x.1).op ⋙ F) i'.op

/--
A morphism from the stalk of `F` at `x` to some object `Y` is completely determined by its
composition with the `germ` morphisms.
-/
theorem stalk_hom_ext (F : X.presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
  (ih : ∀ U : opens X hxU : x ∈ U, F.germ ⟨x, hxU⟩ ≫ f₁ = F.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
  colimit.hom_ext$
    fun U =>
      by 
        induction U using Opposite.rec 
        cases' U with U hxU 
        exact ih U hxU

@[simp, reassoc, elementwise]
theorem stalk_functor_map_germ {F G : X.presheaf C} (U : opens X) (x : U) (f : F ⟶ G) :
  germ F x ≫ (stalk_functor C x.1).map f = f.app (op U) ≫ germ G x :=
  colimit.ι_map (whisker_left (open_nhds.inclusion x.1).op f) (op ⟨U, x.2⟩)

variable(C)

/--
For a presheaf `F` on a space `X`, a continuous map `f : X ⟶ Y` induces a morphisms between the
stalk of `f _ * F` at `f x` and the stalk of `F` at `x`.
-/
def stalk_pushforward (f : X ⟶ Y) (F : X.presheaf C) (x : X) : (f _* F).stalk (f x) ⟶ F.stalk x :=
  by 
    trans 
    swap 
    exact colimit.pre _ (open_nhds.map f x).op 
    exact colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) F)

@[simp, elementwise, reassoc]
theorem stalk_pushforward_germ (f : X ⟶ Y) (F : X.presheaf C) (U : opens Y) (x : (opens.map f).obj U) :
  (f _* F).germ ⟨f x, x.2⟩ ≫ F.stalk_pushforward C f x = F.germ x :=
  by 
    rw [stalk_pushforward, germ, colimit.ι_map_assoc, colimit.ι_pre, whisker_right_app]
    erw [CategoryTheory.Functor.map_id, category.id_comp]
    rfl

namespace StalkPushforward

attribute [local tidy] tactic.op_induction'

@[simp]
theorem id (ℱ : X.presheaf C) (x : X) :
  ℱ.stalk_pushforward C (𝟙 X) x = (stalk_functor C x).map (pushforward.id ℱ).hom :=
  by 
    dsimp [stalk_pushforward, stalk_functor]
    ext1 
    runTac 
      tactic.op_induction' 
    cases j 
    cases j_val 
    rw [colimit.ι_map_assoc, colimit.ι_map, colimit.ι_pre, whisker_left_app, whisker_right_app, pushforward.id_hom_app,
      eq_to_hom_map, eq_to_hom_refl]
    dsimp 
    erw [CategoryTheory.Functor.map_id]

@[simp]
theorem comp (ℱ : X.presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  ℱ.stalk_pushforward C (f ≫ g) x = (f _* ℱ).stalkPushforward C g (f x) ≫ ℱ.stalk_pushforward C f x :=
  by 
    dsimp [stalk_pushforward, stalk_functor]
    ext U 
    induction U using Opposite.rec 
    cases U 
    cases U_val 
    simp only [colimit.ι_map_assoc, colimit.ι_pre_assoc, whisker_right_app, category.assoc]
    dsimp 
    erw [CategoryTheory.Functor.map_id, category.id_comp, category.id_comp, category.id_comp, colimit.ι_pre,
      colimit.ι_pre]
    rfl

end StalkPushforward

section StalkPullback

/-- The morphism `ℱ_{f x} ⟶ (f⁻¹ℱ)ₓ` that factors through `(f_*f⁻¹ℱ)_{f x}`. -/
def stalk_pullback_hom (f : X ⟶ Y) (F : Y.presheaf C) (x : X) : F.stalk (f x) ⟶ (pullback_obj f F).stalk x :=
  (stalk_functor _ (f x)).map ((pushforward_pullback_adjunction C f).Unit.app F) ≫ stalk_pushforward _ _ _ x

/-- The morphism `(f⁻¹ℱ)(U) ⟶ ℱ_{f(x)}` for some `U ∋ x`. -/
def germ_to_pullback_stalk (f : X ⟶ Y) (F : Y.presheaf C) (U : opens X) (x : U) :
  (pullback_obj f F).obj (op U) ⟶ F.stalk (f x) :=
  colimit.desc (Lan.diagram (opens.map f).op F (op U))
    { x := F.stalk (f x),
      ι :=
        { app := fun V => F.germ ⟨f x, V.hom.unop.le x.2⟩,
          naturality' :=
            fun _ _ i =>
              by 
                erw [category.comp_id]
                exact F.germ_res i.left.unop _ } }

/-- The morphism `(f⁻¹ℱ)ₓ ⟶ ℱ_{f(x)}`. -/
def stalk_pullback_inv (f : X ⟶ Y) (F : Y.presheaf C) (x : X) : (pullback_obj f F).stalk x ⟶ F.stalk (f x) :=
  colimit.desc ((open_nhds.inclusion x).op ⋙ presheaf.pullback_obj f F)
    { x := F.stalk (f x),
      ι :=
        { app := fun U => F.germ_to_pullback_stalk _ f (unop U).1 ⟨x, (unop U).2⟩,
          naturality' :=
            fun _ _ _ =>
              by 
                erw [colimit.pre_desc, category.comp_id]
                congr } }

/-- The isomorphism `ℱ_{f(x)} ≅ (f⁻¹ℱ)ₓ`. -/
def stalk_pullback_iso (f : X ⟶ Y) (F : Y.presheaf C) (x : X) : F.stalk (f x) ≅ (pullback_obj f F).stalk x :=
  { hom := stalk_pullback_hom _ _ _ _, inv := stalk_pullback_inv _ _ _ _,
    hom_inv_id' :=
      by 
        delta' stalk_pullback_hom stalk_pullback_inv stalk_functor presheaf.pullback stalk_pushforward
          germ_to_pullback_stalk germ 
        ext j 
        induction j using Opposite.rec 
        cases j 
        simp only [TopologicalSpace.OpenNhds.inclusion_map_iso_inv, whisker_right_app, whisker_left_app,
          whiskering_left_obj_map, functor.comp_map, colimit.ι_map_assoc, nat_trans.op_id, Lan_obj_map,
          pushforward_pullback_adjunction_unit_app_app, category.assoc, colimit.ι_pre_assoc]
        erw [colimit.ι_desc, colimit.pre_desc, colimit.ι_desc, category.comp_id]
        simpa,
    inv_hom_id' :=
      by 
        delta' stalk_pullback_hom stalk_pullback_inv stalk_functor presheaf.pullback stalk_pushforward 
        ext U j 
        induction U using Opposite.rec 
        cases U 
        cases j 
        cases j_right 
        erw [colimit.map_desc, colimit.map_desc, colimit.ι_desc_assoc, colimit.ι_desc_assoc, colimit.ι_desc,
          category.comp_id]
        simp only [cocone.whisker_ι, colimit.cocone_ι, open_nhds.inclusion_map_iso_inv, cocones.precompose_obj_ι,
          whisker_right_app, whisker_left_app, nat_trans.comp_app, whiskering_left_obj_map, nat_trans.op_id,
          Lan_obj_map, pushforward_pullback_adjunction_unit_app_app]
        erw
          [←colimit.w _
            (@hom_of_le (open_nhds x) _ ⟨_, U_property⟩ ⟨(opens.map f).obj (unop j_left), j_hom.unop.le U_property⟩
                j_hom.unop.le).op]
        erw [colimit.ι_pre_assoc (Lan.diagram _ F _) (costructured_arrow.map _)]
        erw [colimit.ι_pre_assoc (Lan.diagram _ F _) (costructured_arrow.map _)]
        congr 
        simp only [category.assoc, costructured_arrow.map_mk]
        delta' costructured_arrow.mk 
        congr }

end StalkPullback

section Concrete

variable{C}

variable[concrete_category.{v} C]

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

@[ext]
theorem germ_ext (F : X.presheaf C) {U V : opens X} {x : X} {hxU : x ∈ U} {hxV : x ∈ V} (W : opens X) (hxW : x ∈ W)
  (iWU : W ⟶ U) (iWV : W ⟶ V) {sU : F.obj (op U)} {sV : F.obj (op V)} (ih : F.map iWU.op sU = F.map iWV.op sV) :
  F.germ ⟨x, hxU⟩ sU = F.germ ⟨x, hxV⟩ sV :=
  by 
    erw [←F.germ_res iWU ⟨x, hxW⟩, ←F.germ_res iWV ⟨x, hxW⟩, comp_apply, comp_apply, ih]

variable[preserves_filtered_colimits (forget C)]

/--
For presheaves valued in a concrete category whose forgetful functor preserves filtered colimits,
every element of the stalk is the germ of a section.
-/
theorem germ_exist (F : X.presheaf C) (x : X) (t : stalk F x) :
  ∃ (U : opens X)(m : x ∈ U)(s : F.obj (op U)), F.germ ⟨x, m⟩ s = t :=
  by 
    obtain ⟨U, s, e⟩ := types.jointly_surjective _ (is_colimit_of_preserves (forget C) (colimit.is_colimit _)) t 
    revert s e 
    rw [show U = op (unop U) from rfl]
    generalize unop U = V 
    clear U 
    cases' V with V m 
    intro s e 
    exact ⟨V, m, s, e⟩

theorem germ_eq (F : X.presheaf C) {U V : opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V) (s : F.obj (op U))
  (t : F.obj (op V)) (h : germ F ⟨x, mU⟩ s = germ F ⟨x, mV⟩ t) :
  ∃ (W : opens X)(m : x ∈ W)(iU : W ⟶ U)(iV : W ⟶ V), F.map iU.op s = F.map iV.op t :=
  by 
    obtain ⟨W, iU, iV, e⟩ :=
      (types.filtered_colimit.is_colimit_eq_iff _
            (is_colimit_of_preserves _ (colimit.is_colimit ((open_nhds.inclusion x).op ⋙ F)))).mp
        h 
    exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩

theorem stalk_functor_map_injective_of_app_injective {F G : presheaf C X} (f : F ⟶ G)
  (h : ∀ U : opens X, Function.Injective (f.app (op U))) (x : X) : Function.Injective ((stalk_functor C x).map f) :=
  fun s t hst =>
    by 
      rcases germ_exist F x s with ⟨U₁, hxU₁, s, rfl⟩
      rcases germ_exist F x t with ⟨U₂, hxU₂, t, rfl⟩
      simp only [stalk_functor_map_germ_apply _ ⟨x, _⟩] at hst 
      obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst 
      rw [←comp_apply, ←comp_apply, ←f.naturality, ←f.naturality, comp_apply, comp_apply] at heq 
      replace heq := h W HEq 
      convert congr_argₓ (F.germ ⟨x, hxW⟩) HEq 
      exacts[(F.germ_res_apply iWU₁ ⟨x, hxW⟩ s).symm, (F.germ_res_apply iWU₂ ⟨x, hxW⟩ t).symm]

variable[has_limits C][preserves_limits (forget C)][reflects_isomorphisms (forget C)]

/--
Let `F` be a sheaf valued in a concrete category, whose forgetful functor reflects isomorphisms,
preserves limits and filtered colimits. Then two sections who agree on every stalk must be equal.
-/
theorem section_ext (F : sheaf C X) (U : opens X) (s t : F.1.obj (op U)) (h : ∀ x : U, F.1.germ x s = F.1.germ x t) :
  s = t :=
  by 
    choose V m i₁ i₂ heq using fun x : U => F.1.germ_eq x.1 x.2 x.2 s t (h x)
    apply F.eq_of_locally_eq' V U i₁
    ·
      intro x hxU 
      rw [opens.mem_coe, opens.mem_supr]
      exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
    ·
      intro x 
      rw [HEq, Subsingleton.elimₓ (i₁ x) (i₂ x)]

theorem app_injective_of_stalk_functor_map_injective {F : sheaf C X} {G : presheaf C X} (f : F.1 ⟶ G)
  (h : ∀ x : X, Function.Injective ((stalk_functor C x).map f)) (U : opens X) : Function.Injective (f.app (op U)) :=
  fun s t hst =>
    section_ext F _ _ _$
      fun x =>
        h x.1$
          by 
            rw [stalk_functor_map_germ_apply, stalk_functor_map_germ_apply, hst]

theorem app_injective_iff_stalk_functor_map_injective {F : sheaf C X} {G : presheaf C X} (f : F.1 ⟶ G) :
  (∀ x : X, Function.Injective ((stalk_functor C x).map f)) ↔ ∀ U : opens X, Function.Injective (f.app (op U)) :=
  ⟨app_injective_of_stalk_functor_map_injective f, stalk_functor_map_injective_of_app_injective f⟩

-- error in Topology.Sheaves.Stalks: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For surjectivity, we are given an arbitrary section `t` and need to find a preimage for it.
We claim that it suffices to find preimages *locally*. That is, for each `x : U` we construct
a neighborhood `V ≤ U` and a section `s : F.obj (op V))` such that `f.app (op V) s` and `t`
agree on `V`. -/
theorem app_surjective_of_injective_of_locally_surjective
{F G : sheaf C X}
(f : «expr ⟶ »(F, G))
(hinj : ∀ x : X, function.injective ((stalk_functor C x).map f))
(U : opens X)
(hsurj : ∀
 (t)
 (x : U), «expr∃ , »((V : opens X)
  (m : «expr ∈ »(x.1, V))
  (iVU : «expr ⟶ »(V, U))
  (s : F.1.obj (op V)), «expr = »(f.app (op V) s, G.1.map iVU.op t))) : function.surjective (f.app (op U)) :=
begin
  intro [ident t],
  choose [] [ident V] [ident mV, ident iVU, ident sf, ident heq] ["using", expr hsurj t],
  have [ident V_cover] [":", expr «expr ≤ »(U, supr V)] [],
  { intros [ident x, ident hxU],
    rw ["[", expr opens.mem_coe, ",", expr opens.mem_supr, "]"] [],
    exact [expr ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩] },
  obtain ["⟨", ident s, ",", ident s_spec, ",", "-", "⟩", ":=", expr F.exists_unique_gluing' V U iVU V_cover sf _],
  { use [expr s],
    apply [expr G.eq_of_locally_eq' V U iVU V_cover],
    intro [ident x],
    rw ["[", "<-", expr comp_apply, ",", "<-", expr f.naturality, ",", expr comp_apply, ",", expr s_spec, ",", expr heq, "]"] [] },
  { intros [ident x, ident y],
    apply [expr section_ext],
    intro [ident z],
    apply [expr hinj z],
    erw ["[", expr stalk_functor_map_germ_apply, ",", expr stalk_functor_map_germ_apply, "]"] [],
    simp_rw ["[", "<-", expr comp_apply, ",", expr f.naturality, ",", expr comp_apply, ",", expr heq, ",", "<-", expr comp_apply, ",", "<-", expr G.1.map_comp, "]"] [],
    refl }
end

theorem app_surjective_of_stalk_functor_map_bijective {F G : sheaf C X} (f : F ⟶ G)
  (h : ∀ x : X, Function.Bijective ((stalk_functor C x).map f)) (U : opens X) : Function.Surjective (f.app (op U)) :=
  by 
    refine' app_surjective_of_injective_of_locally_surjective f (fun x => (h x).1) U fun t x => _ 
    obtain ⟨s₀, hs₀⟩ := (h x).2 (G.1.germ x t)
    obtain ⟨V₁, hxV₁, s₁, hs₁⟩ := F.1.germ_exist x.1 s₀ 
    subst hs₁ 
    rename' hs₀ => hs₁ 
    erw [stalk_functor_map_germ_apply V₁ ⟨x.1, hxV₁⟩ f s₁] at hs₁ 
    obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.1.germ_eq x.1 hxV₁ x.2 _ _ hs₁ 
    use V₂, hxV₂, iV₂U, F.1.map iV₂V₁.op s₁ 
    rw [←comp_apply, f.naturality, comp_apply, HEq]

theorem app_bijective_of_stalk_functor_map_bijective {F G : sheaf C X} (f : F ⟶ G)
  (h : ∀ x : X, Function.Bijective ((stalk_functor C x).map f)) (U : opens X) : Function.Bijective (f.app (op U)) :=
  ⟨app_injective_of_stalk_functor_map_injective f (fun x => (h x).1) U,
    app_surjective_of_stalk_functor_map_bijective f h U⟩

/--
Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then if the stalk maps of a morphism
`f : F ⟶ G` are all isomorphisms, `f` must be an isomorphism.
-/
theorem is_iso_of_stalk_functor_map_iso {F G : sheaf C X} (f : F ⟶ G) [∀ x : X, is_iso ((stalk_functor C x).map f)] :
  is_iso f :=
  by 
    suffices  : is_iso ((sheaf.forget C X).map f)
    ·
      exact is_iso_of_fully_faithful (sheaf.forget C X) f 
    suffices  : ∀ U : «expr ᵒᵖ» (opens X), is_iso (f.app U)
    ·
      exact @nat_iso.is_iso_of_is_iso_app _ _ _ _ F.1 G.1 f this 
    intro U 
    induction U using Opposite.rec 
    suffices  : is_iso ((forget C).map (f.app (op U)))
    ·
      exact is_iso_of_reflects_iso (f.app (op U)) (forget C)
    rw [is_iso_iff_bijective]
    apply app_bijective_of_stalk_functor_map_bijective 
    intro x 
    apply (is_iso_iff_bijective _).mp 
    exact functor.map_is_iso (forget C) ((stalk_functor C x).map f)

/--
Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then a morphism `f : F ⟶ G` is an
isomorphism if and only if all of its stalk maps are isomorphisms.
-/
theorem is_iso_iff_stalk_functor_map_iso {F G : sheaf C X} (f : F ⟶ G) :
  is_iso f ↔ ∀ x : X, is_iso ((stalk_functor C x).map f) :=
  by 
    split 
    ·
      intro h x 
      skip 
      exact @functor.map_is_iso _ _ _ _ _ _ (stalk_functor C x) f ((sheaf.forget C X).map_is_iso f)
    ·
      intro h 
      exact is_iso_of_stalk_functor_map_iso f

end Concrete

end Top.Presheaf

