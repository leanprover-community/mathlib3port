import Mathbin.Topology.Category.Top.Basic 
import Mathbin.CategoryTheory.Limits.Types 
import Mathbin.CategoryTheory.Limits.Preserves.Basic 
import Mathbin.CategoryTheory.Category.Ulift

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/


open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe u v w

noncomputable theory

namespace Top

variable{J : Type u}[small_category J]

local notation "forget" => forget Top

/--
A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone (F : J ⥤ Top.{u}) : cone F :=
  { x := Top.of { u : ∀ j : J, F.obj j | ∀ {i j : J} f : i ⟶ j, F.map f (u i) = u j },
    π :=
      { app :=
          fun j =>
            { toFun := fun u => u.val j,
              continuous_to_fun :=
                show Continuous ((fun u : ∀ j : J, F.obj j => u j) ∘ Subtype.val)by 
                  continuity } } }

/--
A choice of limit cone for a functor `F : J ⥤ Top` whose topology is defined as an
infimum of topologies infimum.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone_infi (F : J ⥤ Top.{u}) : cone F :=
  { x := ⟨(types.limit_cone (F ⋙ forget)).x, ⨅j, (F.obj j).str.induced ((types.limit_cone (F ⋙ forget)).π.app j)⟩,
    π :=
      { app := fun j => ⟨(types.limit_cone (F ⋙ forget)).π.app j, continuous_iff_le_induced.mpr (infi_le _ _)⟩,
        naturality' := fun j j' f => ContinuousMap.coe_inj ((types.limit_cone (F ⋙ forget)).π.naturality f) } }

/--
The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_is_limit (F : J ⥤ Top.{u}) : is_limit (limit_cone F) :=
  { lift :=
      fun S =>
        { toFun :=
            fun x =>
              ⟨fun j => S.π.app _ x,
                fun i j f =>
                  by 
                    dsimp 
                    erw [←S.w f]
                    rfl⟩ },
    uniq' :=
      fun S m h =>
        by 
          ext : 3
          simpa [←h] }

/--
The chosen cone `Top.limit_cone_infi F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_infi_is_limit (F : J ⥤ Top.{u}) : is_limit (limit_cone_infi F) :=
  by 
    refine' is_limit.of_faithful forget (types.limit_cone_is_limit _) (fun s => ⟨_, _⟩) fun s => rfl 
    exact
      continuous_iff_coinduced_le.mpr
        (le_infi$ fun j => coinduced_le_iff_le_induced.mp$ (continuous_iff_coinduced_le.mp (s.π.app j).Continuous : _))

instance Top_has_limits : has_limits.{u} Top.{u} :=
  { HasLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exactI { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        { PreservesLimit :=
            fun F =>
              by 
                exactI
                  preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
                    (types.limit_cone_is_limit (F ⋙ forget)) } }

/--
A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimit_cocone (F : J ⥤ Top.{u}) : cocone F :=
  { x :=
      ⟨(types.colimit_cocone (F ⋙ forget)).x,
        ⨆j, (F.obj j).str.coinduced ((types.colimit_cocone (F ⋙ forget)).ι.app j)⟩,
    ι :=
      { app := fun j => ⟨(types.colimit_cocone (F ⋙ forget)).ι.app j, continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
        naturality' := fun j j' f => ContinuousMap.coe_inj ((types.colimit_cocone (F ⋙ forget)).ι.naturality f) } }

/--
The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimit_cocone_is_colimit (F : J ⥤ Top.{u}) : is_colimit (colimit_cocone F) :=
  by 
    refine' is_colimit.of_faithful forget (types.colimit_cocone_is_colimit _) (fun s => ⟨_, _⟩) fun s => rfl 
    exact
      continuous_iff_le_induced.mpr
        (supr_le$ fun j => coinduced_le_iff_le_induced.mp$ (continuous_iff_coinduced_le.mp (s.ι.app j).Continuous : _))

instance Top_has_colimits : has_colimits.{u} Top.{u} :=
  { HasColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exactI
            { HasColimit :=
                fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_cocone_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
  { PreservesColimitsOfShape :=
      fun J 𝒥 =>
        { PreservesColimit :=
            fun F =>
              by 
                exactI
                  preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
                    (types.colimit_cocone_is_colimit (F ⋙ forget)) } }

end Top

namespace Top

section CofilteredLimit

variable{J : Type u}[small_category J][is_cofiltered J](F : J ⥤ Top.{u})(C : cone F)(hC : is_limit C)

include hC

/--
Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem is_topological_basis_cofiltered_limit (T : ∀ j, Set (Set (F.obj j))) (hT : ∀ j, is_topological_basis (T j))
  (univ : ∀ i : J, Set.Univ ∈ T i) (inter : ∀ i U1 U2 : Set (F.obj i), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
  (compat : ∀ i j : J f : i ⟶ j V : Set (F.obj j) hV : V ∈ T j, F.map f ⁻¹' V ∈ T i) :
  is_topological_basis { U : Set C.X | ∃ (j : _)(V : Set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V } :=
  by 
    classical 
    let D := limit_cone_infi F 
    let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _)
    have hE : Inducing E.hom := (Top.homeoOfIso E).Inducing 
    suffices  : is_topological_basis { U : Set D.X | ∃ (j : _)(V : Set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V }
    ·
      convert this.inducing hE 
      ext U0 
      split 
      ·
        rintro ⟨j, V, hV, rfl⟩
        refine' ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩
      ·
        rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩
        refine' ⟨j, V, hV, rfl⟩
    convert is_topological_basis_infi hT fun j x : D.X => D.π.app j x 
    ext U0 
    split 
    ·
      rintro ⟨j, V, hV, rfl⟩
      let U : ∀ i, Set (F.obj i) :=
        fun i =>
          if h : i = j then
            by 
              rw [h]
              exact V
          else Set.Univ 
      refine' ⟨U, {j}, _, _⟩
      ·
        rintro i h 
        rw [Finset.mem_singleton] at h 
        dsimp [U]
        rw [dif_pos h]
        subst h 
        exact hV
      ·
        dsimp [U]
        simp 
    ·
      rintro ⟨U, G, h1, h2⟩
      obtain ⟨j, hj⟩ := is_cofiltered.inf_objs_exists G 
      let g : ∀ e he : e ∈ G, j ⟶ e := fun _ he => (hj he).some 
      let Vs : J → Set (F.obj j) := fun e => if h : e ∈ G then F.map (g e h) ⁻¹' U e else Set.Univ 
      let V : Set (F.obj j) := ⋂(e : J)(he : e ∈ G), Vs e 
      refine' ⟨j, V, _, _⟩
      ·
        have  :
          ∀ S : Set (Set (F.obj j)) E : Finset J P : J → Set (F.obj j) univ : Set.Univ ∈ S inter :
            ∀ A B : Set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S cond : ∀ e : J he : e ∈ E, P e ∈ S,
            (⋂(e : _)(he : e ∈ E), P e) ∈ S
        ·
          intro S E 
          apply E.induction_on
          ·
            intro P he hh 
            simpa
          ·
            intro a E ha hh1 hh2 hh3 hh4 hh5 
            rw [Finset.set_bInter_insert]
            refine' hh4 _ _ (hh5 _ (Finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _)
            intro e he 
            exact hh5 e (Finset.mem_insert_of_mem he)
        refine' this _ _ _ (univ _) (inter _) _ 
        intro e he 
        dsimp [Vs]
        rw [dif_pos he]
        exact compat j e (g e he) (U e) (h1 e he)
      ·
        rw [h2]
        dsimp [V]
        rw [Set.preimage_Inter]
        congr 1 
        ext1 e 
        rw [Set.preimage_Inter]
        congr 1 
        ext1 he 
        dsimp [Vs]
        rw [dif_pos he, ←Set.preimage_comp]
        congr 1
        change _ = «expr⇑ » (D.π.app j ≫ F.map (g e he))
        rw [D.w]

end CofilteredLimit

section TopologicalKonig

/-!
## Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limit_cone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [directed_order J]` and `F : Jᵒᵖ ⥤ Top`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in `nonempty_sections_of_fintype_cofiltered_system` and
`nonempty_sections_of_fintype_inverse_system`.

(See https://stacks.math.columbia.edu/tag/086J for the Set version.)
-/


variable{J : Type u}[small_category J]

variable(F : J ⥤ Top.{u})

private abbrev finite_diagram_arrow {J : Type u} [small_category J] (G : Finset J) :=
  Σ'(X Y : J)(mX : X ∈ G)(mY : Y ∈ G), X ⟶ Y

private abbrev finite_diagram (J : Type u) [small_category J] :=
  ΣG : Finset J, Finset (finite_diagram_arrow G)

/--
Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
def partial_sections {J : Type u} [small_category J] (F : J ⥤ Top.{u}) {G : Finset J}
  (H : Finset (finite_diagram_arrow G)) : Set (∀ j, F.obj j) :=
  { u | ∀ {f : finite_diagram_arrow G} hf : f ∈ H, F.map f.2.2.2.2 (u f.1) = u f.2.1 }

theorem partial_sections.nonempty [is_cofiltered J] [h : ∀ j : J, Nonempty (F.obj j)] {G : Finset J}
  (H : Finset (finite_diagram_arrow G)) : (partial_sections F H).Nonempty :=
  by 
    classical 
    use
      fun j : J =>
        if hj : j ∈ G then F.map (is_cofiltered.inf_to G H hj) (h (is_cofiltered.inf G H)).some else (h _).some 
    rintro ⟨X, Y, hX, hY, f⟩ hf 
    dsimp only 
    rwa [dif_pos hX, dif_pos hY, ←comp_app, ←F.map_comp, @is_cofiltered.inf_to_commutes _ _ _ G H]

theorem partial_sections.directed : Directed Superset fun G : finite_diagram J => partial_sections F G.2 :=
  by 
    classical 
    intro A B 
    let ιA : finite_diagram_arrow A.1 → finite_diagram_arrow (A.1⊔B.1) :=
      fun f => ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
    let ιB : finite_diagram_arrow B.1 → finite_diagram_arrow (A.1⊔B.1) :=
      fun f => ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1, Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
    refine' ⟨⟨A.1⊔B.1, A.2.Image ιA⊔B.2.Image ιB⟩, _, _⟩
    ·
      rintro u hu f hf 
      have  : ιA f ∈ A.2.Image ιA⊔B.2.Image ιB
      ·
        apply Finset.mem_union_left 
        rw [Finset.mem_image]
        refine' ⟨f, hf, rfl⟩
      exact hu this
    ·
      rintro u hu f hf 
      have  : ιB f ∈ A.2.Image ιA⊔B.2.Image ιB
      ·
        apply Finset.mem_union_right 
        rw [Finset.mem_image]
        refine' ⟨f, hf, rfl⟩
      exact hu this

theorem partial_sections.closed [∀ j : J, T2Space (F.obj j)] {G : Finset J} (H : Finset (finite_diagram_arrow G)) :
  IsClosed (partial_sections F H) :=
  by 
    have  : partial_sections F H = ⋂(f : finite_diagram_arrow G)(hf : f ∈ H), { u | F.map f.2.2.2.2 (u f.1) = u f.2.1 }
    ·
      ext1 
      simp only [Set.mem_Inter, Set.mem_set_of_eq]
      rfl 
    rw [this]
    apply is_closed_bInter 
    intro f hf 
    apply is_closed_eq 
    continuity

/--
Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological spaces.
--/
theorem nonempty_limit_cone_of_compact_t2_cofiltered_system [is_cofiltered J] [∀ j : J, Nonempty (F.obj j)]
  [∀ j : J, CompactSpace (F.obj j)] [∀ j : J, T2Space (F.obj j)] : Nonempty (Top.limitCone F).x :=
  by 
    classical 
    obtain ⟨u, hu⟩ :=
      IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed (fun G => partial_sections F _)
        (partial_sections.directed F) (fun G => partial_sections.nonempty F _)
        (fun G => IsClosed.is_compact (partial_sections.closed F _)) fun G => partial_sections.closed F _ 
    use u 
    intro X Y f 
    let G : finite_diagram J :=
      ⟨{X, Y},
        {⟨X, Y,
            by 
              simp only [true_orₓ, eq_self_iff_true, Finset.mem_insert],
            by 
              simp only [eq_self_iff_true, or_trueₓ, Finset.mem_insert, Finset.mem_singleton],
            f⟩}⟩
    exact hu _ ⟨G, rfl⟩ (Finset.mem_singleton_self _)

end TopologicalKonig

end Top

section FintypeKonig

/-- This bootstraps `nonempty_sections_of_fintype_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `Top.nonempty_limit_cone_of_compact_t2_inverse_system`. -/
theorem NonemptySectionsOfFintypeCofilteredSystem.init {J : Type u} [small_category J] [is_cofiltered J]
  (F : J ⥤ Type u) [hf : ∀ j : J, Fintype (F.obj j)] [hne : ∀ j : J, Nonempty (F.obj j)] : F.sections.nonempty :=
  by 
    let F' : J ⥤ Top := F ⋙ Top.discrete 
    haveI  : ∀ j : J, Fintype (F'.obj j) := hf 
    haveI  : ∀ j : J, Nonempty (F'.obj j) := hne 
    obtain ⟨⟨u, hu⟩⟩ := Top.nonempty_limit_cone_of_compact_t2_cofiltered_system F' 
    exact ⟨u, fun _ _ f => hu f⟩

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_fintype_cofiltered_system {J : Type u} [category.{w} J] [is_cofiltered J] (F : J ⥤ Type v)
  [∀ j : J, Fintype (F.obj j)] [∀ j : J, Nonempty (F.obj j)] : F.sections.nonempty :=
  by 
    let J' : Type max w v u := as_small.{max w v} J 
    let down : J' ⥤ J := as_small.down 
    let F' : J' ⥤ Type max u v w := down ⋙ F ⋙ ulift_functor.{max u w, v}
    haveI  : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
    haveI  : ∀ i, Fintype (F'.obj i) := fun i => Fintype.ofEquiv (F.obj (down.obj i)) equiv.ulift.symm 
    obtain ⟨u, hu⟩ := NonemptySectionsOfFintypeCofilteredSystem.init F' 
    use fun j => (u ⟨j⟩).down 
    intro j j' f 
    have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (Ulift.up f)
    simp only [as_small.down, functor.comp_map, ulift_functor_map, functor.op_map] at h 
    simpRw [←h]
    rfl

/-- The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_cofiltered_system` for a generalization to cofiltered limits.
That version applies in almost all cases, and the only difference is that this version
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
theorem nonempty_sections_of_fintype_inverse_system {J : Type u} [DirectedOrder J] (F : «expr ᵒᵖ» J ⥤ Type v)
  [∀ j : «expr ᵒᵖ» J, Fintype (F.obj j)] [∀ j : «expr ᵒᵖ» J, Nonempty (F.obj j)] : F.sections.nonempty :=
  by 
    runTac 
      tactic.unfreeze_local_instances 
    byCases' h : Nonempty J
    ·
      apply nonempty_sections_of_fintype_cofiltered_system
    ·
      rw [not_nonempty_iff_imp_false] at h 
      exact ⟨fun j => False.elim (h j.unop), fun j => False.elim (h j.unop)⟩

end FintypeKonig

