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
  { x := Top.of { u:∀ j : J, F.obj j | ∀ {i j : J} f : i ⟶ j, F.map f (u i) = u j },
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
          exact { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        { PreservesLimit :=
            fun F =>
              by 
                exact
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
          exact
            { HasColimit :=
                fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_cocone_is_colimit F } } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
  { PreservesColimitsOfShape :=
      fun J 𝒥 =>
        { PreservesColimit :=
            fun F =>
              by 
                exact
                  preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
                    (types.colimit_cocone_is_colimit (F ⋙ forget)) } }

end Top

namespace Top

section CofilteredLimit

variable{J : Type u}[small_category J][is_cofiltered J](F : J ⥤ Top.{u})(C : cone F)(hC : is_limit C)

include hC

-- error in Topology.Category.Top.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem is_topological_basis_cofiltered_limit
(T : ∀ j, set (set (F.obj j)))
(hT : ∀ j, is_topological_basis (T j))
(univ : ∀ i : J, «expr ∈ »(set.univ, T i))
(inter : ∀ (i) (U1 U2 : set (F.obj i)), «expr ∈ »(U1, T i) → «expr ∈ »(U2, T i) → «expr ∈ »(«expr ∩ »(U1, U2), T i))
(compat : ∀
 (i j : J)
 (f : «expr ⟶ »(i, j))
 (V : set (F.obj j))
 (hV : «expr ∈ »(V, T j)), «expr ∈ »(«expr ⁻¹' »(F.map f, V), T i)) : is_topological_basis {U : set C.X | «expr∃ , »((j)
 (V : set (F.obj j)), «expr ∧ »(«expr ∈ »(V, T j), «expr = »(U, «expr ⁻¹' »(C.π.app j, V))))} :=
begin
  classical,
  let [ident D] [] [":=", expr limit_cone_infi F],
  let [ident E] [":", expr «expr ≅ »(C.X, D.X)] [":=", expr hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _)],
  have [ident hE] [":", expr inducing E.hom] [":=", expr (Top.homeo_of_iso E).inducing],
  suffices [] [":", expr is_topological_basis {U : set D.X | «expr∃ , »((j)
    (V : set (F.obj j)), «expr ∧ »(«expr ∈ »(V, T j), «expr = »(U, «expr ⁻¹' »(D.π.app j, V))))}],
  { convert [] [expr this.inducing hE] [],
    ext [] [ident U0] [],
    split,
    { rintro ["⟨", ident j, ",", ident V, ",", ident hV, ",", ident rfl, "⟩"],
      refine [expr ⟨«expr ⁻¹' »(D.π.app j, V), ⟨j, V, hV, rfl⟩, rfl⟩] },
    { rintro ["⟨", ident W, ",", "⟨", ident j, ",", ident V, ",", ident hV, ",", ident rfl, "⟩", ",", ident rfl, "⟩"],
      refine [expr ⟨j, V, hV, rfl⟩] } },
  convert [] [expr is_topological_basis_infi hT (λ (j) (x : D.X), D.π.app j x)] [],
  ext [] [ident U0] [],
  split,
  { rintros ["⟨", ident j, ",", ident V, ",", ident hV, ",", ident rfl, "⟩"],
    let [ident U] [":", expr ∀
     i, set (F.obj i)] [":=", expr λ i, if h : «expr = »(i, j) then by { rw [expr h] [],
       exact [expr V] } else set.univ],
    refine [expr ⟨U, {j}, _, _⟩],
    { rintro [ident i, ident h],
      rw [expr finset.mem_singleton] ["at", ident h],
      dsimp [] ["[", expr U, "]"] [] [],
      rw [expr dif_pos h] [],
      subst [expr h],
      exact [expr hV] },
    { dsimp [] ["[", expr U, "]"] [] [],
      simp [] [] [] [] [] [] } },
  { rintros ["⟨", ident U, ",", ident G, ",", ident h1, ",", ident h2, "⟩"],
    obtain ["⟨", ident j, ",", ident hj, "⟩", ":=", expr is_cofiltered.inf_objs_exists G],
    let [ident g] [":", expr ∀ (e) (he : «expr ∈ »(e, G)), «expr ⟶ »(j, e)] [":=", expr λ _ he, (hj he).some],
    let [ident Vs] [":", expr J → set (F.obj j)] [":=", expr λ
     e, if h : «expr ∈ »(e, G) then «expr ⁻¹' »(F.map (g e h), U e) else set.univ],
    let [ident V] [":", expr set (F.obj j)] [":=", expr «expr⋂ , »((e : J) (he : «expr ∈ »(e, G)), Vs e)],
    refine [expr ⟨j, V, _, _⟩],
    { have [] [":", expr ∀
       (S : set (set (F.obj j)))
       (E : finset J)
       (P : J → set (F.obj j))
       (univ : «expr ∈ »(set.univ, S))
       (inter : ∀ A B : set (F.obj j), «expr ∈ »(A, S) → «expr ∈ »(B, S) → «expr ∈ »(«expr ∩ »(A, B), S))
       (cond : ∀
        (e : J)
        (he : «expr ∈ »(e, E)), «expr ∈ »(P e, S)), «expr ∈ »(«expr⋂ , »((e) (he : «expr ∈ »(e, E)), P e), S)] [],
      { intros [ident S, ident E],
        apply [expr E.induction_on],
        { intros [ident P, ident he, ident hh],
          simpa [] [] [] [] [] [] },
        { intros [ident a, ident E, ident ha, ident hh1, ident hh2, ident hh3, ident hh4, ident hh5],
          rw [expr finset.set_bInter_insert] [],
          refine [expr hh4 _ _ (hh5 _ (finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _)],
          intros [ident e, ident he],
          exact [expr hh5 e (finset.mem_insert_of_mem he)] } },
      refine [expr this _ _ _ (univ _) (inter _) _],
      intros [ident e, ident he],
      dsimp [] ["[", expr Vs, "]"] [] [],
      rw [expr dif_pos he] [],
      exact [expr compat j e (g e he) (U e) (h1 e he)] },
    { rw [expr h2] [],
      dsimp [] ["[", expr V, "]"] [] [],
      rw [expr set.preimage_Inter] [],
      congr' [1] [],
      ext1 [] [ident e],
      rw [expr set.preimage_Inter] [],
      congr' [1] [],
      ext1 [] [ident he],
      dsimp [] ["[", expr Vs, "]"] [] [],
      rw ["[", expr dif_pos he, ",", "<-", expr set.preimage_comp, "]"] [],
      congr' [1] [],
      change [expr «expr = »(_, «expr⇑ »(«expr ≫ »(D.π.app j, F.map (g e he))))] [] [],
      rw [expr D.w] [] } }
end

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

-- error in Topology.Category.Top.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem partial_sections.directed : directed superset (λ G : finite_diagram J, partial_sections F G.2) :=
begin
  classical,
  intros [ident A, ident B],
  let [ident ιA] [":", expr finite_diagram_arrow A.1 → finite_diagram_arrow «expr ⊔ »(A.1, B.1)] [":=", expr λ
   f, ⟨f.1, f.2.1, finset.mem_union_left _ f.2.2.1, finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩],
  let [ident ιB] [":", expr finite_diagram_arrow B.1 → finite_diagram_arrow «expr ⊔ »(A.1, B.1)] [":=", expr λ
   f, ⟨f.1, f.2.1, finset.mem_union_right _ f.2.2.1, finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩],
  refine [expr ⟨⟨«expr ⊔ »(A.1, B.1), «expr ⊔ »(A.2.image ιA, B.2.image ιB)⟩, _, _⟩],
  { rintro [ident u, ident hu, ident f, ident hf],
    have [] [":", expr «expr ∈ »(ιA f, «expr ⊔ »(A.2.image ιA, B.2.image ιB))] [],
    { apply [expr finset.mem_union_left],
      rw [expr finset.mem_image] [],
      refine [expr ⟨f, hf, rfl⟩] },
    exact [expr hu this] },
  { rintro [ident u, ident hu, ident f, ident hf],
    have [] [":", expr «expr ∈ »(ιB f, «expr ⊔ »(A.2.image ιA, B.2.image ιB))] [],
    { apply [expr finset.mem_union_right],
      rw [expr finset.mem_image] [],
      refine [expr ⟨f, hf, rfl⟩] },
    exact [expr hu this] }
end

-- error in Topology.Category.Top.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem partial_sections.closed
[∀ j : J, t2_space (F.obj j)]
{G : finset J}
(H : finset (finite_diagram_arrow G)) : is_closed (partial_sections F H) :=
begin
  have [] [":", expr «expr = »(partial_sections F H, «expr⋂ , »({f : finite_diagram_arrow G}
     (hf : «expr ∈ »(f, H)), {u | «expr = »(F.map f.2.2.2.2 (u f.1), u f.2.1)}))] [],
  { ext1 [] [],
    simp [] [] ["only"] ["[", expr set.mem_Inter, ",", expr set.mem_set_of_eq, "]"] [] [],
    refl },
  rw [expr this] [],
  apply [expr is_closed_bInter],
  intros [ident f, ident hf],
  apply [expr is_closed_eq],
  continuity [] []
end

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

-- error in Topology.Category.Top.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This bootstraps `nonempty_sections_of_fintype_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `Top.nonempty_limit_cone_of_compact_t2_inverse_system`. -/
theorem nonempty_sections_of_fintype_cofiltered_system.init
{J : Type u}
[small_category J]
[is_cofiltered J]
(F : «expr ⥤ »(J, Type u))
[hf : ∀ j : J, fintype (F.obj j)]
[hne : ∀ j : J, nonempty (F.obj j)] : F.sections.nonempty :=
begin
  let [ident F'] [":", expr «expr ⥤ »(J, Top)] [":=", expr «expr ⋙ »(F, Top.discrete)],
  haveI [] [":", expr ∀ j : J, fintype (F'.obj j)] [":=", expr hf],
  haveI [] [":", expr ∀ j : J, nonempty (F'.obj j)] [":=", expr hne],
  obtain ["⟨", "⟨", ident u, ",", ident hu, "⟩", "⟩", ":=", expr Top.nonempty_limit_cone_of_compact_t2_cofiltered_system F'],
  exact [expr ⟨u, λ _ _ f, hu f⟩]
end

-- error in Topology.Category.Top.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_fintype_cofiltered_system
{J : Type u}
[category.{w} J]
[is_cofiltered J]
(F : «expr ⥤ »(J, Type v))
[∀ j : J, fintype (F.obj j)]
[∀ j : J, nonempty (F.obj j)] : F.sections.nonempty :=
begin
  let [ident J'] [":", expr Type max w v u] [":=", expr as_small.{max w v} J],
  let [ident down] [":", expr «expr ⥤ »(J', J)] [":=", expr as_small.down],
  let [ident F'] [":", expr «expr ⥤ »(J', Type max u v w)] [":=", expr «expr ⋙ »(down, «expr ⋙ »(F, ulift_functor.{max u w, v}))],
  haveI [] [":", expr ∀ i, nonempty (F'.obj i)] [":=", expr λ i, ⟨⟨classical.arbitrary (F.obj (down.obj i))⟩⟩],
  haveI [] [":", expr ∀ i, fintype (F'.obj i)] [":=", expr λ i, fintype.of_equiv (F.obj (down.obj i)) equiv.ulift.symm],
  obtain ["⟨", ident u, ",", ident hu, "⟩", ":=", expr nonempty_sections_of_fintype_cofiltered_system.init F'],
  use [expr λ j, (u ⟨j⟩).down],
  intros [ident j, ident j', ident f],
  have [ident h] [] [":=", expr @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ulift.up f)],
  simp [] [] ["only"] ["[", expr as_small.down, ",", expr functor.comp_map, ",", expr ulift_functor_map, ",", expr functor.op_map, "]"] [] ["at", ident h],
  simp_rw ["[", "<-", expr h, "]"] [],
  refl
end

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

