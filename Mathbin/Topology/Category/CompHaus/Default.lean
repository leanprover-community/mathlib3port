import Mathbin.CategoryTheory.Adjunction.Reflective 
import Mathbin.Topology.Category.Top.Default 
import Mathbin.Topology.StoneCech 
import Mathbin.CategoryTheory.Monad.Limits 
import Mathbin.Topology.UrysohnsLemma

/-!

# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `Top`.
The fully faithful functor `CompHaus ⥤ Top` is denoted `CompHaus_to_Top`.

**Note:** The file `topology/category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`Compactum_to_CompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `Compactum_to_CompHaus.is_equivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/


universe u

open CategoryTheory

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus where 
  toTop : Top
  [IsCompact : CompactSpace to_Top]
  [is_hausdorff : T2Space to_Top]

namespace CompHaus

instance : Inhabited CompHaus :=
  ⟨{ toTop := { α := Pempty } }⟩

instance : CoeSort CompHaus (Type _) :=
  ⟨fun X => X.to_Top⟩

instance {X : CompHaus} : CompactSpace X :=
  X.is_compact

instance {X : CompHaus} : T2Space X :=
  X.is_hausdorff

instance category : category CompHaus :=
  induced_category.category to_Top

instance concrete_category : concrete_category CompHaus :=
  induced_category.concrete_category _

@[simp]
theorem coe_to_Top {X : CompHaus} : (X.to_Top : Type _) = X :=
  rfl

variable (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHaus :=
  { toTop := Top.of X, IsCompact := ‹_›, is_hausdorff := ‹_› }

@[simp]
theorem coe_of : (CompHaus.of X : Type _) = X :=
  rfl

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
theorem IsClosedMap {X Y : CompHaus.{u}} (f : X ⟶ Y) : IsClosedMap f :=
  fun C hC => (hC.is_compact.image f.continuous).IsClosed

-- error in Topology.Category.CompHaus.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
theorem is_iso_of_bijective {X Y : CompHaus.{u}} (f : «expr ⟶ »(X, Y)) (bij : function.bijective f) : is_iso f :=
begin
  let [ident E] [] [":=", expr equiv.of_bijective _ bij],
  have [ident hE] [":", expr continuous E.symm] [],
  { rw [expr continuous_iff_is_closed] [],
    intros [ident S, ident hS],
    rw ["<-", expr E.image_eq_preimage] [],
    exact [expr is_closed_map f S hS] },
  refine [expr ⟨⟨⟨E.symm, hE⟩, _, _⟩⟩],
  { ext [] [ident x] [],
    apply [expr E.symm_apply_apply] },
  { ext [] [ident x] [],
    apply [expr E.apply_symm_apply] }
end

-- error in Topology.Category.CompHaus.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable
def iso_of_bijective {X Y : CompHaus.{u}} (f : «expr ⟶ »(X, Y)) (bij : function.bijective f) : «expr ≅ »(X, Y) :=
by letI [] [] [":=", expr is_iso_of_bijective _ bij]; exact [expr as_iso f]

end CompHaus

-- error in Topology.Category.CompHaus.Default: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler full
/-- The fully faithful embedding of `CompHaus` in `Top`. -/
@[simps #[expr { rhs_md := semireducible }], derive #["[", expr full, ",", expr faithful, "]"]]
def CompHaus_to_Top : «expr ⥤ »(CompHaus.{u}, Top.{u}) :=
induced_functor _

instance CompHaus.forget_reflects_isomorphisms : reflects_isomorphisms (forget CompHaus.{u}) :=
  ⟨by 
      intros A B f hf <;> exact CompHaus.is_iso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩

/--
(Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps]
def stoneCechObj (X : Top) : CompHaus :=
  CompHaus.of (StoneCech X)

/--
(Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stoneCechEquivalence (X : Top.{u}) (Y : CompHaus.{u}) :
  (stoneCechObj X ⟶ Y) ≃ X ⟶ compHausToTop.obj Y :=
  { toFun := fun f => { toFun := f ∘ stoneCechUnit, continuous_to_fun := f.2.comp (@continuous_stone_cech_unit X _) },
    invFun := fun f => { toFun := stoneCechExtend f.2, continuous_to_fun := continuous_stone_cech_extend f.2 },
    left_inv :=
      by 
        rintro ⟨f : StoneCech X ⟶ Y, hf : Continuous f⟩
        ext (x : StoneCech X)
        refine' congr_funₓ _ x 
        apply Continuous.ext_on dense_range_stone_cech_unit (continuous_stone_cech_extend _) hf 
        rintro _ ⟨y, rfl⟩
        apply congr_funₓ (stone_cech_extend_extends (hf.comp _)) y,
    right_inv :=
      by 
        rintro ⟨f : (X : Type _) ⟶ Y, hf : Continuous f⟩
        ext 
        exact congr_funₓ (stone_cech_extend_extends hf) x }

/--
The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def topToCompHaus : Top.{u} ⥤ CompHaus.{u} :=
  adjunction.left_adjoint_of_equiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl

theorem Top_to_CompHaus_obj (X : Top) : «expr↥ » (topToCompHaus.obj X) = StoneCech X :=
  rfl

/--
The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
noncomputable instance compHausToTop.reflective : reflective compHausToTop :=
  { toIsRightAdjoint := ⟨topToCompHaus, adjunction.adjunction_of_equiv_left _ _⟩ }

noncomputable instance compHausToTop.createsLimits : creates_limits compHausToTop :=
  monadic_creates_limits _

instance CompHaus.has_limits : limits.has_limits CompHaus :=
  has_limits_of_has_limits_creates_limits compHausToTop

instance CompHaus.has_colimits : limits.has_colimits CompHaus :=
  has_colimits_of_reflective compHausToTop

namespace CompHaus

-- error in Topology.Category.CompHaus.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of
`Top.limit_cone`. -/ def limit_cone {J : Type u} [small_category J] (F : «expr ⥤ »(J, CompHaus.{u})) : limits.cone F :=
{ X := { to_Top := (Top.limit_cone «expr ⋙ »(F, CompHaus_to_Top)).X,
    is_compact := begin
      show [expr compact_space «expr↥ »({u : ∀
        j, F.obj j | ∀ {i j : J} (f : «expr ⟶ »(i, j)), «expr = »(F.map f (u i), u j)})],
      rw ["<-", expr is_compact_iff_compact_space] [],
      apply [expr is_closed.is_compact],
      have [] [":", expr «expr = »({u : ∀
        j, F.obj j | ∀
        {i j : J}
        (f : «expr ⟶ »(i, j)), «expr = »(F.map f (u i), u j)}, «expr⋂ , »((i j : J)
         (f : «expr ⟶ »(i, j)), {u | «expr = »(F.map f (u i), u j)}))] [],
      { ext1 [] [],
        simp [] [] ["only"] ["[", expr set.mem_Inter, ",", expr set.mem_set_of_eq, "]"] [] [] },
      rw [expr this] [],
      apply [expr is_closed_Inter],
      intros [ident i],
      apply [expr is_closed_Inter],
      intros [ident j],
      apply [expr is_closed_Inter],
      intros [ident f],
      apply [expr is_closed_eq],
      { exact [expr (continuous_map.continuous (F.map f)).comp (continuous_apply i)] },
      { exact [expr continuous_apply j] }
    end,
    is_hausdorff := show t2_space «expr↥ »({u : ∀
     j, F.obj j | ∀ {i j : J} (f : «expr ⟶ »(i, j)), «expr = »(F.map f (u i), u j)}), from infer_instance },
  π := { app := λ j, (Top.limit_cone «expr ⋙ »(F, CompHaus_to_Top)).π.app j,
    naturality' := by { intros ["_", "_", "_"],
      ext [] ["⟨", ident x, ",", ident hx, "⟩"] [],
      simp [] [] ["only"] ["[", expr comp_apply, ",", expr functor.const.obj_map, ",", expr id_apply, "]"] [] [],
      exact [expr (hx f).symm] } } }

/-- The limit cone `CompHaus.limit_cone F` is indeed a limit cone. -/
def limit_cone_is_limit {J : Type u} [small_category J] (F : J ⥤ CompHaus.{u}) : limits.is_limit (limit_cone F) :=
  { lift := fun S => (Top.limitConeIsLimit (F ⋙ compHausToTop)).lift (compHausToTop.mapCone S),
    uniq' := fun S m h => (Top.limitConeIsLimit _).uniq (compHausToTop.mapCone S) _ h }

-- error in Topology.Category.CompHaus.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem epi_iff_surjective {X Y : CompHaus.{u}} (f : «expr ⟶ »(X, Y)) : «expr ↔ »(epi f, function.surjective f) :=
begin
  split,
  { contrapose ["!"] [],
    rintros ["⟨", ident y, ",", ident hy, "⟩", ident hf],
    let [ident C] [] [":=", expr set.range f],
    have [ident hC] [":", expr is_closed C] [":=", expr (is_compact_range f.continuous).is_closed],
    let [ident D] [] [":=", expr {y}],
    have [ident hD] [":", expr is_closed D] [":=", expr is_closed_singleton],
    have [ident hCD] [":", expr disjoint C D] [],
    { rw [expr set.disjoint_singleton_right] [],
      rintro ["⟨", ident y', ",", ident hy', "⟩"],
      exact [expr hy y' hy'] },
    haveI [] [":", expr normal_space «expr↥ »(Y.to_Top)] [":=", expr normal_of_compact_t2],
    obtain ["⟨", ident φ, ",", ident hφ0, ",", ident hφ1, ",", ident hφ01, "⟩", ":=", expr exists_continuous_zero_one_of_closed hC hD hCD],
    haveI [] [":", expr compact_space «expr $ »(ulift.{u}, set.Icc (0 : exprℝ()) 1)] [":=", expr homeomorph.ulift.symm.compact_space],
    haveI [] [":", expr t2_space «expr $ »(ulift.{u}, set.Icc (0 : exprℝ()) 1)] [":=", expr homeomorph.ulift.symm.t2_space],
    let [ident Z] [] [":=", expr of «expr $ »(ulift.{u}, set.Icc (0 : exprℝ()) 1)],
    let [ident g] [":", expr «expr ⟶ »(Y, Z)] [":=", expr ⟨λ
      y', ⟨⟨φ y', hφ01 y'⟩⟩, continuous_ulift_up.comp (continuous_subtype_mk (λ y', hφ01 y') φ.continuous)⟩],
    let [ident h] [":", expr «expr ⟶ »(Y, Z)] [":=", expr ⟨λ
      _, ⟨⟨0, set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩],
    have [ident H] [":", expr «expr = »(h, g)] [],
    { rw ["<-", expr cancel_epi f] [],
      ext [] [ident x] [],
      dsimp [] [] [] [],
      simp [] [] ["only"] ["[", expr comp_apply, ",", expr continuous_map.coe_mk, ",", expr subtype.coe_mk, ",", expr hφ0 (set.mem_range_self x), ",", expr pi.zero_apply, "]"] [] [] },
    apply_fun [expr λ e, (e y).down] ["at", ident H] [],
    dsimp [] [] [] ["at", ident H],
    simp [] [] ["only"] ["[", expr subtype.mk_eq_mk, ",", expr hφ1 (set.mem_singleton y), ",", expr pi.one_apply, "]"] [] ["at", ident H],
    exact [expr zero_ne_one H] },
  { rw ["<-", expr category_theory.epi_iff_surjective] [],
    apply [expr faithful_reflects_epi (forget CompHaus)] }
end

-- error in Topology.Category.CompHaus.Default: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mono_iff_injective {X Y : CompHaus.{u}} (f : «expr ⟶ »(X, Y)) : «expr ↔ »(mono f, function.injective f) :=
begin
  split,
  { introsI [ident hf, ident x₁, ident x₂, ident h],
    let [ident g₁] [":", expr «expr ⟶ »(of punit, X)] [":=", expr ⟨λ _, x₁, continuous_of_discrete_topology⟩],
    let [ident g₂] [":", expr «expr ⟶ »(of punit, X)] [":=", expr ⟨λ _, x₂, continuous_of_discrete_topology⟩],
    have [] [":", expr «expr = »(«expr ≫ »(g₁, f), «expr ≫ »(g₂, f))] [],
    by { ext [] [] [],
      exact [expr h] },
    rw [expr cancel_mono] ["at", ident this],
    apply_fun [expr λ e, e punit.star] ["at", ident this] [],
    exact [expr this] },
  { rw ["<-", expr category_theory.mono_iff_injective] [],
    apply [expr faithful_reflects_mono (forget CompHaus)] }
end

end CompHaus

