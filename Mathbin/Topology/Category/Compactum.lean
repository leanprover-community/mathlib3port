import Mathbin.CategoryTheory.Monad.Types 
import Mathbin.CategoryTheory.Monad.Limits 
import Mathbin.CategoryTheory.Equivalence 
import Mathbin.Topology.Category.CompHaus.Default 
import Mathbin.Data.Set.Constructions

/-!

# Compacta and Compact Hausdorff Spaces

Recall that, given a monad `M` on `Type*`, an *algebra* for `M` consists of the following data:
- A type `X : Type*`
- A "structure" map `M X → X`.
This data must also satisfy a distributivity and unit axiom, and algebras for `M` form a category
in an evident way.

See the file `category_theory.monad.algebra` for a general version, as well as the following link.
https://ncatlab.org/nlab/show/monad

This file proves the equivalence between the category of *compact Hausdorff topological spaces*
and the category of algebras for the *ultrafilter monad*.

## Notation:

Here are the main objects introduced in this file.
- `Compactum` is the type of compacta, which we define as algebras for the ultrafilter monad.
- `Compactum_to_CompHaus` is the functor `Compactum ⥤ CompHaus`. Here `CompHaus` is the usual
  category of compact Hausdorff spaces.
- `Compactum_to_CompHaus.is_equivalence` is a term of type `is_equivalence Compactum_to_CompHaus`.

The proof of this equivalence is a bit technical. But the idea is quite simply that the structure
map `ultrafilter X → X` for an algebra `X` of the ultrafilter monad should be considered as the map
sending an ultrafilter to its limit in `X`. The topology on `X` is then defined by mimicking the
characterization of open sets in terms of ultrafilters.

Any `X : Compactum` is endowed with a coercion to `Type*`, as well as the following instances:
- `topological_space X`.
- `compact_space X`.
- `t2_space X`.

Any morphism `f : X ⟶ Y` of is endowed with a coercion to a function `X → Y`, which is shown to
be continuous in `continuous_of_hom`.

The function `Compactum.of_topological_space` can be used to construct a `Compactum` from a
topological space which satisfies `compact_space` and `t2_space`.

We also add wrappers around structures which already exist. Here are the main ones, all in the
`Compactum` namespace:

- `forget : Compactum ⥤ Type*` is the forgetful functor, which induces a `concrete_category`
  instance for `Compactum`.
- `free : Type* ⥤ Compactum` is the left adjoint to `forget`, and the adjunction is in `adj`.
- `str : ultrafilter X → X` is the structure map for `X : Compactum`.
  The notation `X.str` is preferred.
- `join : ultrafilter (ultrafilter X) → ultrafilter X` is the monadic join for `X : Compactum`.
  Again, the notation `X.join` is preferred.
- `incl : X → ultrafilter X` is the unit for `X : Compactum`. The notation `X.incl` is preferred.

## References

- E. Manes, Algebraic Theories, Graduate Texts in Mathematics 26, Springer-Verlag, 1976.
- https://ncatlab.org/nlab/show/ultrafilter

-/


universe u

open CategoryTheory Filter Ultrafilter TopologicalSpace CategoryTheory.Limits HasFiniteInter

open_locale Classical TopologicalSpace

local notation "β" => of_type_monad Ultrafilter

-- error in Topology.Category.Compactum: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- The type `Compactum` of Compacta, defined as algebras for the ultrafilter monad. -/
@[derive #["[", expr category, ",", expr inhabited, "]"]]
def Compactum :=
monad.algebra exprβ()

namespace Compactum

-- error in Topology.Category.Compactum: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler creates_limits
/-- The forgetful functor to Type* -/
@[derive #["[", expr creates_limits, ",", expr faithful, "]"]]
def forget : «expr ⥤ »(Compactum, Type*) :=
monad.forget _

/-- The "free" Compactum functor. -/
def free : Type _ ⥤ Compactum :=
  monad.free _

/-- The adjunction between `free` and `forget`. -/
def adj : free ⊣ forget :=
  monad.adj _

instance  : concrete_category Compactum :=
  { forget := forget }

instance  : CoeSort Compactum (Type _) :=
  ⟨forget.obj⟩

instance  {X Y : Compactum} : CoeFun (X ⟶ Y) fun f => X → Y :=
  ⟨fun f => f.f⟩

instance  : has_limits Compactum :=
  has_limits_of_has_limits_creates_limits forget

/-- The structure map for a compactum, essentially sending an ultrafilter to its limit. -/
def str (X : Compactum) : Ultrafilter X → X :=
  X.a

/-- The monadic join. -/
def join (X : Compactum) : Ultrafilter (Ultrafilter X) → Ultrafilter X :=
  β.μ.app _

/-- The inclusion of `X` into `ultrafilter X`. -/
def incl (X : Compactum) : X → Ultrafilter X :=
  β.η.app _

@[simp]
theorem str_incl (X : Compactum) (x : X) : X.str (X.incl x) = x :=
  by 
    change (β.η.app _ ≫ X.a) _ = _ 
    rw [monad.algebra.unit]
    rfl

@[simp]
theorem str_hom_commute (X Y : Compactum) (f : X ⟶ Y) (xs : Ultrafilter X) : f (X.str xs) = Y.str (map f xs) :=
  by 
    change (X.a ≫ f.f) _ = _ 
    rw [←f.h]
    rfl

@[simp]
theorem join_distrib (X : Compactum) (uux : Ultrafilter (Ultrafilter X)) : X.str (X.join uux) = X.str (map X.str uux) :=
  by 
    change (β.μ.app _ ≫ X.a) _ = _ 
    rw [monad.algebra.assoc]
    rfl

instance  {X : Compactum} : TopologicalSpace X :=
  { IsOpen := fun U => ∀ (F : Ultrafilter X), X.str F ∈ U → U ∈ F, is_open_univ := fun _ _ => Filter.univ_sets _,
    is_open_inter := fun S T h3 h4 h5 h6 => Filter.inter_sets _ (h3 _ h6.1) (h4 _ h6.2),
    is_open_sUnion := fun S h1 F ⟨T, hT, h2⟩ => mem_of_superset (h1 T hT _ h2) (Set.subset_sUnion_of_mem hT) }

theorem is_closed_iff {X : Compactum} (S : Set X) : IsClosed S ↔ ∀ (F : Ultrafilter X), S ∈ F → X.str F ∈ S :=
  by 
    rw [←is_open_compl_iff]
    split 
    ·
      intro cond F h 
      byContra c 
      specialize cond F c 
      rw [compl_mem_iff_not_mem] at cond 
      contradiction
    ·
      intro h1 F h2 
      specialize h1 F 
      cases F.mem_or_compl_mem S <;> finish

instance  {X : Compactum} : CompactSpace X :=
  by 
    constructor 
    rw [is_compact_iff_ultrafilter_le_nhds]
    intro F h 
    refine'
      ⟨X.str F,
        by 
          tauto,
        _⟩
    rw [le_nhds_iff]
    intro S h1 h2 
    exact h2 F h1

/-- A local definition used only in the proofs. -/
private def basic {X : Compactum} (A : Set X) : Set (Ultrafilter X) :=
  { F | A ∈ F }

/-- A local definition used only in the proofs. -/
private def cl {X : Compactum} (A : Set X) : Set X :=
  X.str '' basic A

private theorem basic_inter {X : Compactum} (A B : Set X) : basic (A ∩ B) = basic A ∩ basic B :=
  by 
    ext G 
    split 
    ·
      intro hG 
      split  <;> filterUpwards [hG] <;> intro x 
      exacts[And.left, And.right]
    ·
      rintro ⟨h1, h2⟩
      exact inter_mem h1 h2

private theorem subset_cl {X : Compactum} (A : Set X) : A ⊆ cl A :=
  fun a ha =>
    ⟨X.incl a, ha,
      by 
        simp ⟩

-- error in Topology.Category.Compactum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private theorem cl_cl {X : Compactum} (A : set X) : «expr ⊆ »(cl (cl A), cl A) :=
begin
  rintros ["_", "⟨", ident F, ",", ident hF, ",", ident rfl, "⟩"],
  let [ident fsu] [] [":=", expr finset (set (ultrafilter X))],
  let [ident ssu] [] [":=", expr set (set (ultrafilter X))],
  let [ident ι] [":", expr fsu → ssu] [":=", expr coe],
  let [ident C0] [":", expr ssu] [":=", expr {Z | «expr∃ , »((B «expr ∈ » F), «expr = »(«expr ⁻¹' »(X.str, B), Z))}],
  let [ident AA] [] [":=", expr {G : ultrafilter X | «expr ∈ »(A, G)}],
  let [ident C1] [] [":=", expr insert AA C0],
  let [ident C2] [] [":=", expr finite_inter_closure C1],
  have [ident claim1] [":", expr ∀ B C «expr ∈ » C0, «expr ∈ »(«expr ∩ »(B, C), C0)] [],
  { rintros [ident B, ident C, "⟨", ident Q, ",", ident hQ, ",", ident rfl, "⟩", "⟨", ident R, ",", ident hR, ",", ident rfl, "⟩"],
    use [expr «expr ∩ »(Q, R)],
    simp [] [] ["only"] ["[", expr and_true, ",", expr eq_self_iff_true, ",", expr set.preimage_inter, ",", expr subtype.val_eq_coe, "]"] [] [],
    exact [expr inter_sets _ hQ hR] },
  have [ident claim2] [":", expr ∀ B «expr ∈ » C0, set.nonempty B] [],
  { rintros [ident B, "⟨", ident Q, ",", ident hQ, ",", ident rfl, "⟩"],
    obtain ["⟨", ident q, "⟩", ":=", expr filter.nonempty_of_mem hQ],
    use [expr X.incl q],
    simpa [] [] [] [] [] [] },
  have [ident claim3] [":", expr ∀ B «expr ∈ » C0, «expr ∩ »(AA, B).nonempty] [],
  { rintros [ident B, "⟨", ident Q, ",", ident hQ, ",", ident rfl, "⟩"],
    have [] [":", expr «expr ∩ »(Q, cl A).nonempty] [":=", expr filter.nonempty_of_mem (inter_mem hQ hF)],
    rcases [expr this, "with", "⟨", ident q, ",", ident hq1, ",", ident P, ",", ident hq2, ",", ident hq3, "⟩"],
    refine [expr ⟨P, hq2, _⟩],
    rw ["<-", expr hq3] ["at", ident hq1],
    simpa [] [] [] [] [] [] },
  suffices [] [":", expr ∀ T : fsu, «expr ⊆ »(ι T, C1) → «expr⋂₀ »(ι T).nonempty],
  { obtain ["⟨", ident G, ",", ident h1, "⟩", ":=", expr exists_ultrafilter_of_finite_inter_nonempty _ this],
    use [expr X.join G],
    have [] [":", expr «expr = »(G.map X.str, F)] [":=", expr ultrafilter.coe_le_coe.1 (λ
      S hS, h1 (or.inr ⟨S, hS, rfl⟩))],
    rw ["[", expr join_distrib, ",", expr this, "]"] [],
    exact [expr ⟨h1 (or.inl rfl), rfl⟩] },
  have [ident claim4] [] [":=", expr finite_inter_closure_has_finite_inter C1],
  have [ident claim5] [":", expr has_finite_inter C0] [":=", expr ⟨⟨_, univ_mem, set.preimage_univ⟩, claim1⟩],
  have [ident claim6] [":", expr ∀ P «expr ∈ » C2, (P : set (ultrafilter X)).nonempty] [],
  { suffices [] [":", expr ∀
     P «expr ∈ » C2, «expr ∨ »(«expr ∈ »(P, C0), «expr∃ , »((Q «expr ∈ » C0), «expr = »(P, «expr ∩ »(AA, Q))))],
    { intros [ident P, ident hP],
      cases [expr this P hP] [],
      { exact [expr claim2 _ h] },
      { rcases [expr h, "with", "⟨", ident Q, ",", ident hQ, ",", ident rfl, "⟩"],
        exact [expr claim3 _ hQ] } },
    intros [ident P, ident hP],
    exact [expr claim5.finite_inter_closure_insert _ hP] },
  intros [ident T, ident hT],
  suffices [] [":", expr «expr ∈ »(«expr⋂₀ »(ι T), C2)],
  by exact [expr claim6 _ this],
  apply [expr claim4.finite_inter_mem],
  intros [ident t, ident ht],
  exact [expr finite_inter_closure.basic (@hT t ht)]
end

theorem is_closed_cl {X : Compactum} (A : Set X) : IsClosed (cl A) :=
  by 
    rw [is_closed_iff]
    intro F hF 
    exact cl_cl _ ⟨F, hF, rfl⟩

-- error in Topology.Category.Compactum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem str_eq_of_le_nhds
{X : Compactum}
(F : ultrafilter X)
(x : X) : «expr ≤ »(«expr↑ »(F), expr𝓝() x) → «expr = »(X.str F, x) :=
begin
  let [ident fsu] [] [":=", expr finset (set (ultrafilter X))],
  let [ident ssu] [] [":=", expr set (set (ultrafilter X))],
  let [ident ι] [":", expr fsu → ssu] [":=", expr coe],
  let [ident T0] [":", expr ssu] [":=", expr {S | «expr∃ , »((A «expr ∈ » F), «expr = »(S, basic A))}],
  let [ident AA] [] [":=", expr «expr ⁻¹' »(X.str, {x})],
  let [ident T1] [] [":=", expr insert AA T0],
  let [ident T2] [] [":=", expr finite_inter_closure T1],
  intro [ident cond],
  have [ident claim1] [":", expr ∀ A : set X, is_closed A → «expr ∈ »(A, F) → «expr ∈ »(x, A)] [],
  { intros [ident A, ident hA, ident h],
    by_contradiction [ident H],
    rw [expr le_nhds_iff] ["at", ident cond],
    specialize [expr cond «expr ᶜ»(A) H hA.is_open_compl],
    rw ["[", expr ultrafilter.mem_coe, ",", expr ultrafilter.compl_mem_iff_not_mem, "]"] ["at", ident cond],
    contradiction },
  have [ident claim2] [":", expr ∀ A : set X, «expr ∈ »(A, F) → «expr ∈ »(x, cl A)] [],
  { intros [ident A, ident hA],
    exact [expr claim1 (cl A) (is_closed_cl A) (mem_of_superset hA (subset_cl A))] },
  have [ident claim3] [":", expr ∀ S1 S2 «expr ∈ » T0, «expr ∈ »(«expr ∩ »(S1, S2), T0)] [],
  { rintros [ident S1, ident S2, "⟨", ident S1, ",", ident hS1, ",", ident rfl, "⟩", "⟨", ident S2, ",", ident hS2, ",", ident rfl, "⟩"],
    exact [expr ⟨«expr ∩ »(S1, S2), inter_mem hS1 hS2, by simp [] [] [] ["[", expr basic_inter, "]"] [] []⟩] },
  have [ident claim4] [":", expr ∀ S «expr ∈ » T0, «expr ∩ »(AA, S).nonempty] [],
  { rintros [ident S, "⟨", ident S, ",", ident hS, ",", ident rfl, "⟩"],
    rcases [expr claim2 _ hS, "with", "⟨", ident G, ",", ident hG, ",", ident hG2, "⟩"],
    exact [expr ⟨G, hG2, hG⟩] },
  have [ident claim5] [":", expr ∀ S «expr ∈ » T0, set.nonempty S] [],
  { rintros [ident S, "⟨", ident S, ",", ident hS, ",", ident rfl, "⟩"],
    exact [expr ⟨F, hS⟩] },
  have [ident claim6] [":", expr ∀ S «expr ∈ » T2, set.nonempty S] [],
  { suffices [] [":", expr ∀
     S «expr ∈ » T2, «expr ∨ »(«expr ∈ »(S, T0), «expr∃ , »((Q «expr ∈ » T0), «expr = »(S, «expr ∩ »(AA, Q))))],
    { intros [ident S, ident hS],
      cases [expr this _ hS] ["with", ident h, ident h],
      { exact [expr claim5 S h] },
      { rcases [expr h, "with", "⟨", ident Q, ",", ident hQ, ",", ident rfl, "⟩"],
        exact [expr claim4 Q hQ] } },
    intros [ident S, ident hS],
    apply [expr finite_inter_closure_insert],
    { split,
      { use [expr set.univ],
        refine [expr ⟨filter.univ_sets _, _⟩],
        ext [] [] [],
        refine [expr ⟨_, by tauto []⟩],
        { intro [],
          apply [expr filter.univ_sets] } },
      { exact [expr claim3] } },
    { exact [expr hS] } },
  suffices [] [":", expr ∀ F : fsu, «expr ⊆ »(«expr↑ »(F), T1) → «expr⋂₀ »(ι F).nonempty],
  { obtain ["⟨", ident G, ",", ident h1, "⟩", ":=", expr ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ this],
    have [ident c1] [":", expr «expr = »(X.join G, F)] [":=", expr ultrafilter.coe_le_coe.1 (λ
      P hP, h1 (or.inr ⟨P, hP, rfl⟩))],
    have [ident c2] [":", expr «expr = »(G.map X.str, X.incl x)] [],
    { refine [expr ultrafilter.coe_le_coe.1 (λ P hP, _)],
      apply [expr mem_of_superset (h1 (or.inl rfl))],
      rintros [ident x, "⟨", ident rfl, "⟩"],
      exact [expr hP] },
    simp [] [] [] ["[", "<-", expr c1, ",", expr c2, "]"] [] [] },
  intros [ident T, ident hT],
  refine [expr claim6 _ (finite_inter_mem (finite_inter_closure_has_finite_inter _) _ _)],
  intros [ident t, ident ht],
  exact [expr finite_inter_closure.basic (@hT t ht)]
end

theorem le_nhds_of_str_eq {X : Compactum} (F : Ultrafilter X) (x : X) : X.str F = x → «expr↑ » F ≤ 𝓝 x :=
  fun h =>
    le_nhds_iff.mpr
      fun s hx hs =>
        hs _$
          by 
            rwa [h]

instance  {X : Compactum} : T2Space X :=
  by 
    rw [t2_iff_ultrafilter]
    intro _ _ F hx hy 
    rw [←str_eq_of_le_nhds _ _ hx, ←str_eq_of_le_nhds _ _ hy]

/-- The structure map of a compactum actually computes limits. -/
theorem Lim_eq_str {X : Compactum} (F : Ultrafilter X) : F.Lim = X.str F :=
  by 
    rw [Ultrafilter.Lim_eq_iff_le_nhds, le_nhds_iff]
    tauto

theorem cl_eq_closure {X : Compactum} (A : Set X) : cl A = Closure A :=
  by 
    ext 
    rw [mem_closure_iff_ultrafilter]
    split 
    ·
      rintro ⟨F, h1, h2⟩
      exact ⟨F, h1, le_nhds_of_str_eq _ _ h2⟩
    ·
      rintro ⟨F, h1, h2⟩
      exact ⟨F, h1, str_eq_of_le_nhds _ _ h2⟩

/-- Any morphism of compacta is continuous. -/
theorem continuous_of_hom {X Y : Compactum} (f : X ⟶ Y) : Continuous f :=
  by 
    rw [continuous_iff_ultrafilter]
    intro x _ h 
    rw [tendsto, ←coe_map]
    apply le_nhds_of_str_eq 
    rw [←str_hom_commute, str_eq_of_le_nhds _ x h]

-- error in Topology.Category.Compactum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given any compact Hausdorff space, we construct a Compactum. -/
noncomputable
def of_topological_space (X : Type*) [topological_space X] [compact_space X] [t2_space X] : Compactum :=
{ A := X,
  a := ultrafilter.Lim,
  unit' := by { ext [] [ident x] [],
    exact [expr Lim_eq (by finish ["[", expr le_nhds_iff, "]"] [])] },
  assoc' := begin
    ext [] [ident FF] [],
    change [expr ultrafilter (ultrafilter X)] [] ["at", ident FF],
    set [] [ident x] [] [":="] [expr (ultrafilter.map ultrafilter.Lim FF).Lim] ["with", ident c1],
    have [ident c2] [":", expr ∀ (U : set X) (F : ultrafilter X), «expr ∈ »(F.Lim, U) → is_open U → «expr ∈ »(U, F)] [],
    { intros [ident U, ident F, ident h1, ident hU],
      exact [expr «expr ▸ »(c1, is_open_iff_ultrafilter.mp hU _ h1 _ (ultrafilter.le_nhds_Lim _))] },
    have [ident c3] [":", expr «expr ≤ »(«expr↑ »(ultrafilter.map ultrafilter.Lim FF), expr𝓝() x)] [],
    { rw [expr le_nhds_iff] [],
      intros [ident U, ident hx, ident hU],
      exact [expr mem_coe.2 (c2 _ _ (by rwa ["<-", expr c1] []) hU)] },
    have [ident c4] [":", expr ∀
     U : set X, «expr ∈ »(x, U) → is_open U → «expr ∈ »({G : ultrafilter X | «expr ∈ »(U, G)}, FF)] [],
    { intros [ident U, ident hx, ident hU],
      suffices [] [":", expr «expr ∈ »(«expr ⁻¹' »(ultrafilter.Lim, U), FF)],
      { apply [expr mem_of_superset this],
        intros [ident P, ident hP],
        exact [expr c2 U P hP hU] },
      exact [expr @c3 U (is_open.mem_nhds hU hx)] },
    apply [expr Lim_eq],
    rw [expr le_nhds_iff] [],
    exact [expr c4]
  end }

-- error in Topology.Category.Compactum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any continuous map between Compacta is a morphism of compacta. -/
def hom_of_continuous {X Y : Compactum} (f : X → Y) (cont : continuous f) : «expr ⟶ »(X, Y) :=
{ f := f,
  h' := begin
    rw [expr continuous_iff_ultrafilter] ["at", ident cont],
    ext [] ["(", ident F, ":", expr ultrafilter X, ")"] [],
    specialize [expr cont (X.str F) F (le_nhds_of_str_eq F (X.str F) rfl)],
    have [] [] [":=", expr str_eq_of_le_nhds (ultrafilter.map f F) _ cont],
    simpa [] [] ["only"] ["[", "<-", expr this, ",", expr types_comp_apply, ",", expr of_type_functor_map, "]"] [] []
  end }

end Compactum

/-- The functor functor from Compactum to CompHaus. -/
def compactumToCompHaus : Compactum ⥤ CompHaus :=
  { obj := fun X => { toTop := { α := X } },
    map := fun X Y f => { toFun := f, continuous_to_fun := Compactum.continuous_of_hom _ } }

namespace compactumToCompHaus

/-- The functor Compactum_to_CompHaus is full. -/
def full : full compactumToCompHaus.{u} :=
  { Preimage := fun X Y f => Compactum.homOfContinuous f.1 f.2 }

/-- The functor Compactum_to_CompHaus is faithful. -/
theorem faithful : faithful compactumToCompHaus :=
  {  }

/-- This definition is used to prove essential surjectivity of Compactum_to_CompHaus. -/
noncomputable def iso_of_topological_space {D : CompHaus} :
  compactumToCompHaus.obj (Compactum.ofTopologicalSpace D) ≅ D :=
  { Hom :=
      { toFun := id,
        continuous_to_fun :=
          continuous_def.2$
            fun _ h =>
              by 
                rw [is_open_iff_ultrafilter'] at h 
                exact h },
    inv :=
      { toFun := id,
        continuous_to_fun :=
          continuous_def.2$
            fun _ h1 =>
              by 
                rw [is_open_iff_ultrafilter']
                intro _ h2 
                exact h1 _ h2 } }

/-- The functor Compactum_to_CompHaus is essentially surjective. -/
theorem ess_surj : ess_surj compactumToCompHaus :=
  { mem_ess_image := fun X => ⟨Compactum.ofTopologicalSpace X, ⟨iso_of_topological_space⟩⟩ }

/-- The functor Compactum_to_CompHaus is an equivalence of categories. -/
noncomputable def is_equivalence : is_equivalence compactumToCompHaus :=
  by 
    apply equivalence.of_fully_faithfully_ess_surj _ 
    exact compactumToCompHaus.full 
    exact compactumToCompHaus.faithful 
    exact compactumToCompHaus.ess_surj

end compactumToCompHaus

