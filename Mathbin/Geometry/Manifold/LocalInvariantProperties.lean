import Mathbin.Geometry.Manifold.ChartedSpace

/-!
# Local properties invariant under a groupoid

We study properties of a triple `(g, s, x)` where `g` is a function between two spaces `H` and `H'`,
`s` is a subset of `H` and `x` is a point of `H`. Our goal is to register how such a property
should behave to make sense in charted spaces modelled on `H` and `H'`.

The main examples we have in mind are the properties "`g` is differentiable at `x` within `s`", or
"`g` is smooth at `x` within `s`". We want to develop general results that, when applied in these
specific situations, say that the notion of smooth function in a manifold behaves well under
restriction, intersection, is local, and so on.

## Main definitions

* `local_invariant_prop G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `charted_space.lift_prop_within_at` (resp. `lift_prop_at`, `lift_prop_on` and `lift_prop`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : local_invariant_prop G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.lift_prop_within_at_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.lift_prop_within_at_congr` saying that if `lift_prop_within_at P g s x` holds, and `g` and `g'`
coincide on `s`, then `lift_prop_within_at P g' s x` holds. We can't call it
`lift_prop_within_at.congr` as it is in the namespace associated to `local_invariant_prop`, not
in the one for `lift_prop_within_at`.
-/


noncomputable theory

open_locale Classical Manifold TopologicalSpace

open Set

variable{H :
    Type
      _}{M :
    Type
      _}[TopologicalSpace
      H][TopologicalSpace
      M][ChartedSpace H M]{H' : Type _}{M' : Type _}[TopologicalSpace H'][TopologicalSpace M'][ChartedSpace H' M']

namespace StructureGroupoid

variable(G : StructureGroupoid H)(G' : StructureGroupoid H')

/-- Structure recording good behavior of a property of a triple `(f, s, x)` where `f` is a function,
`s` a set and `x` a point. Good behavior here means locality and invariance under given groupoids
(both in the source and in the target). Given such a good behavior, the lift of this property
to charted spaces admitting these groupoids will inherit the good behavior. -/
structure local_invariant_prop(P : (H → H') → Set H → H → Prop) : Prop where 
  is_local : ∀ {s x u} {f : H → H'}, IsOpen u → x ∈ u → (P f s x ↔ P f (s ∩ u) x)
  right_invariance :
  ∀ {s x f} {e : LocalHomeomorph H H}, e ∈ G → x ∈ e.source → P f s x → P (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' s) (e x)
  congr : ∀ {s x} {f g : H → H'}, (∀ y (_ : y ∈ s), f y = g y) → f x = g x → P f s x → P g s x 
  left_invariance :
  ∀ {s x f} {e' : LocalHomeomorph H' H'}, e' ∈ G' → s ⊆ f ⁻¹' e'.source → f x ∈ e'.source → P f s x → P (e' ∘ f) s x

end StructureGroupoid

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`lift_prop_within_at_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
def ChartedSpace.LiftPropWithinAt (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) (x : M) : Prop :=
  ContinuousWithinAt f s x ∧
    P (chart_at H' (f x) ∘ f ∘ (chart_at H x).symm)
      ((chart_at H x).Target ∩ (chart_at H x).symm ⁻¹' (s ∩ f ⁻¹' (chart_at H' (f x)).Source)) (chart_at H x x)

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of functions on sets in a charted space, by requiring that it holds
around each point of the set, in the preferred charts. -/
def ChartedSpace.LiftPropOn (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) :=
  ∀ x (_ : x ∈ s), ChartedSpace.LiftPropWithinAt P f s x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function at a point in a charted space, by requiring that it holds
in the preferred chart. -/
def ChartedSpace.LiftPropAt (P : (H → H') → Set H → H → Prop) (f : M → M') (x : M) :=
  ChartedSpace.LiftPropWithinAt P f univ x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function in a charted space, by requiring that it holds
in the preferred chart around every point. -/
def ChartedSpace.LiftProp (P : (H → H') → Set H → H → Prop) (f : M → M') :=
  ∀ x, ChartedSpace.LiftPropAt P f x

open ChartedSpace

namespace StructureGroupoid

variable{G :
    StructureGroupoid
      H}{G' :
    StructureGroupoid
      H'}{e e' :
    LocalHomeomorph M
      H}{f f' :
    LocalHomeomorph M'
      H'}{P : (H → H') → Set H → H → Prop}{g g' : M → M'}{s t : Set M}{x : M}{Q : (H → H) → Set H → H → Prop}

theorem lift_prop_within_at_univ : lift_prop_within_at P g univ x ↔ lift_prop_at P g x :=
  Iff.rfl

theorem lift_prop_on_univ : lift_prop_on P g univ ↔ lift_prop P g :=
  by 
    simp [lift_prop_on, lift_prop, lift_prop_at]

namespace LocalInvariantProp

variable(hG : G.local_invariant_prop G' P)

include hG

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` can not be captured with a chart in the target). -/
theorem lift_prop_within_at_indep_chart_aux
(he : «expr ∈ »(e, G.maximal_atlas M))
(xe : «expr ∈ »(x, e.source))
(he' : «expr ∈ »(e', G.maximal_atlas M))
(xe' : «expr ∈ »(x, e'.source))
(hf : «expr ∈ »(f, G'.maximal_atlas M'))
(xf : «expr ∈ »(g x, f.source))
(hf' : «expr ∈ »(f', G'.maximal_atlas M'))
(xf' : «expr ∈ »(g x, f'.source))
(hgs : continuous_within_at g s x)
(h : P «expr ∘ »(f, «expr ∘ »(g, e.symm)) «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f.source)))) (e x)) : P «expr ∘ »(f', «expr ∘ »(g, e'.symm)) «expr ∩ »(e'.target, «expr ⁻¹' »(e'.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f'.source)))) (e' x) :=
begin
  obtain ["⟨", ident o, ",", ident o_open, ",", ident xo, ",", ident oe, ",", ident oe', ",", ident of, ",", ident of', "⟩", ":", expr «expr∃ , »((o : set M), «expr ∧ »(is_open o, «expr ∧ »(«expr ∈ »(x, o), «expr ∧ »(«expr ⊆ »(o, e.source), «expr ∧ »(«expr ⊆ »(o, e'.source), «expr ∧ »(«expr ⊆ »(«expr ∩ »(o, s), «expr ⁻¹' »(g, f.source)), «expr ⊆ »(«expr ∩ »(o, s), «expr ⁻¹' »(g, f'.to_local_equiv.source))))))))],
  { have [] [":", expr «expr ∈ »(«expr ∩ »(f.source, f'.source), expr𝓝() (g x))] [":=", expr is_open.mem_nhds (is_open.inter f.open_source f'.open_source) ⟨xf, xf'⟩],
    rcases [expr mem_nhds_within.1 (hgs.preimage_mem_nhds_within this), "with", "⟨", ident u, ",", ident u_open, ",", ident xu, ",", ident hu, "⟩"],
    refine [expr ⟨«expr ∩ »(«expr ∩ »(u, e.source), e'.source), _, ⟨⟨xu, xe⟩, xe'⟩, _, _, _, _⟩],
    { exact [expr is_open.inter (is_open.inter u_open e.open_source) e'.open_source] },
    { assume [binders (x hx)],
      exact [expr hx.1.2] },
    { assume [binders (x hx)],
      exact [expr hx.2] },
    { assume [binders (x hx)],
      exact [expr (hu ⟨hx.1.1.1, hx.2⟩).1] },
    { assume [binders (x hx)],
      exact [expr (hu ⟨hx.1.1.1, hx.2⟩).2] } },
  have [ident A] [":", expr P «expr ∘ »(f, «expr ∘ »(g, e.symm)) «expr ∩ »(«expr ∩ »(e.target, «expr ⁻¹' »(e.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f.source)))), «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, o))) (e x)] [],
  { apply [expr (hG.is_local _ _).1 h],
    { exact [expr e.continuous_on_symm.preimage_open_of_open e.open_target o_open] },
    { simp [] [] ["only"] ["[", expr xe, ",", expr xo, "]"] ["with", ident mfld_simps] [] } },
  have [ident B] [":", expr P «expr ∘ »(«expr ≫ₕ »(f.symm, f'), «expr ∘ »(f, «expr ∘ »(g, e.symm))) «expr ∩ »(«expr ∩ »(e.target, «expr ⁻¹' »(e.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f.source)))), «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, o))) (e x)] [],
  { refine [expr hG.left_invariance (compatible_of_mem_maximal_atlas hf hf') (λ
      y
      hy, _) (by simp [] [] ["only"] ["[", expr xe, ",", expr xf, ",", expr xf', "]"] ["with", ident mfld_simps] []) A],
    simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
    have [] [":", expr «expr ∈ »(e.symm y, «expr ∩ »(o, s))] [],
    by simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [],
    simpa [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] ["using", expr of' this] },
  have [ident C] [":", expr P «expr ∘ »(f', «expr ∘ »(g, e.symm)) «expr ∩ »(«expr ∩ »(e.target, «expr ⁻¹' »(e.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f.source)))), «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, o))) (e x)] [],
  { refine [expr hG.congr (λ
      y hy, _) (by simp [] [] ["only"] ["[", expr xe, ",", expr xf, "]"] ["with", ident mfld_simps] []) B],
    simp [] [] ["only"] ["[", expr local_homeomorph.coe_trans, ",", expr function.comp_app, "]"] [] [],
    rw [expr f.left_inv] [],
    apply [expr of],
    simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
    simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [] },
  let [ident w] [] [":=", expr «expr ≫ₕ »(e.symm, e')],
  let [ident ow] [] [":=", expr «expr ∩ »(w.target, «expr ⁻¹' »(w.symm, «expr ∩ »(«expr ∩ »(e.target, «expr ⁻¹' »(e.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f.source)))), «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, o)))))],
  have [ident wG] [":", expr «expr ∈ »(w, G)] [":=", expr compatible_of_mem_maximal_atlas he he'],
  have [ident D] [":", expr P «expr ∘ »(«expr ∘ »(f', «expr ∘ »(g, e.symm)), w.symm) ow (w (e x))] [":=", expr hG.right_invariance wG (by simp [] [] ["only"] ["[", expr w, ",", expr xe, ",", expr xe', "]"] ["with", ident mfld_simps] []) C],
  have [ident E] [":", expr P «expr ∘ »(f', «expr ∘ »(g, e'.symm)) ow (w (e x))] [],
  { refine [expr hG.congr _ (by simp [] [] ["only"] ["[", expr xe, ",", expr xe', "]"] ["with", ident mfld_simps] []) D],
    assume [binders (y hy)],
    simp [] [] ["only"] [] ["with", ident mfld_simps] [],
    rw [expr e.left_inv] [],
    simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
    simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [] },
  have [] [":", expr «expr = »(w (e x), e' x)] [],
  by simp [] [] ["only"] ["[", expr w, ",", expr xe, "]"] ["with", ident mfld_simps] [],
  rw [expr this] ["at", ident E],
  have [] [":", expr «expr = »(ow, «expr ∩ »(«expr ∩ »(e'.target, «expr ⁻¹' »(e'.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f'.source)))), «expr ∩ »(w.target, «expr ∩ »(e'.target, «expr ⁻¹' »(e'.symm, o)))))] [],
  { ext [] [ident y] [],
    split,
    { assume [binders (hy)],
      have [] [":", expr «expr = »(e.symm (e (e'.symm y)), e'.symm y)] [],
      by { simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
        simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [] },
      simp [] [] ["only"] ["[", expr this, "]"] ["with", ident mfld_simps] ["at", ident hy],
      have [] [":", expr «expr ∈ »(g (e'.symm y), f'.source)] [],
      by { apply [expr of'],
        simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [] },
      simp [] [] ["only"] ["[", expr hy, ",", expr this, "]"] ["with", ident mfld_simps] [] },
    { assume [binders (hy)],
      simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
      have [] [":", expr «expr ∈ »(g (e'.symm y), f.source)] [],
      by { apply [expr of],
        simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [] },
      simp [] [] ["only"] ["[", expr this, ",", expr hy, "]"] ["with", ident mfld_simps] [] } },
  rw [expr this] ["at", ident E],
  apply [expr (hG.is_local _ _).2 E],
  { exact [expr is_open.inter w.open_target (e'.continuous_on_symm.preimage_open_of_open e'.open_target o_open)] },
  { simp [] [] ["only"] ["[", expr xe', ",", expr xe, ",", expr xo, "]"] ["with", ident mfld_simps] [] }
end

theorem lift_prop_within_at_indep_chart [HasGroupoid M G] [HasGroupoid M' G'] (he : e ∈ G.maximal_atlas M)
  (xe : x ∈ e.source) (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
  lift_prop_within_at P g s x ↔
    ContinuousWithinAt g s x ∧ P (f ∘ g ∘ e.symm) (e.target ∩ e.symm ⁻¹' (s ∩ g ⁻¹' f.source)) (e x) :=
  ⟨fun H =>
      ⟨H.1,
        hG.lift_prop_within_at_indep_chart_aux (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) he xe
          (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf H.1 H.2⟩,
    fun H =>
      ⟨H.1,
        hG.lift_prop_within_at_indep_chart_aux he xe (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf
          (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) H.1 H.2⟩⟩

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_on_indep_chart
[has_groupoid M G]
[has_groupoid M' G']
(he : «expr ∈ »(e, G.maximal_atlas M))
(hf : «expr ∈ »(f, G'.maximal_atlas M'))
(h : lift_prop_on P g s) : ∀
y «expr ∈ » «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f.source)))), P «expr ∘ »(f, «expr ∘ »(g, e.symm)) «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, «expr ∩ »(s, «expr ⁻¹' »(g, f.source)))) y :=
begin
  assume [binders (y hy)],
  simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
  have [] [":", expr «expr ∈ »(e.symm y, s)] [],
  by simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [],
  convert [] [expr ((hG.lift_prop_within_at_indep_chart he _ hf _).1 (h _ this)).2] [],
  repeat { simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [] }
end

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_within_at_inter'
(ht : «expr ∈ »(t, «expr𝓝[ ] »(s, x))) : «expr ↔ »(lift_prop_within_at P g «expr ∩ »(s, t) x, lift_prop_within_at P g s x) :=
begin
  by_cases [expr hcont, ":", expr «expr¬ »(continuous_within_at g s x)],
  { have [] [":", expr «expr¬ »(continuous_within_at g «expr ∩ »(s, t) x)] [],
    by rwa ["[", expr continuous_within_at_inter' ht, "]"] [],
    simp [] [] ["only"] ["[", expr lift_prop_within_at, ",", expr hcont, ",", expr this, ",", expr false_and, "]"] [] [] },
  push_neg ["at", ident hcont],
  have [ident A] [":", expr continuous_within_at g «expr ∩ »(s, t) x] [],
  by rwa ["[", expr continuous_within_at_inter' ht, "]"] [],
  obtain ["⟨", ident o, ",", ident o_open, ",", ident xo, ",", ident oc, ",", ident oc', ",", ident ost, "⟩", ":", expr «expr∃ , »((o : set M), «expr ∧ »(is_open o, «expr ∧ »(«expr ∈ »(x, o), «expr ∧ »(«expr ⊆ »(o, (chart_at H x).source), «expr ∧ »(«expr ⊆ »(«expr ∩ »(o, s), «expr ⁻¹' »(g, (chart_at H' (g x)).source)), «expr ⊆ »(«expr ∩ »(o, s), t))))))],
  { rcases [expr mem_nhds_within.1 ht, "with", "⟨", ident u, ",", ident u_open, ",", ident xu, ",", ident ust, "⟩"],
    have [] [":", expr «expr ∈ »((chart_at H' (g x)).source, expr𝓝() (g x))] [":=", expr is_open.mem_nhds (chart_at H' (g x)).open_source (mem_chart_source H' (g x))],
    rcases [expr mem_nhds_within.1 (hcont.preimage_mem_nhds_within this), "with", "⟨", ident v, ",", ident v_open, ",", ident xv, ",", ident hv, "⟩"],
    refine [expr ⟨«expr ∩ »(«expr ∩ »(u, v), (chart_at H x).source), _, ⟨⟨xu, xv⟩, mem_chart_source _ _⟩, _, _, _⟩],
    { exact [expr is_open.inter (is_open.inter u_open v_open) (chart_at H x).open_source] },
    { assume [binders (y hy)],
      exact [expr hy.2] },
    { assume [binders (y hy)],
      exact [expr hv ⟨hy.1.1.2, hy.2⟩] },
    { assume [binders (y hy)],
      exact [expr ust ⟨hy.1.1.1, hy.2⟩] } },
  simp [] [] ["only"] ["[", expr lift_prop_within_at, ",", expr A, ",", expr hcont, ",", expr true_and, ",", expr preimage_inter, "]"] [] [],
  have [ident B] [":", expr is_open «expr ∩ »((chart_at H x).target, «expr ⁻¹' »((chart_at H x).symm, o))] [":=", expr (chart_at H x).preimage_open_of_open_symm o_open],
  have [ident C] [":", expr «expr ∈ »(chart_at H x x, «expr ∩ »((chart_at H x).target, «expr ⁻¹' »((chart_at H x).symm, o)))] [],
  by simp [] [] ["only"] ["[", expr xo, "]"] ["with", ident mfld_simps] [],
  conv_lhs [] [] { rw [expr hG.is_local B C] },
  conv_rhs [] [] { rw [expr hG.is_local B C] },
  congr' [2] [],
  have [] [":", expr ∀ y, «expr ∈ »(y, «expr ∩ »(o, s)) → «expr ∈ »(y, t)] [":=", expr ost],
  mfld_set_tac
end

theorem lift_prop_within_at_inter (ht : t ∈ 𝓝 x) : lift_prop_within_at P g (s ∩ t) x ↔ lift_prop_within_at P g s x :=
  hG.lift_prop_within_at_inter' (mem_nhds_within_of_mem_nhds ht)

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_at_of_lift_prop_within_at
(h : lift_prop_within_at P g s x)
(hs : «expr ∈ »(s, expr𝓝() x)) : lift_prop_at P g x :=
begin
  have [] [":", expr «expr = »(s, «expr ∩ »(univ, s))] [],
  by rw [expr univ_inter] [],
  rwa ["[", expr this, ",", expr hG.lift_prop_within_at_inter hs, "]"] ["at", ident h]
end

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_within_at_of_lift_prop_at_of_mem_nhds
(h : lift_prop_at P g x)
(hs : «expr ∈ »(s, expr𝓝() x)) : lift_prop_within_at P g s x :=
begin
  have [] [":", expr «expr = »(s, «expr ∩ »(univ, s))] [],
  by rw [expr univ_inter] [],
  rwa ["[", expr this, ",", expr hG.lift_prop_within_at_inter hs, "]"] []
end

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_on_of_locally_lift_prop_on
(h : ∀
 x «expr ∈ » s, «expr∃ , »((u), «expr ∧ »(is_open u, «expr ∧ »(«expr ∈ »(x, u), lift_prop_on P g «expr ∩ »(s, u))))) : lift_prop_on P g s :=
begin
  assume [binders (x hx)],
  rcases [expr h x hx, "with", "⟨", ident u, ",", ident u_open, ",", ident xu, ",", ident hu, "⟩"],
  have [] [] [":=", expr hu x ⟨hx, xu⟩],
  rwa [expr hG.lift_prop_within_at_inter] ["at", ident this],
  exact [expr is_open.mem_nhds u_open xu]
end

theorem lift_prop_of_locally_lift_prop_on (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ lift_prop_on P g u) : lift_prop P g :=
  by 
    rw [←lift_prop_on_univ]
    apply hG.lift_prop_on_of_locally_lift_prop_on fun x hx => _ 
    simp [h x]

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_within_at_congr
(h : lift_prop_within_at P g s x)
(h₁ : ∀ y «expr ∈ » s, «expr = »(g' y, g y))
(hx : «expr = »(g' x, g x)) : lift_prop_within_at P g' s x :=
begin
  refine [expr ⟨h.1.congr h₁ hx, _⟩],
  have [ident A] [":", expr «expr = »(«expr ∩ »(s, «expr ⁻¹' »(g', (chart_at H' (g' x)).source)), «expr ∩ »(s, «expr ⁻¹' »(g, (chart_at H' (g' x)).source)))] [],
  { ext [] [ident y] [],
    split,
    { assume [binders (hy)],
      simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
      simp [] [] ["only"] ["[", expr hy, ",", "<-", expr h₁ _ hy.1, "]"] ["with", ident mfld_simps] [] },
    { assume [binders (hy)],
      simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
      simp [] [] ["only"] ["[", expr hy, ",", expr h₁ _ hy.1, "]"] ["with", ident mfld_simps] [] } },
  have [] [] [":=", expr h.2],
  rw ["[", "<-", expr hx, ",", "<-", expr A, "]"] ["at", ident this],
  convert [] [expr hG.congr _ _ this] ["using", 2],
  { assume [binders (y hy)],
    simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
    have [] [":", expr «expr ∈ »((chart_at H x).symm y, s)] [],
    by simp [] [] ["only"] ["[", expr hy, "]"] [] [],
    simp [] [] ["only"] ["[", expr hy, ",", expr h₁ _ this, "]"] ["with", ident mfld_simps] [] },
  { simp [] [] ["only"] ["[", expr hx, "]"] ["with", ident mfld_simps] [] }
end

theorem lift_prop_within_at_congr_iff (h₁ : ∀ y (_ : y ∈ s), g' y = g y) (hx : g' x = g x) :
  lift_prop_within_at P g' s x ↔ lift_prop_within_at P g s x :=
  ⟨fun h => hG.lift_prop_within_at_congr h (fun y hy => (h₁ y hy).symm) hx.symm,
    fun h => hG.lift_prop_within_at_congr h h₁ hx⟩

theorem lift_prop_within_at_congr_of_eventually_eq (h : lift_prop_within_at P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g)
  (hx : g' x = g x) : lift_prop_within_at P g' s x :=
  by 
    rcases h₁.exists_mem with ⟨t, t_nhd, ht⟩
    rw [←hG.lift_prop_within_at_inter' t_nhd] at h⊢
    exact hG.lift_prop_within_at_congr h (fun y hy => ht hy.2) hx

theorem lift_prop_within_at_congr_iff_of_eventually_eq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
  lift_prop_within_at P g' s x ↔ lift_prop_within_at P g s x :=
  ⟨fun h => hG.lift_prop_within_at_congr_of_eventually_eq h h₁.symm hx.symm,
    fun h => hG.lift_prop_within_at_congr_of_eventually_eq h h₁ hx⟩

theorem lift_prop_at_congr_of_eventually_eq (h : lift_prop_at P g x) (h₁ : g' =ᶠ[𝓝 x] g) : lift_prop_at P g' x :=
  by 
    apply hG.lift_prop_within_at_congr_of_eventually_eq h _ h₁.eq_of_nhds 
    convert h₁ 
    rw [nhds_within_univ]

theorem lift_prop_at_congr_iff_of_eventually_eq (h₁ : g' =ᶠ[𝓝 x] g) : lift_prop_at P g' x ↔ lift_prop_at P g x :=
  ⟨fun h => hG.lift_prop_at_congr_of_eventually_eq h h₁.symm, fun h => hG.lift_prop_at_congr_of_eventually_eq h h₁⟩

theorem lift_prop_on_congr (h : lift_prop_on P g s) (h₁ : ∀ y (_ : y ∈ s), g' y = g y) : lift_prop_on P g' s :=
  fun x hx => hG.lift_prop_within_at_congr (h x hx) h₁ (h₁ x hx)

theorem lift_prop_on_congr_iff (h₁ : ∀ y (_ : y ∈ s), g' y = g y) : lift_prop_on P g' s ↔ lift_prop_on P g s :=
  ⟨fun h => hG.lift_prop_on_congr h fun y hy => (h₁ y hy).symm, fun h => hG.lift_prop_on_congr h h₁⟩

omit hG

theorem lift_prop_within_at_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
  (h : lift_prop_within_at P g t x) (hst : s ⊆ t) : lift_prop_within_at P g s x :=
  by 
    refine' ⟨h.1.mono hst, _⟩
    apply mono (fun y hy => _) h.2
    simp' only with mfld_simps  at hy 
    simp' only [hy, hst _] with mfld_simps

theorem lift_prop_within_at_of_lift_prop_at (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
  (h : lift_prop_at P g x) : lift_prop_within_at P g s x :=
  by 
    rw [←lift_prop_within_at_univ] at h 
    exact lift_prop_within_at_mono mono h (subset_univ _)

theorem lift_prop_on_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x) (h : lift_prop_on P g t)
  (hst : s ⊆ t) : lift_prop_on P g s :=
  fun x hx => lift_prop_within_at_mono mono (h x (hst hx)) hst

theorem lift_prop_on_of_lift_prop (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x) (h : lift_prop P g) :
  lift_prop_on P g s :=
  by 
    rw [←lift_prop_on_univ] at h 
    exact lift_prop_on_mono mono h (subset_univ _)

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_at_of_mem_maximal_atlas
[has_groupoid M G]
(hG : G.local_invariant_prop G Q)
(hQ : ∀ y, Q id univ y)
(he : «expr ∈ »(e, maximal_atlas M G))
(hx : «expr ∈ »(x, e.source)) : lift_prop_at Q e x :=
begin
  suffices [ident h] [":", expr Q «expr ∘ »(e, e.symm) e.target (e x)],
  { rw ["[", expr lift_prop_at, ",", expr hG.lift_prop_within_at_indep_chart he hx G.id_mem_maximal_atlas (mem_univ _), "]"] [],
    refine [expr ⟨(e.continuous_at hx).continuous_within_at, _⟩],
    simpa [] [] ["only"] [] ["with", ident mfld_simps] [] },
  have [ident A] [":", expr Q id e.target (e x)] [],
  { have [] [":", expr «expr ∈ »(e x, e.target)] [],
    by simp [] [] ["only"] ["[", expr hx, "]"] ["with", ident mfld_simps] [],
    simpa [] [] ["only"] [] ["with", ident mfld_simps] ["using", expr (hG.is_local e.open_target this).1 (hQ (e x))] },
  apply [expr hG.congr _ _ A]; simp [] [] ["only"] ["[", expr hx, "]"] ["with", ident mfld_simps] [] { contextual := tt }
end

theorem lift_prop_on_of_mem_maximal_atlas [HasGroupoid M G] (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y)
  (he : e ∈ maximal_atlas M G) : lift_prop_on Q e e.source :=
  by 
    intro x hx 
    apply hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds (hG.lift_prop_at_of_mem_maximal_atlas hQ he hx)
    apply IsOpen.mem_nhds e.open_source hx

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_at_symm_of_mem_maximal_atlas
[has_groupoid M G]
{x : H}
(hG : G.local_invariant_prop G Q)
(hQ : ∀ y, Q id univ y)
(he : «expr ∈ »(e, maximal_atlas M G))
(hx : «expr ∈ »(x, e.target)) : lift_prop_at Q e.symm x :=
begin
  suffices [ident h] [":", expr Q «expr ∘ »(e, e.symm) e.target x],
  { have [ident A] [":", expr «expr = »(«expr ∩ »(«expr ⁻¹' »(e.symm, e.source), e.target), e.target)] [],
    by mfld_set_tac,
    have [] [":", expr «expr ∈ »(e.symm x, e.source)] [],
    by simp [] [] ["only"] ["[", expr hx, "]"] ["with", ident mfld_simps] [],
    rw ["[", expr lift_prop_at, ",", expr hG.lift_prop_within_at_indep_chart G.id_mem_maximal_atlas (mem_univ _) he this, "]"] [],
    refine [expr ⟨(e.symm.continuous_at hx).continuous_within_at, _⟩],
    simp [] [] ["only"] [] ["with", ident mfld_simps] [],
    rwa ["[", expr hG.is_local e.open_target hx, ",", expr A, "]"] [] },
  have [ident A] [":", expr Q id e.target x] [],
  by simpa [] [] ["only"] [] ["with", ident mfld_simps] ["using", expr (hG.is_local e.open_target hx).1 (hQ x)],
  apply [expr hG.congr _ _ A]; simp [] [] ["only"] ["[", expr hx, "]"] ["with", ident mfld_simps] [] { contextual := tt }
end

theorem lift_prop_on_symm_of_mem_maximal_atlas [HasGroupoid M G] (hG : G.local_invariant_prop G Q)
  (hQ : ∀ y, Q id univ y) (he : e ∈ maximal_atlas M G) : lift_prop_on Q e.symm e.target :=
  by 
    intro x hx 
    apply hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds (hG.lift_prop_at_symm_of_mem_maximal_atlas hQ he hx)
    apply IsOpen.mem_nhds e.open_target hx

theorem lift_prop_at_chart [HasGroupoid M G] (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_at Q (chart_at H x) x :=
  hG.lift_prop_at_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x) (mem_chart_source H x)

theorem lift_prop_on_chart [HasGroupoid M G] (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_on Q (chart_at H x) (chart_at H x).Source :=
  hG.lift_prop_on_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)

theorem lift_prop_at_chart_symm [HasGroupoid M G] (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_at Q (chart_at H x).symm ((chart_at H x) x) :=
  hG.lift_prop_at_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)
    (by 
      simp )

theorem lift_prop_on_chart_symm [HasGroupoid M G] (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) :
  lift_prop_on Q (chart_at H x).symm (chart_at H x).Target :=
  hG.lift_prop_on_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lift_prop_id (hG : G.local_invariant_prop G Q) (hQ : ∀ y, Q id univ y) : lift_prop Q (id : M → M) :=
begin
  assume [binders (x)],
  dsimp [] ["[", expr lift_prop_at, ",", expr lift_prop_within_at, "]"] [] [],
  refine [expr ⟨continuous_within_at_id, _⟩],
  let [ident t] [] [":=", expr «expr ∩ »((chart_at H x).target, «expr ⁻¹' »((chart_at H x).symm, (chart_at H x).source))],
  suffices [ident H] [":", expr Q id t (chart_at H x x)],
  { simp [] [] ["only"] [] ["with", ident mfld_simps] [],
    refine [expr hG.congr (λ y hy, _) (by simp [] [] [] [] [] []) H],
    simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
    simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [] },
  have [] [":", expr «expr = »(t, «expr ∩ »(univ, (chart_at H x).target))] [],
  by mfld_set_tac,
  rw [expr this] [],
  exact [expr (hG.is_local (chart_at H x).open_target (by simp [] [] [] [] [] [])).1 (hQ _)]
end

end LocalInvariantProp

section LocalStructomorph

variable(G)

open LocalHomeomorph

/-- A function from a model space `H` to itself is a local structomorphism, with respect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
def is_local_structomorph_within_at (f : H → H) (s : Set H) (x : H) : Prop :=
  x ∈ s → ∃ e : LocalHomeomorph H H, e ∈ G ∧ eq_on f e.to_fun (s ∩ e.source) ∧ x ∈ e.source

-- error in Geometry.Manifold.LocalInvariantProperties: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For a groupoid `G` which is `closed_under_restriction`, being a local structomorphism is a local
invariant property. -/
theorem is_local_structomorph_within_at_local_invariant_prop
[closed_under_restriction G] : local_invariant_prop G G (is_local_structomorph_within_at G) :=
{ is_local := begin
    intros [ident s, ident x, ident u, ident f, ident hu, ident hux],
    split,
    { rintros [ident h, ident hx],
      rcases [expr h hx.1, "with", "⟨", ident e, ",", ident heG, ",", ident hef, ",", ident hex, "⟩"],
      have [] [":", expr «expr ⊆ »(«expr ∩ »(«expr ∩ »(s, u), e.source), «expr ∩ »(s, e.source))] [":=", expr by mfld_set_tac],
      exact [expr ⟨e, heG, hef.mono this, hex⟩] },
    { rintros [ident h, ident hx],
      rcases [expr h ⟨hx, hux⟩, "with", "⟨", ident e, ",", ident heG, ",", ident hef, ",", ident hex, "⟩"],
      refine [expr ⟨e.restr (interior u), _, _, _⟩],
      { exact [expr closed_under_restriction' heG is_open_interior] },
      { have [] [":", expr «expr = »(«expr ∩ »(«expr ∩ »(s, u), e.source), «expr ∩ »(s, «expr ∩ »(e.source, u)))] [":=", expr by mfld_set_tac],
        simpa [] [] ["only"] ["[", expr this, ",", expr interior_interior, ",", expr hu.interior_eq, "]"] ["with", ident mfld_simps] ["using", expr hef] },
      { simp [] [] ["only"] ["[", "*", ",", expr interior_interior, ",", expr hu.interior_eq, "]"] ["with", ident mfld_simps] [] } }
  end,
  right_invariance := begin
    intros [ident s, ident x, ident f, ident e', ident he'G, ident he'x, ident h, ident hx],
    have [ident hxs] [":", expr «expr ∈ »(x, s)] [":=", expr by simpa [] [] ["only"] ["[", expr e'.left_inv he'x, "]"] ["with", ident mfld_simps] ["using", expr hx.2]],
    rcases [expr h hxs, "with", "⟨", ident e, ",", ident heG, ",", ident hef, ",", ident hex, "⟩"],
    refine [expr ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, _, _⟩],
    { intros [ident y, ident hy],
      simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
      simp [] [] ["only"] ["[", expr hef ⟨hy.1.2, hy.2.2⟩, "]"] ["with", ident mfld_simps] [] },
    { simp [] [] ["only"] ["[", expr hex, ",", expr he'x, "]"] ["with", ident mfld_simps] [] }
  end,
  congr := begin
    intros [ident s, ident x, ident f, ident g, ident hfgs, ident hfg', ident h, ident hx],
    rcases [expr h hx, "with", "⟨", ident e, ",", ident heG, ",", ident hef, ",", ident hex, "⟩"],
    refine [expr ⟨e, heG, _, hex⟩],
    intros [ident y, ident hy],
    rw ["[", "<-", expr hef hy, ",", expr hfgs y hy.1, "]"] []
  end,
  left_invariance := begin
    intros [ident s, ident x, ident f, ident e', ident he'G, ident he', ident hfx, ident h, ident hx],
    rcases [expr h hx, "with", "⟨", ident e, ",", ident heG, ",", ident hef, ",", ident hex, "⟩"],
    refine [expr ⟨e.trans e', G.trans heG he'G, _, _⟩],
    { intros [ident y, ident hy],
      simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
      simp [] [] ["only"] ["[", expr hef ⟨hy.1, hy.2.1⟩, "]"] ["with", ident mfld_simps] [] },
    { simpa [] [] ["only"] ["[", expr hex, ",", expr hef ⟨hx, hex⟩, "]"] ["with", ident mfld_simps] ["using", expr hfx] }
  end }

end LocalStructomorph

end StructureGroupoid

