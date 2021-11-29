import Mathbin.Topology.ContinuousFunction.Weierstrass 
import Mathbin.Analysis.Complex.Basic

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topological_closure`.
  This follows from the Weierstrass approximation theorem on `[-∥f∥, ∥f∥]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topological_closure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topological_closure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for self-adjoint subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/


noncomputable theory

namespace ContinuousMap

variable {X : Type _} [TopologicalSpace X] [CompactSpace X]

/--
Turn a function `f : C(X, ℝ)` into a continuous map into `set.Icc (-∥f∥) (∥f∥)`,
thereby explicitly attaching bounds.
-/
def attach_bound (f : C(X, ℝ)) : C(X, Set.Icc (-∥f∥) ∥f∥) :=
  { toFun := fun x => ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩ }

@[simp]
theorem attach_bound_apply_coe (f : C(X, ℝ)) (x : X) : ((attach_bound f) x : ℝ) = f x :=
  rfl

theorem polynomial_comp_attach_bound (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : Polynomial ℝ) :
  (g.to_continuous_map_on (Set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attachBound = Polynomial.aeval f g :=
  by 
    ext 
    simp only [ContinuousMap.comp_coe, Function.comp_app, ContinuousMap.attach_bound_apply_coe,
      Polynomial.to_continuous_map_on_to_fun, Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuous_map_apply,
      Polynomial.to_continuous_map_to_fun]

/--
Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `set.Icc (-∥f∥) ∥f∥)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`.
-/
theorem polynomial_comp_attach_bound_mem (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : Polynomial ℝ) :
  (g.to_continuous_map_on (Set.Icc (-∥f∥) ∥f∥)).comp (f : C(X, ℝ)).attachBound ∈ A :=
  by 
    rw [polynomial_comp_attach_bound]
    apply SetLike.coe_mem

-- error in Topology.ContinuousFunction.StoneWeierstrass: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_attach_bound_mem_closure
(A : subalgebra exprℝ() «exprC( , )»(X, exprℝ()))
(f : A)
(p : «exprC( , )»(set.Icc «expr- »(«expr∥ ∥»(f)) «expr∥ ∥»(f), exprℝ())) : «expr ∈ »(p.comp (attach_bound f), A.topological_closure) :=
begin
  have [ident mem_closure] [":", expr «expr ∈ »(p, (polynomial_functions (set.Icc «expr- »(«expr∥ ∥»(f)) «expr∥ ∥»(f))).topological_closure)] [":=", expr continuous_map_mem_polynomial_functions_closure _ _ p],
  have [ident frequently_mem_polynomials] [] [":=", expr mem_closure_iff_frequently.mp mem_closure],
  apply [expr mem_closure_iff_frequently.mpr],
  refine [expr ((comp_right_continuous_map exprℝ() (attach_bound (f : «exprC( , )»(X, exprℝ())))).continuous_at p).tendsto.frequently_map _ _ frequently_mem_polynomials],
  rintros ["_", "⟨", ident g, ",", "⟨", "-", ",", ident rfl, "⟩", "⟩"],
  simp [] [] ["only"] ["[", expr set_like.mem_coe, ",", expr alg_hom.coe_to_ring_hom, ",", expr comp_right_continuous_map_apply, ",", expr polynomial.to_continuous_map_on_alg_hom_apply, "]"] [] [],
  apply [expr polynomial_comp_attach_bound_mem]
end

theorem abs_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) : (f : C(X, ℝ)).abs ∈ A.topological_closure :=
  by 
    let M := ∥f∥
    let f' := attach_bound (f : C(X, ℝ))
    let abs : C(Set.Icc (-∥f∥) ∥f∥, ℝ) := { toFun := fun x : Set.Icc (-∥f∥) ∥f∥ => |(x : ℝ)| }
    change abs.comp f' ∈ A.topological_closure 
    apply comp_attach_bound_mem_closure

theorem inf_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
  (f : C(X, ℝ))⊓(g : C(X, ℝ)) ∈ A.topological_closure :=
  by 
    rw [inf_eq]
    refine'
      A.topological_closure.smul_mem
        (A.topological_closure.sub_mem
          (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
            (A.subalgebra_topological_closure g.property))
          _)
        _ 
    exactModCast abs_mem_subalgebra_closure A _

theorem inf_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ))) (f g : A) :
  (f : C(X, ℝ))⊓(g : C(X, ℝ)) ∈ A :=
  by 
    convert inf_mem_subalgebra_closure A f g 
    apply SetLike.ext' 
    symm 
    erw [closure_eq_iff_is_closed]
    exact h

theorem sup_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
  (f : C(X, ℝ))⊔(g : C(X, ℝ)) ∈ A.topological_closure :=
  by 
    rw [sup_eq]
    refine'
      A.topological_closure.smul_mem
        (A.topological_closure.add_mem
          (A.topological_closure.add_mem (A.subalgebra_topological_closure f.property)
            (A.subalgebra_topological_closure g.property))
          _)
        _ 
    exactModCast abs_mem_subalgebra_closure A _

theorem sup_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ))) (f g : A) :
  (f : C(X, ℝ))⊔(g : C(X, ℝ)) ∈ A :=
  by 
    convert sup_mem_subalgebra_closure A f g 
    apply SetLike.ext' 
    symm 
    erw [closure_eq_iff_is_closed]
    exact h

open_locale TopologicalSpace

-- error in Topology.ContinuousFunction.StoneWeierstrass: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sublattice_closure_eq_top
(L : set «exprC( , )»(X, exprℝ()))
(nA : L.nonempty)
(inf_mem : ∀ f g «expr ∈ » L, «expr ∈ »(«expr ⊓ »(f, g), L))
(sup_mem : ∀ f g «expr ∈ » L, «expr ∈ »(«expr ⊔ »(f, g), L))
(sep : L.separates_points_strongly) : «expr = »(closure L, «expr⊤»()) :=
begin
  apply [expr eq_top_iff.mpr],
  rintros [ident f, "-"],
  refine [expr filter.frequently.mem_closure ((filter.has_basis.frequently_iff metric.nhds_basis_ball).mpr (λ
     ε pos, _))],
  simp [] [] ["only"] ["[", expr exists_prop, ",", expr metric.mem_ball, "]"] [] [],
  by_cases [expr nX, ":", expr nonempty X],
  swap,
  exact [expr ⟨nA.some, (dist_lt_iff pos).mpr (λ x, false.elim (nX ⟨x⟩)), nA.some_spec⟩],
  dsimp [] ["[", expr set.separates_points_strongly, "]"] [] ["at", ident sep],
  let [ident g] [":", expr X → X → L] [":=", expr λ x y, (sep f x y).some],
  have [ident w₁] [":", expr ∀ x y, «expr = »(g x y x, f x)] [":=", expr λ x y, (sep f x y).some_spec.1],
  have [ident w₂] [":", expr ∀ x y, «expr = »(g x y y, f y)] [":=", expr λ x y, (sep f x y).some_spec.2],
  let [ident U] [":", expr X → X → set X] [":=", expr λ x y, {z | «expr < »(«expr - »(f z, ε), g x y z)}],
  have [ident U_nhd_y] [":", expr ∀ x y, «expr ∈ »(U x y, expr𝓝() y)] [],
  { intros [ident x, ident y],
    refine [expr is_open.mem_nhds _ _],
    { apply [expr is_open_lt]; continuity [] [] },
    { rw ["[", expr set.mem_set_of_eq, ",", expr w₂, "]"] [],
      exact [expr sub_lt_self _ pos] } },
  let [ident ys] [":", expr ∀ x, finset X] [":=", expr λ x, (compact_space.elim_nhds_subcover (U x) (U_nhd_y x)).some],
  let [ident ys_w] [":", expr ∀
   x, «expr = »(«expr⋃ , »((y «expr ∈ » ys x), U x y), «expr⊤»())] [":=", expr λ
   x, (compact_space.elim_nhds_subcover (U x) (U_nhd_y x)).some_spec],
  have [ident ys_nonempty] [":", expr ∀
   x, (ys x).nonempty] [":=", expr λ x, set.nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x)],
  let [ident h] [":", expr ∀
   x, L] [":=", expr λ
   x, ⟨(ys x).sup' (ys_nonempty x) (λ
     y, (g x y : «exprC( , )»(X, exprℝ()))), finset.sup'_mem _ sup_mem _ _ _ (λ y _, (g x y).2)⟩],
  have [ident lt_h] [":", expr ∀ x z, «expr < »(«expr - »(f z, ε), h x z)] [],
  { intros [ident x, ident z],
    obtain ["⟨", ident y, ",", ident ym, ",", ident zm, "⟩", ":=", expr set.exists_set_mem_of_union_eq_top _ _ (ys_w x) z],
    dsimp [] ["[", expr h, "]"] [] [],
    simp [] [] ["only"] ["[", expr coe_fn_coe_base', ",", expr subtype.coe_mk, ",", expr sup'_coe, ",", expr finset.sup'_apply, ",", expr finset.lt_sup'_iff, "]"] [] [],
    exact [expr ⟨y, ym, zm⟩] },
  have [ident h_eq] [":", expr ∀ x, «expr = »(h x x, f x)] [],
  { intro [ident x],
    simp [] [] ["only"] ["[", expr coe_fn_coe_base', "]"] [] ["at", ident w₁],
    simp [] [] [] ["[", expr coe_fn_coe_base', ",", expr w₁, "]"] [] [] },
  let [ident W] [":", expr ∀ x, set X] [":=", expr λ x, {z | «expr < »(h x z, «expr + »(f z, ε))}],
  have [ident W_nhd] [":", expr ∀ x, «expr ∈ »(W x, expr𝓝() x)] [],
  { intros [ident x],
    refine [expr is_open.mem_nhds _ _],
    { apply [expr is_open_lt]; continuity [] [] },
    { dsimp ["only"] ["[", expr W, ",", expr set.mem_set_of_eq, "]"] [] [],
      rw [expr h_eq] [],
      exact [expr lt_add_of_pos_right _ pos] } },
  let [ident xs] [":", expr finset X] [":=", expr (compact_space.elim_nhds_subcover W W_nhd).some],
  let [ident xs_w] [":", expr «expr = »(«expr⋃ , »((x «expr ∈ » xs), W x), «expr⊤»())] [":=", expr (compact_space.elim_nhds_subcover W W_nhd).some_spec],
  have [ident xs_nonempty] [":", expr xs.nonempty] [":=", expr set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w],
  let [ident k] [":", expr (L : Type*)] [":=", expr ⟨xs.inf' xs_nonempty (λ
     x, (h x : «exprC( , )»(X, exprℝ()))), finset.inf'_mem _ inf_mem _ _ _ (λ x _, (h x).2)⟩],
  refine [expr ⟨k.1, _, k.2⟩],
  rw [expr dist_lt_iff pos] [],
  intro [ident z],
  rw ["[", expr show ∀
   a
   b
   ε : exprℝ(), «expr ↔ »(«expr < »(dist a b, ε), «expr ∧ »(«expr < »(a, «expr + »(b, ε)), «expr < »(«expr - »(b, ε), a))), by { intros [],
     simp [] [] ["only"] ["[", "<-", expr metric.mem_ball, ",", expr real.ball_eq_Ioo, ",", expr set.mem_Ioo, ",", expr and_comm, "]"] [] [] }, "]"] [],
  fsplit,
  { dsimp [] ["[", expr k, "]"] [] [],
    simp [] [] ["only"] ["[", expr finset.inf'_lt_iff, ",", expr continuous_map.inf'_apply, "]"] [] [],
    exact [expr set.exists_set_mem_of_union_eq_top _ _ xs_w z] },
  { dsimp [] ["[", expr k, "]"] [] [],
    simp [] [] ["only"] ["[", expr finset.lt_inf'_iff, ",", expr continuous_map.inf'_apply, "]"] [] [],
    intros [ident x, ident xm],
    apply [expr lt_h] }
end

-- error in Topology.ContinuousFunction.StoneWeierstrass: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
theorem subalgebra_topological_closure_eq_top_of_separates_points
(A : subalgebra exprℝ() «exprC( , )»(X, exprℝ()))
(w : A.separates_points) : «expr = »(A.topological_closure, «expr⊤»()) :=
begin
  apply [expr set_like.ext'],
  let [ident L] [] [":=", expr A.topological_closure],
  have [ident n] [":", expr set.nonempty (L : set «exprC( , )»(X, exprℝ()))] [":=", expr ⟨(1 : «exprC( , )»(X, exprℝ())), A.subalgebra_topological_closure A.one_mem⟩],
  convert [] [expr sublattice_closure_eq_top (L : set «exprC( , )»(X, exprℝ())) n (λ
    f
    g
    fm
    gm, inf_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩) (λ
    f
    g
    fm
    gm, sup_mem_closed_subalgebra L A.is_closed_topological_closure ⟨f, fm⟩ ⟨g, gm⟩) (subalgebra.separates_points.strongly (subalgebra.separates_points_monotone A.subalgebra_topological_closure w))] [],
  { simp [] [] [] [] [] [] }
end

/--
An alternative statement of the Stone-Weierstrass theorem.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is a uniform limit of elements of `A`.
-/
theorem continuous_map_mem_subalgebra_closure_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.separates_points)
  (f : C(X, ℝ)) : f ∈ A.topological_closure :=
  by 
    rw [subalgebra_topological_closure_eq_top_of_separates_points A w]
    simp 

-- error in Topology.ContinuousFunction.StoneWeierstrass: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_map_of_separates_points
(A : subalgebra exprℝ() «exprC( , )»(X, exprℝ()))
(w : A.separates_points)
(f : «exprC( , )»(X, exprℝ()))
(ε : exprℝ())
(pos : «expr < »(0, ε)) : «expr∃ , »((g : A), «expr < »(«expr∥ ∥»(«expr - »((g : «exprC( , )»(X, exprℝ())), f)), ε)) :=
begin
  have [ident w] [] [":=", expr mem_closure_iff_frequently.mp (continuous_map_mem_subalgebra_closure_of_separates_points A w f)],
  rw [expr metric.nhds_basis_ball.frequently_iff] ["at", ident w],
  obtain ["⟨", ident g, ",", ident H, ",", ident m, "⟩", ":=", expr w ε pos],
  rw ["[", expr metric.mem_ball, ",", expr dist_eq_norm, "]"] ["at", ident H],
  exact [expr ⟨⟨g, m⟩, H⟩]
end

/--
An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons and don't like bundled continuous functions.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_of_separates_points (A : Subalgebra ℝ C(X, ℝ)) (w : A.separates_points)
  (f : X → ℝ) (c : Continuous f) (ε : ℝ) (pos : 0 < ε) : ∃ g : A, ∀ x, ∥g x - f x∥ < ε :=
  by 
    obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuous_map_of_separates_points A w ⟨f, c⟩ ε Pos 
    use g 
    rwa [norm_lt_iff _ Pos] at b

end ContinuousMap

section Complex

open Complex

variable {X : Type _} [TopologicalSpace X]

namespace ContinuousMap

/-- A real subalgebra of `C(X, ℂ)` is `conj_invariant`, if it contains all its conjugates. -/
def conj_invariant_subalgebra (A : Subalgebra ℝ C(X, ℂ)) : Prop :=
  A.map (conj_ae.toAlgHom.compLeftContinuous ℝ conj_cle.Continuous) ≤ A

theorem mem_conj_invariant_subalgebra {A : Subalgebra ℝ C(X, ℂ)} (hA : conj_invariant_subalgebra A) {f : C(X, ℂ)}
  (hf : f ∈ A) : (conj_ae.toAlgHom.compLeftContinuous ℝ conj_cle.Continuous) f ∈ A :=
  hA ⟨f, hf, rfl⟩

end ContinuousMap

open ContinuousMap

-- error in Topology.ContinuousFunction.StoneWeierstrass: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a conjugation-invariant subalgebra of `C(X, ℂ)` separates points, then the real subalgebra
of its purely real-valued elements also separates points. -/
theorem subalgebra.separates_points.complex_to_real
{A : subalgebra exprℂ() «exprC( , )»(X, exprℂ())}
(hA : A.separates_points)
(hA' : conj_invariant_subalgebra (A.restrict_scalars exprℝ())) : ((A.restrict_scalars exprℝ()).comap' (of_real_am.comp_left_continuous exprℝ() continuous_of_real)).separates_points :=
begin
  intros [ident x₁, ident x₂, ident hx],
  obtain ["⟨", "_", ",", "⟨", ident f, ",", ident hfA, ",", ident rfl, "⟩", ",", ident hf, "⟩", ":=", expr hA hx],
  let [ident F] [":", expr «exprC( , )»(X, exprℂ())] [":=", expr «expr - »(f, const (f x₂))],
  have [ident hFA] [":", expr «expr ∈ »(F, A)] [],
  { refine [expr A.sub_mem hfA _],
    convert [] [expr A.smul_mem A.one_mem (f x₂)] [],
    ext1 [] [],
    simp [] [] [] [] [] [] },
  refine [expr ⟨_, ⟨(⟨complex.norm_sq, continuous_norm_sq⟩ : «exprC( , )»(exprℂ(), exprℝ())).comp F, _, rfl⟩, _⟩],
  { rw ["[", expr set_like.mem_coe, ",", expr subalgebra.mem_comap, "]"] [],
    convert [] [expr (A.restrict_scalars exprℝ()).mul_mem (mem_conj_invariant_subalgebra hA' hFA) hFA] [],
    ext1 [] [],
    exact [expr complex.norm_sq_eq_conj_mul_self] },
  { have [] [":", expr «expr ≠ »(«expr - »(f x₁, f x₂), 0)] [":=", expr sub_ne_zero.mpr hf],
    simpa [] [] [] [] [] ["using", expr this] }
end

variable [CompactSpace X]

-- error in Topology.ContinuousFunction.StoneWeierstrass: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The Stone-Weierstrass approximation theorem, complex version,
that a subalgebra `A` of `C(X, ℂ)`, where `X` is a compact topological space,
is dense if it is conjugation-invariant and separates points.
-/
theorem continuous_map.subalgebra_complex_topological_closure_eq_top_of_separates_points
(A : subalgebra exprℂ() «exprC( , )»(X, exprℂ()))
(hA : A.separates_points)
(hA' : conj_invariant_subalgebra (A.restrict_scalars exprℝ())) : «expr = »(A.topological_closure, «expr⊤»()) :=
begin
  rw [expr algebra.eq_top_iff] [],
  let [ident I] [":", expr «expr →ₗ[ ] »(«exprC( , )»(X, exprℝ()), exprℝ(), «exprC( , )»(X, exprℂ()))] [":=", expr of_real_clm.comp_left_continuous exprℝ() X],
  have [ident key] [":", expr «expr ≤ »(I.range, (A.to_submodule.restrict_scalars exprℝ()).topological_closure)] [],
  { let [ident A₀] [":", expr submodule exprℝ() «exprC( , )»(X, exprℝ())] [":=", expr (A.to_submodule.restrict_scalars exprℝ()).comap I],
    have [ident SW] [":", expr «expr = »(A₀.topological_closure, «expr⊤»())] [],
    { have [] [] [":=", expr subalgebra_topological_closure_eq_top_of_separates_points _ (hA.complex_to_real hA')],
      exact [expr congr_arg subalgebra.to_submodule this] },
    rw ["[", "<-", expr submodule.map_top, ",", "<-", expr SW, "]"] [],
    have [ident h₁] [] [":=", expr A₀.topological_closure_map (of_real_clm.comp_left_continuous_compact X)],
    have [ident h₂] [] [":=", expr (A.to_submodule.restrict_scalars exprℝ()).map_comap_le I],
    exact [expr h₁.trans (submodule.topological_closure_mono h₂)] },
  intros [ident f],
  let [ident f_re] [":", expr «exprC( , )»(X, exprℝ())] [":=", expr (⟨complex.re, complex.re_clm.continuous⟩ : «exprC( , )»(exprℂ(), exprℝ())).comp f],
  let [ident f_im] [":", expr «exprC( , )»(X, exprℝ())] [":=", expr (⟨complex.im, complex.im_clm.continuous⟩ : «exprC( , )»(exprℂ(), exprℝ())).comp f],
  have [ident h_f_re] [":", expr «expr ∈ »(I f_re, A.topological_closure)] [":=", expr key ⟨f_re, rfl⟩],
  have [ident h_f_im] [":", expr «expr ∈ »(I f_im, A.topological_closure)] [":=", expr key ⟨f_im, rfl⟩],
  convert [] [expr A.topological_closure.add_mem h_f_re (A.topological_closure.smul_mem h_f_im complex.I)] [],
  ext [] [] []; simp [] [] [] ["[", expr I, "]"] [] []
end

end Complex

