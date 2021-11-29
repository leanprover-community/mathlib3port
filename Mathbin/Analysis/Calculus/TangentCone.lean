import Mathbin.Analysis.Convex.Basic 
import Mathbin.Analysis.SpecificLimits

/-!
# Tangent cone

In this file, we define two predicates `unique_diff_within_at 𝕜 s x` and `unique_diff_on 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangent_cone_at`,
and express `unique_diff_within_at` and `unique_diff_on` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `unique_diff_within_at` and `unique_diff_on` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `fderiv.lean`. Hence, derivatives are not defined yet. The
property of uniqueness of the derivative is therefore proved in `fderiv.lean`, but based on the
properties of the tangent cone we prove here.
-/


variable (𝕜 : Type _) [NondiscreteNormedField 𝕜]

open Filter Set

open_locale TopologicalSpace

section TangentCone

variable {E : Type _} [AddCommMonoidₓ E] [Module 𝕜 E] [TopologicalSpace E]

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def TangentConeAt (s : Set E) (x : E) : Set E :=
  { y:E |
    ∃ (c : ℕ → 𝕜)(d : ℕ → E),
      (∀ᶠn in at_top, (x+d n) ∈ s) ∧
        tendsto (fun n => ∥c n∥) at_top at_top ∧ tendsto (fun n => c n • d n) at_top (𝓝 y) }

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `unique_diff_within_at.eq` in `fderiv.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional).
 -/
@[mkIff]
structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where 
  dense_tangent_cone : Dense (Submodule.span 𝕜 (TangentConeAt 𝕜 s x) : Set E)
  mem_closure : x ∈ Closure s

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space.  The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `unique_diff_on.eq` in
`fderiv.lean`. -/
def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x _ : x ∈ s, UniqueDiffWithinAt 𝕜 s x

end TangentCone

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F]

variable {G : Type _} [NormedGroup G] [NormedSpace ℝ G]

variable {𝕜} {x y : E} {s t : Set E}

section TangentCone

open NormedField

-- error in Analysis.Calculus.TangentCone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tangent_cone_univ : «expr = »(tangent_cone_at 𝕜 univ x, univ) :=
begin
  refine [expr univ_subset_iff.1 (λ y hy, _)],
  rcases [expr exists_one_lt_norm 𝕜, "with", "⟨", ident w, ",", ident hw, "⟩"],
  refine [expr ⟨λ
    n, «expr ^ »(w, n), λ n, «expr • »(«expr ⁻¹»(«expr ^ »(w, n)), y), univ_mem' (λ n, mem_univ _), _, _⟩],
  { simp [] [] ["only"] ["[", expr norm_pow, "]"] [] [],
    exact [expr tendsto_pow_at_top_at_top_of_one_lt hw] },
  { convert [] [expr tendsto_const_nhds] [],
    ext [] [ident n] [],
    have [] [":", expr «expr = »(«expr * »(«expr ^ »(w, n), «expr ⁻¹»(«expr ^ »(w, n))), 1)] [],
    { apply [expr mul_inv_cancel],
      apply [expr pow_ne_zero],
      simpa [] [] [] ["[", expr norm_eq_zero, "]"] [] ["using", expr (ne_of_lt (lt_trans zero_lt_one hw)).symm] },
    rw ["[", expr smul_smul, ",", expr this, ",", expr one_smul, "]"] [] }
end

theorem tangent_cone_mono (h : s ⊆ t) : TangentConeAt 𝕜 s x ⊆ TangentConeAt 𝕜 t x :=
  by 
    rintro y ⟨c, d, ds, ctop, clim⟩
    exact ⟨c, d, mem_of_superset ds fun n hn => h hn, ctop, clim⟩

-- error in Analysis.Calculus.TangentCone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
theorem tangent_cone_at.lim_zero
{α : Type*}
(l : filter α)
{c : α → 𝕜}
{d : α → E}
(hc : tendsto (λ n, «expr∥ ∥»(c n)) l at_top)
(hd : tendsto (λ n, «expr • »(c n, d n)) l (expr𝓝() y)) : tendsto d l (expr𝓝() 0) :=
begin
  have [ident A] [":", expr tendsto (λ
    n, «expr ⁻¹»(«expr∥ ∥»(c n))) l (expr𝓝() 0)] [":=", expr tendsto_inv_at_top_zero.comp hc],
  have [ident B] [":", expr tendsto (λ
    n, «expr∥ ∥»(«expr • »(c n, d n))) l (expr𝓝() «expr∥ ∥»(y))] [":=", expr (continuous_norm.tendsto _).comp hd],
  have [ident C] [":", expr tendsto (λ
    n, «expr * »(«expr ⁻¹»(«expr∥ ∥»(c n)), «expr∥ ∥»(«expr • »(c n, d n)))) l (expr𝓝() «expr * »(0, «expr∥ ∥»(y)))] [":=", expr A.mul B],
  rw [expr zero_mul] ["at", ident C],
  have [] [":", expr «expr∀ᶠ in , »((n), l, «expr = »(«expr * »(«expr ⁻¹»(«expr∥ ∥»(c n)), «expr∥ ∥»(«expr • »(c n, d n))), «expr∥ ∥»(d n)))] [],
  { apply [expr (eventually_ne_of_tendsto_norm_at_top hc 0).mono (λ n hn, _)],
    rw ["[", expr norm_smul, ",", "<-", expr mul_assoc, ",", expr inv_mul_cancel, ",", expr one_mul, "]"] [],
    rwa ["[", expr ne.def, ",", expr norm_eq_zero, "]"] [] },
  have [ident D] [":", expr tendsto (λ n, «expr∥ ∥»(d n)) l (expr𝓝() 0)] [":=", expr tendsto.congr' this C],
  rw [expr tendsto_zero_iff_norm_tendsto_zero] [],
  exact [expr D]
end

theorem tangent_cone_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) : TangentConeAt 𝕜 s x ⊆ TangentConeAt 𝕜 t x :=
  by 
    rintro y ⟨c, d, ds, ctop, clim⟩
    refine' ⟨c, d, _, ctop, clim⟩
    suffices  : tendsto (fun n => x+d n) at_top (𝓝[t] x)
    exact tendsto_principal.1 (tendsto_inf.1 this).2
    refine' (tendsto_inf.2 ⟨_, tendsto_principal.2 ds⟩).mono_right h 
    simpa only [add_zeroₓ] using tendsto_const_nhds.add (TangentConeAt.lim_zero at_top ctop clim)

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
theorem tangent_cone_congr (h : 𝓝[s] x = 𝓝[t] x) : TangentConeAt 𝕜 s x = TangentConeAt 𝕜 t x :=
  subset.antisymm (tangent_cone_mono_nhds$ le_of_eqₓ h) (tangent_cone_mono_nhds$ le_of_eqₓ h.symm)

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
theorem tangent_cone_inter_nhds (ht : t ∈ 𝓝 x) : TangentConeAt 𝕜 (s ∩ t) x = TangentConeAt 𝕜 s x :=
  tangent_cone_congr (nhds_within_restrict' _ ht).symm

-- error in Analysis.Calculus.TangentCone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The tangent cone of a product contains the tangent cone of its left factor. -/
theorem subset_tangent_cone_prod_left
{t : set F}
{y : F}
(ht : «expr ∈ »(y, closure t)) : «expr ⊆ »(«expr '' »(linear_map.inl 𝕜 E F, tangent_cone_at 𝕜 s x), tangent_cone_at 𝕜 (set.prod s t) (x, y)) :=
begin
  rintros ["_", "⟨", ident v, ",", "⟨", ident c, ",", ident d, ",", ident hd, ",", ident hc, ",", ident hy, "⟩", ",", ident rfl, "⟩"],
  have [] [":", expr ∀
   n, «expr∃ , »((d'), «expr ∧ »(«expr ∈ »(«expr + »(y, d'), t), «expr < »(«expr∥ ∥»(«expr • »(c n, d')), «expr ^ »(«expr / »((1 : exprℝ()), 2), n))))] [],
  { assume [binders (n)],
    rcases [expr mem_closure_iff_nhds.1 ht _ (eventually_nhds_norm_smul_sub_lt (c n) y (pow_pos one_half_pos n)), "with", "⟨", ident z, ",", ident hz, ",", ident hzt, "⟩"],
    exact [expr ⟨«expr - »(z, y), by simpa [] [] [] [] [] ["using", expr hzt], by simpa [] [] [] [] [] ["using", expr hz]⟩] },
  choose [] [ident d'] [ident hd'] ["using", expr this],
  refine [expr ⟨c, λ n, (d n, d' n), _, hc, _⟩],
  show [expr «expr∀ᶠ in , »((n), at_top, «expr ∈ »(«expr + »((x, y), (d n, d' n)), set.prod s t))],
  { filter_upwards ["[", expr hd, "]"] [],
    assume [binders (n hn)],
    simp [] [] [] ["[", expr hn, ",", expr (hd' n).1, "]"] [] [] },
  { apply [expr tendsto.prod_mk_nhds hy _],
    refine [expr squeeze_zero_norm (λ n, (hd' n).2.le) _],
    exact [expr tendsto_pow_at_top_nhds_0_of_lt_1 one_half_pos.le one_half_lt_one] }
end

-- error in Analysis.Calculus.TangentCone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The tangent cone of a product contains the tangent cone of its right factor. -/
theorem subset_tangent_cone_prod_right
{t : set F}
{y : F}
(hs : «expr ∈ »(x, closure s)) : «expr ⊆ »(«expr '' »(linear_map.inr 𝕜 E F, tangent_cone_at 𝕜 t y), tangent_cone_at 𝕜 (set.prod s t) (x, y)) :=
begin
  rintros ["_", "⟨", ident w, ",", "⟨", ident c, ",", ident d, ",", ident hd, ",", ident hc, ",", ident hy, "⟩", ",", ident rfl, "⟩"],
  have [] [":", expr ∀
   n, «expr∃ , »((d'), «expr ∧ »(«expr ∈ »(«expr + »(x, d'), s), «expr < »(«expr∥ ∥»(«expr • »(c n, d')), «expr ^ »(«expr / »((1 : exprℝ()), 2), n))))] [],
  { assume [binders (n)],
    rcases [expr mem_closure_iff_nhds.1 hs _ (eventually_nhds_norm_smul_sub_lt (c n) x (pow_pos one_half_pos n)), "with", "⟨", ident z, ",", ident hz, ",", ident hzs, "⟩"],
    exact [expr ⟨«expr - »(z, x), by simpa [] [] [] [] [] ["using", expr hzs], by simpa [] [] [] [] [] ["using", expr hz]⟩] },
  choose [] [ident d'] [ident hd'] ["using", expr this],
  refine [expr ⟨c, λ n, (d' n, d n), _, hc, _⟩],
  show [expr «expr∀ᶠ in , »((n), at_top, «expr ∈ »(«expr + »((x, y), (d' n, d n)), set.prod s t))],
  { filter_upwards ["[", expr hd, "]"] [],
    assume [binders (n hn)],
    simp [] [] [] ["[", expr hn, ",", expr (hd' n).1, "]"] [] [] },
  { apply [expr tendsto.prod_mk_nhds _ hy],
    refine [expr squeeze_zero_norm (λ n, (hd' n).2.le) _],
    exact [expr tendsto_pow_at_top_nhds_0_of_lt_1 one_half_pos.le one_half_lt_one] }
end

-- error in Analysis.Calculus.TangentCone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The tangent cone of a product contains the tangent cone of each factor. -/
theorem maps_to_tangent_cone_pi
{ι : Type*}
[decidable_eq ι]
{E : ι → Type*}
[∀ i, normed_group (E i)]
[∀ i, normed_space 𝕜 (E i)]
{s : ∀ i, set (E i)}
{x : ∀ i, E i}
{i : ι}
(hi : ∀
 j «expr ≠ » i, «expr ∈ »(x j, closure (s j))) : maps_to (linear_map.single i : «expr →ₗ[ ] »(E i, 𝕜, ∀
 j, E j)) (tangent_cone_at 𝕜 (s i) (x i)) (tangent_cone_at 𝕜 (set.pi univ s) x) :=
begin
  rintros [ident w, "⟨", ident c, ",", ident d, ",", ident hd, ",", ident hc, ",", ident hy, "⟩"],
  have [] [":", expr ∀
   (n)
   (j «expr ≠ » i), «expr∃ , »((d'), «expr ∧ »(«expr ∈ »(«expr + »(x j, d'), s j), «expr < »(«expr∥ ∥»(«expr • »(c n, d')), «expr ^ »((«expr / »(1, 2) : exprℝ()), n))))] [],
  { assume [binders (n j hj)],
    rcases [expr mem_closure_iff_nhds.1 (hi j hj) _ (eventually_nhds_norm_smul_sub_lt (c n) (x j) (pow_pos one_half_pos n)), "with", "⟨", ident z, ",", ident hz, ",", ident hzs, "⟩"],
    exact [expr ⟨«expr - »(z, x j), by simpa [] [] [] [] [] ["using", expr hzs], by simpa [] [] [] [] [] ["using", expr hz]⟩] },
  choose ["!"] [ident d'] [ident hd's, ident hcd'] [],
  refine [expr ⟨c, λ
    n, function.update (d' n) i (d n), hd.mono (λ n hn j hj', _), hc, «expr $ »(tendsto_pi_nhds.2, λ j, _)⟩],
  { rcases [expr em «expr = »(j, i), "with", ident rfl, "|", ident hj]; simp [] [] [] ["*"] [] [] },
  { rcases [expr em «expr = »(j, i), "with", ident rfl, "|", ident hj],
    { simp [] [] [] ["[", expr hy, "]"] [] [] },
    { suffices [] [":", expr tendsto (λ n, «expr • »(c n, d' n j)) at_top (expr𝓝() 0)],
      by simpa [] [] [] ["[", expr hj, "]"] [] [],
      refine [expr squeeze_zero_norm (λ n, (hcd' n j hj).le) _],
      exact [expr tendsto_pow_at_top_nhds_0_of_lt_1 one_half_pos.le one_half_lt_one] } }
end

-- error in Analysis.Calculus.TangentCone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangent_cone_of_segment_subset
{s : set G}
{x y : G}
(h : «expr ⊆ »(segment exprℝ() x y, s)) : «expr ∈ »(«expr - »(y, x), tangent_cone_at exprℝ() s x) :=
begin
  let [ident c] [] [":=", expr λ n : exprℕ(), «expr ^ »((2 : exprℝ()), n)],
  let [ident d] [] [":=", expr λ n : exprℕ(), «expr • »(«expr ⁻¹»(c n), «expr - »(y, x))],
  refine [expr ⟨c, d, filter.univ_mem' (λ n, h _), _, _⟩],
  show [expr «expr ∈ »(«expr + »(x, d n), segment exprℝ() x y)],
  { rw [expr segment_eq_image] [],
    refine [expr ⟨«expr ⁻¹»(c n), ⟨_, _⟩, _⟩],
    { rw [expr inv_nonneg] [],
      apply [expr pow_nonneg],
      norm_num [] [] },
    { apply [expr inv_le_one],
      apply [expr one_le_pow_of_one_le],
      norm_num [] [] },
    { simp [] [] ["only"] ["[", expr d, ",", expr sub_smul, ",", expr smul_sub, ",", expr one_smul, "]"] [] [],
      abel [] [] [] } },
  show [expr filter.tendsto (λ n : exprℕ(), «expr∥ ∥»(c n)) filter.at_top filter.at_top],
  { have [] [":", expr «expr = »(λ n : exprℕ(), «expr∥ ∥»(c n), c)] [],
    by { ext [] [ident n] [],
      exact [expr abs_of_nonneg (pow_nonneg (by norm_num [] []) _)] },
    rw [expr this] [],
    exact [expr tendsto_pow_at_top_at_top_of_one_lt (by norm_num [] [])] },
  show [expr filter.tendsto (λ n : exprℕ(), «expr • »(c n, d n)) filter.at_top (expr𝓝() «expr - »(y, x))],
  { have [] [":", expr «expr = »(λ n : exprℕ(), «expr • »(c n, d n), λ n, «expr - »(y, x))] [],
    { ext [] [ident n] [],
      simp [] [] ["only"] ["[", expr d, ",", expr smul_smul, "]"] [] [],
      rw ["[", expr mul_inv_cancel, ",", expr one_smul, "]"] [],
      exact [expr pow_ne_zero _ (by norm_num [] [])] },
    rw [expr this] [],
    apply [expr tendsto_const_nhds] }
end

end TangentCone

section UniqueDiff

/-!
### Properties of `unique_diff_within_at` and `unique_diff_on`

This section is devoted to properties of the predicates
`unique_diff_within_at` and `unique_diff_on`. -/


theorem UniqueDiffOn.unique_diff_within_at {s : Set E} {x} (hs : UniqueDiffOn 𝕜 s) (h : x ∈ s) :
  UniqueDiffWithinAt 𝕜 s x :=
  hs x h

theorem unique_diff_within_at_univ : UniqueDiffWithinAt 𝕜 univ x :=
  by 
    rw [unique_diff_within_at_iff, tangent_cone_univ]
    simp 

theorem unique_diff_on_univ : UniqueDiffOn 𝕜 (univ : Set E) :=
  fun x hx => unique_diff_within_at_univ

theorem unique_diff_on_empty : UniqueDiffOn 𝕜 (∅ : Set E) :=
  fun x hx => hx.elim

theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x ≤ 𝓝[t] x) : UniqueDiffWithinAt 𝕜 t x :=
  by 
    simp only [unique_diff_within_at_iff] at *
    rw [mem_closure_iff_nhds_within_ne_bot] at h⊢
    exact ⟨h.1.mono$ Submodule.span_mono$ tangent_cone_mono_nhds st, h.2.mono st⟩

theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ t) : UniqueDiffWithinAt 𝕜 t x :=
  h.mono_nhds$ nhds_within_mono _ st

theorem unique_diff_within_at_congr (st : 𝓝[s] x = 𝓝[t] x) : UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x :=
  ⟨fun h => h.mono_nhds$ le_of_eqₓ st, fun h => h.mono_nhds$ le_of_eqₓ st.symm⟩

theorem unique_diff_within_at_inter (ht : t ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  unique_diff_within_at_congr$ (nhds_within_restrict' _ ht).symm

theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (unique_diff_within_at_inter ht).2 hs

theorem unique_diff_within_at_inter' (ht : t ∈ 𝓝[s] x) : UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  unique_diff_within_at_congr$ (nhds_within_restrict'' _ ht).symm

theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝[s] x) : UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (unique_diff_within_at_inter' ht).2 hs

theorem unique_diff_within_at_of_mem_nhds (h : s ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 s x :=
  by 
    simpa only [univ_inter] using unique_diff_within_at_univ.inter h

theorem IsOpen.unique_diff_within_at (hs : IsOpen s) (xs : x ∈ s) : UniqueDiffWithinAt 𝕜 s x :=
  unique_diff_within_at_of_mem_nhds (IsOpen.mem_nhds hs xs)

theorem UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 𝕜 (s ∩ t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

theorem IsOpen.unique_diff_on (hs : IsOpen s) : UniqueDiffOn 𝕜 s :=
  fun x hx => IsOpen.unique_diff_within_at hs hx

-- error in Analysis.Calculus.TangentCone: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
theorem unique_diff_within_at.prod
{t : set F}
{y : F}
(hs : unique_diff_within_at 𝕜 s x)
(ht : unique_diff_within_at 𝕜 t y) : unique_diff_within_at 𝕜 (set.prod s t) (x, y) :=
begin
  rw ["[", expr unique_diff_within_at_iff, "]"] ["at", "⊢", ident hs, ident ht],
  rw ["[", expr closure_prod_eq, "]"] [],
  refine [expr ⟨_, hs.2, ht.2⟩],
  have [] [":", expr «expr ≤ »(_, submodule.span 𝕜 (tangent_cone_at 𝕜 (s.prod t) (x, y)))] [":=", expr submodule.span_mono (union_subset (subset_tangent_cone_prod_left ht.2) (subset_tangent_cone_prod_right hs.2))],
  rw ["[", expr linear_map.span_inl_union_inr, ",", expr set_like.le_def, "]"] ["at", ident this],
  exact [expr (hs.1.prod ht.1).mono this]
end

theorem UniqueDiffWithinAt.univ_pi (ι : Type _) [Fintype ι] (E : ι → Type _) [∀ i, NormedGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i) (h : ∀ i, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
  UniqueDiffWithinAt 𝕜 (Set.Pi univ s) x :=
  by 
    classical 
    simp only [unique_diff_within_at_iff, closure_pi_set] at h⊢
    refine' ⟨(dense_pi univ fun i _ => (h i).1).mono _, fun i _ => (h i).2⟩
    normCast 
    simp only [←Submodule.supr_map_single, supr_le_iff, LinearMap.map_span, Submodule.span_le, ←maps_to']
    exact fun i => (maps_to_tangent_cone_pi$ fun j hj => (h j).2).mono subset.rfl Submodule.subset_span

theorem UniqueDiffWithinAt.pi (ι : Type _) [Fintype ι] (E : ι → Type _) [∀ i, NormedGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (x : ∀ i, E i) (I : Set ι)
  (h : ∀ i _ : i ∈ I, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.Pi I s) x :=
  by 
    classical 
    rw [←Set.univ_pi_piecewise]
    refine' UniqueDiffWithinAt.univ_pi _ _ _ _ fun i => _ 
    byCases' hi : i ∈ I <;> simp [unique_diff_within_at_univ]

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
theorem UniqueDiffOn.prod {t : Set F} (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) : UniqueDiffOn 𝕜 (Set.Prod s t) :=
  fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.pi (ι : Type _) [Fintype ι] (E : ι → Type _) [∀ i, NormedGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  (s : ∀ i, Set (E i)) (I : Set ι) (h : ∀ i _ : i ∈ I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.Pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi _ _ _ _ _$ fun i hi => h i hi (x i) (hx i hi)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.univ_pi (ι : Type _) [Fintype ι] (E : ι → Type _) [∀ i, NormedGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] (s : ∀ i, Set (E i)) (h : ∀ i, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.Pi univ s) :=
  UniqueDiffOn.pi _ _ _ _$ fun i _ => h i

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem unique_diff_on_convex {s : Set G} (conv : Convex ℝ s) (hs : (Interior s).Nonempty) : UniqueDiffOn ℝ s :=
  by 
    intro x xs 
    rcases hs with ⟨y, hy⟩
    suffices  : y - x ∈ Interior (TangentConeAt ℝ s x)
    ·
      refine' ⟨Dense.of_closure _, subset_closure xs⟩
      simp
        [(Submodule.span ℝ (TangentConeAt ℝ s x)).eq_top_of_nonempty_interior'
          ⟨y - x, interior_mono Submodule.subset_span this⟩]
    rw [mem_interior_iff_mem_nhds] at hy⊢
    apply mem_of_superset ((is_open_map_sub_right x).image_mem_nhds hy)
    rintro _ ⟨z, zs, rfl⟩
    exact mem_tangent_cone_of_segment_subset (conv.segment_subset xs zs)

theorem unique_diff_on_Ici (a : ℝ) : UniqueDiffOn ℝ (Ici a) :=
  unique_diff_on_convex (convex_Ici a)$
    by 
      simp only [interior_Ici, nonempty_Ioi]

theorem unique_diff_on_Iic (a : ℝ) : UniqueDiffOn ℝ (Iic a) :=
  unique_diff_on_convex (convex_Iic a)$
    by 
      simp only [interior_Iic, nonempty_Iio]

theorem unique_diff_on_Ioi (a : ℝ) : UniqueDiffOn ℝ (Ioi a) :=
  is_open_Ioi.UniqueDiffOn

theorem unique_diff_on_Iio (a : ℝ) : UniqueDiffOn ℝ (Iio a) :=
  is_open_Iio.UniqueDiffOn

theorem unique_diff_on_Icc {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (Icc a b) :=
  unique_diff_on_convex (convex_Icc a b)$
    by 
      simp only [interior_Icc, nonempty_Ioo, hab]

theorem unique_diff_on_Ico (a b : ℝ) : UniqueDiffOn ℝ (Ico a b) :=
  if hab : a < b then
    unique_diff_on_convex (convex_Ico a b)$
      by 
        simp only [interior_Ico, nonempty_Ioo, hab]
  else
    by 
      simp only [Ico_eq_empty hab, unique_diff_on_empty]

theorem unique_diff_on_Ioc (a b : ℝ) : UniqueDiffOn ℝ (Ioc a b) :=
  if hab : a < b then
    unique_diff_on_convex (convex_Ioc a b)$
      by 
        simp only [interior_Ioc, nonempty_Ioo, hab]
  else
    by 
      simp only [Ioc_eq_empty hab, unique_diff_on_empty]

theorem unique_diff_on_Ioo (a b : ℝ) : UniqueDiffOn ℝ (Ioo a b) :=
  is_open_Ioo.UniqueDiffOn

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
theorem unique_diff_on_Icc_zero_one : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
  unique_diff_on_Icc zero_lt_one

end UniqueDiff

