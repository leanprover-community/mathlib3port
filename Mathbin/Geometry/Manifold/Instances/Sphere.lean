import Mathbin.Analysis.Complex.Circle 
import Mathbin.Analysis.InnerProductSpace.Calculus 
import Mathbin.Analysis.InnerProductSpace.PiL2 
import Mathbin.Geometry.Manifold.Algebra.LieGroup 
import Mathbin.Geometry.Manifold.Instances.Real

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put a smooth manifold structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, a local homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal complement of
`v`).

For finite-dimensional `E`, we then construct a smooth manifold instance on the sphere; the charts
here are obtained by composing the local homeomorphisms `stereographic` with arbitrary isometries
from `(ℝ ∙ v)ᗮ` to Euclidean space.

We prove two lemmas about smooth maps:
* `times_cont_mdiff_coe_sphere` states that the coercion map from the sphere into `E` is smooth;
  this is a useful tool for constructing smooth maps *from* the sphere.
* `times_cont_mdiff.cod_restrict_sphere` states that a map from a manifold into the sphere is
  smooth if its lift to a map to `E` is smooth; this is a useful tool for constructing smooth maps
  *to* the sphere.

As an application we prove `times_cont_mdiff_neg_sphere`, that the antipodal map is smooth.

Finally, we equip the `circle` (defined in `analysis.complex.circle` to be the sphere in `ℂ`
centred at `0` of radius `1`) with the following structure:
* a charted space with model space `euclidean_space ℝ (fin 1)` (inherited from `metric.sphere`)
* a Lie group with model with corners `𝓡 1`

We furthermore show that `exp_map_circle` (defined in `analysis.complex.circle` to be the natural
map `λ t, exp (t * I)` from `ℝ` to `circle`) is smooth.


## Implementation notes

The model space for the charted space instance is `euclidean_space ℝ (fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[fact (finrank ℝ E = n + 1)]`.  This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type.  If one used the
naive expression `euclidean_space ℝ (fin (finrank ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `euclidean_space ℝ (fin (2 - 1))` but not with model space
`euclidean_space ℝ (fin 1)`.
-/


variable{E : Type _}[InnerProductSpace ℝ E]

noncomputable theory

open Metric FiniteDimensional

open_locale Manifold

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

section StereographicProjection

variable(v : E)

/-! ### Construction of the stereographic projection -/


/-- Stereographic projection, forward direction. This is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It is smooth away from the affine hyperplane
through `v` parallel to the orthogonal complement.  It restricts on the sphere to the stereographic
projection. -/
def stereoToFun [CompleteSpace E] (x : E) : (ℝ∙v)ᗮ :=
  (2 / ((1 : ℝ) - innerRight v x)) • orthogonalProjection (ℝ∙v)ᗮ x

variable{v}

@[simp]
theorem stereo_to_fun_apply [CompleteSpace E] (x : E) :
  stereoToFun v x = (2 / ((1 : ℝ) - innerRight v x)) • orthogonalProjection (ℝ∙v)ᗮ x :=
  rfl

theorem times_cont_diff_on_stereo_to_fun [CompleteSpace E] :
  TimesContDiffOn ℝ ⊤ (stereoToFun v) { x:E | innerRight v x ≠ (1 : ℝ) } :=
  by 
    refine' TimesContDiffOn.smul _ (orthogonalProjection (ℝ∙v)ᗮ).TimesContDiff.TimesContDiffOn 
    refine' times_cont_diff_const.times_cont_diff_on.div _ _
    ·
      exact (times_cont_diff_const.sub (innerRight v).TimesContDiff).TimesContDiffOn
    ·
      intro x h h' 
      exact h (sub_eq_zero.mp h').symm

theorem continuous_on_stereo_to_fun [CompleteSpace E] :
  ContinuousOn (stereoToFun v) { x:E | innerRight v x ≠ (1 : ℝ) } :=
  times_cont_diff_on_stereo_to_fun.ContinuousOn

variable(v)

/-- Auxiliary function for the construction of the reverse direction of the stereographic
projection.  This is a map from the orthogonal complement of a unit vector `v` in an inner product
space `E` to `E`; we will later prove that it takes values in the unit sphere.

For most purposes, use `stereo_inv_fun`, not `stereo_inv_fun_aux`. -/
def stereoInvFunAux (w : E) : E :=
  ((∥w∥^2)+4)⁻¹ • ((4 : ℝ) • w)+((∥w∥^2) - 4) • v

variable{v}

@[simp]
theorem stereo_inv_fun_aux_apply (w : E) : stereoInvFunAux v w = ((∥w∥^2)+4)⁻¹ • ((4 : ℝ) • w)+((∥w∥^2) - 4) • v :=
  rfl

-- error in Geometry.Manifold.Instances.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem stereo_inv_fun_aux_mem
(hv : «expr = »(«expr∥ ∥»(v), 1))
{w : E}
(hw : «expr ∈ »(w, «expr ᗮ»(«expr ∙ »(exprℝ(), v)))) : «expr ∈ »(stereo_inv_fun_aux v w, sphere (0 : E) 1) :=
begin
  have [ident h₁] [":", expr «expr ≤ »(0, «expr + »(«expr ^ »(«expr∥ ∥»(w), 2), 4))] [":=", expr by nlinarith [] [] []],
  suffices [] [":", expr «expr = »(«expr∥ ∥»(«expr + »(«expr • »((4 : exprℝ()), w), «expr • »(«expr - »(«expr ^ »(«expr∥ ∥»(w), 2), 4), v))), «expr + »(«expr ^ »(«expr∥ ∥»(w), 2), 4))],
  { have [ident h₂] [":", expr «expr ≠ »(«expr + »(«expr ^ »(«expr∥ ∥»(w), 2), 4), 0)] [":=", expr by nlinarith [] [] []],
    simp [] [] ["only"] ["[", expr mem_sphere_zero_iff_norm, ",", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_inv, ",", expr this, ",", expr abs_of_nonneg h₁, ",", expr stereo_inv_fun_aux_apply, "]"] [] [],
    field_simp [] [] [] [] },
  suffices [] [":", expr «expr = »(«expr ^ »(«expr∥ ∥»(«expr + »(«expr • »((4 : exprℝ()), w), «expr • »(«expr - »(«expr ^ »(«expr∥ ∥»(w), 2), 4), v))), 2), «expr ^ »(«expr + »(«expr ^ »(«expr∥ ∥»(w), 2), 4), 2))],
  { have [ident h₃] [":", expr «expr ≤ »(0, «expr∥ ∥»(stereo_inv_fun_aux v w))] [":=", expr norm_nonneg _],
    simpa [] [] [] ["[", expr h₁, ",", expr h₃, ",", "-", ident one_pow, "]"] [] ["using", expr this] },
  simp [] [] [] ["[", expr norm_add_sq_real, ",", expr norm_smul, ",", expr inner_smul_left, ",", expr inner_smul_right, ",", expr inner_left_of_mem_orthogonal_singleton _ hw, ",", expr mul_pow, ",", expr real.norm_eq_abs, ",", expr hv, "]"] [] [],
  ring []
end

-- error in Geometry.Manifold.Instances.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem times_cont_diff_stereo_inv_fun_aux : times_cont_diff exprℝ() «expr⊤»() (stereo_inv_fun_aux v) :=
begin
  have [ident h₀] [":", expr times_cont_diff exprℝ() «expr⊤»() (λ
    w : E, «expr ^ »(«expr∥ ∥»(w), 2))] [":=", expr times_cont_diff_norm_sq],
  have [ident h₁] [":", expr times_cont_diff exprℝ() «expr⊤»() (λ
    w : E, «expr ⁻¹»(«expr + »(«expr ^ »(«expr∥ ∥»(w), 2), 4)))] [],
  { refine [expr (h₀.add times_cont_diff_const).inv _],
    intros [ident x],
    nlinarith [] [] [] },
  have [ident h₂] [":", expr times_cont_diff exprℝ() «expr⊤»() (λ
    w, «expr + »(«expr • »((4 : exprℝ()), w), «expr • »(«expr - »(«expr ^ »(«expr∥ ∥»(w), 2), 4), v)))] [],
  { refine [expr (times_cont_diff_const.smul times_cont_diff_id).add _],
    refine [expr (h₀.sub times_cont_diff_const).smul times_cont_diff_const] },
  exact [expr h₁.smul h₂]
end

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
def stereoInvFun (hv : ∥v∥ = 1) (w : (ℝ∙v)ᗮ) : sphere (0 : E) 1 :=
  ⟨stereoInvFunAux v (w : E), stereo_inv_fun_aux_mem hv w.2⟩

@[simp]
theorem stereo_inv_fun_apply (hv : ∥v∥ = 1) (w : (ℝ∙v)ᗮ) :
  (stereoInvFun hv w : E) = ((∥w∥^2)+4)⁻¹ • ((4 : ℝ) • w)+((∥w∥^2) - 4) • v :=
  rfl

-- error in Geometry.Manifold.Instances.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem stereo_inv_fun_ne_north_pole
(hv : «expr = »(«expr∥ ∥»(v), 1))
(w : «expr ᗮ»(«expr ∙ »(exprℝ(), v))) : «expr ≠ »(stereo_inv_fun hv w, (⟨v, by simp [] [] [] ["[", expr hv, "]"] [] []⟩ : sphere (0 : E) 1)) :=
begin
  refine [expr subtype.ne_of_val_ne _],
  rw ["<-", expr inner_lt_one_iff_real_of_norm_one _ hv] [],
  { have [ident hw] [":", expr «expr = »(«expr⟪ , ⟫_ℝ»(v, w), 0)] [":=", expr inner_right_of_mem_orthogonal_singleton v w.2],
    have [ident hw'] [":", expr «expr < »(«expr * »(«expr ⁻¹»(«expr + »(«expr ^ »(«expr∥ ∥»((w : E)), 2), 4)), «expr - »(«expr ^ »(«expr∥ ∥»((w : E)), 2), 4)), 1)] [],
    { refine [expr (inv_mul_lt_iff' _).mpr _],
      { nlinarith [] [] [] },
      linarith [] [] [] },
    simpa [] [] [] ["[", expr real_inner_comm, ",", expr inner_add_right, ",", expr inner_smul_right, ",", expr real_inner_self_eq_norm_mul_norm, ",", expr hw, ",", expr hv, "]"] [] ["using", expr hw'] },
  { simpa [] [] [] [] [] ["using", expr stereo_inv_fun_aux_mem hv w.2] }
end

theorem continuous_stereo_inv_fun (hv : ∥v∥ = 1) : Continuous (stereoInvFun hv) :=
  continuous_induced_rng (times_cont_diff_stereo_inv_fun_aux.Continuous.comp continuous_subtype_coe)

variable[CompleteSpace E]

-- error in Geometry.Manifold.Instances.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem stereo_left_inv
(hv : «expr = »(«expr∥ ∥»(v), 1))
{x : sphere (0 : E) 1}
(hx : «expr ≠ »((x : E), v)) : «expr = »(stereo_inv_fun hv (stereo_to_fun v x), x) :=
begin
  ext [] [] [],
  simp [] [] ["only"] ["[", expr stereo_to_fun_apply, ",", expr stereo_inv_fun_apply, ",", expr smul_add, "]"] [] [],
  set [] [ident a] [":", expr exprℝ()] [":="] [expr inner_right v x] [],
  set [] [ident y] [] [":="] [expr orthogonal_projection «expr ᗮ»(«expr ∙ »(exprℝ(), v)) x] [],
  have [ident split] [":", expr «expr = »(«expr↑ »(x), «expr + »(«expr • »(a, v), «expr↑ »(y)))] [],
  { convert [] [expr eq_sum_orthogonal_projection_self_orthogonal_complement «expr ∙ »(exprℝ(), v) x] [],
    exact [expr (orthogonal_projection_unit_singleton exprℝ() hv x).symm] },
  have [ident hvy] [":", expr «expr = »(«expr⟪ , ⟫_ℝ»(v, y), 0)] [":=", expr inner_right_of_mem_orthogonal_singleton v y.2],
  have [ident pythag] [":", expr «expr = »(1, «expr + »(«expr ^ »(a, 2), «expr ^ »(«expr∥ ∥»(y), 2)))] [],
  { have [ident hvy'] [":", expr «expr = »(«expr⟪ , ⟫_ℝ»(«expr • »(a, v), y), 0)] [":=", expr by simp [] [] [] ["[", expr inner_smul_left, ",", expr hvy, "]"] [] []],
    convert [] [expr norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hvy'] ["using", 2],
    { simp [] [] [] ["[", "<-", expr split, "]"] [] [] },
    { simp [] [] [] ["[", expr norm_smul, ",", expr hv, ",", expr real.norm_eq_abs, ",", "<-", expr sq, ",", expr sq_abs, "]"] [] [] },
    { exact [expr sq _] } },
  have [ident ha] [":", expr «expr ≠ »(«expr - »(1, a), 0)] [],
  { have [] [":", expr «expr < »(a, 1)] [":=", expr (inner_lt_one_iff_real_of_norm_one hv (by simp [] [] [] [] [] [])).mpr hx.symm],
    linarith [] [] [] },
  have [] [":", expr «expr ≠ »(«expr + »(«expr * »(«expr ^ »(2, 2), «expr ^ »(«expr∥ ∥»(y), 2)), «expr * »(4, «expr ^ »(«expr - »(1, a), 2))), 0)] [],
  { refine [expr ne_of_gt _],
    have [] [] [":=", expr norm_nonneg (y : E)],
    have [] [":", expr «expr < »(0, «expr ^ »(«expr - »(1, a), 2))] [":=", expr sq_pos_of_ne_zero «expr - »(1, a) ha],
    nlinarith [] [] [] },
  have [ident h₁] [":", expr «expr = »(«expr * »(«expr * »(«expr ⁻¹»(«expr + »(«expr * »(«expr / »(«expr ^ »(2, 2), «expr ^ »(«expr - »(1, a), 2)), «expr ^ »(«expr∥ ∥»(y), 2)), 4)), 4), «expr / »(2, «expr - »(1, a))), 1)] [],
  { field_simp [] [] [] [],
    nlinarith [] [] [] },
  have [ident h₂] [":", expr «expr = »(«expr * »(«expr ⁻¹»(«expr + »(«expr * »(«expr / »(«expr ^ »(2, 2), «expr ^ »(«expr - »(1, a), 2)), «expr ^ »(«expr∥ ∥»(y), 2)), 4)), «expr - »(«expr * »(«expr / »(«expr ^ »(2, 2), «expr ^ »(«expr - »(1, a), 2)), «expr ^ »(«expr∥ ∥»(y), 2)), 4)), a)] [],
  { field_simp [] [] [] [],
    transitivity [expr «expr * »(«expr ^ »(«expr - »(1, a), 2), «expr * »(a, «expr + »(«expr * »(«expr ^ »(2, 2), «expr ^ »(«expr∥ ∥»(y), 2)), «expr * »(4, «expr ^ »(«expr - »(1, a), 2)))))],
    { congr,
      nlinarith [] [] [] },
    ring_nf [] [] [],
    ring [] },
  convert [] [expr congr_arg2 has_add.add (congr_arg (λ
     t, «expr • »(t, (y : E))) h₁) (congr_arg (λ t, «expr • »(t, v)) h₂)] ["using", 1],
  { simp [] [] [] ["[", expr inner_add_right, ",", expr inner_smul_right, ",", expr hvy, ",", expr real_inner_self_eq_norm_mul_norm, ",", expr hv, ",", expr mul_smul, ",", expr mul_pow, ",", expr real.norm_eq_abs, ",", expr sq_abs, ",", expr norm_smul, "]"] [] [] },
  { simp [] [] [] ["[", expr split, ",", expr add_comm, "]"] [] [] }
end

-- error in Geometry.Manifold.Instances.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem stereo_right_inv
(hv : «expr = »(«expr∥ ∥»(v), 1))
(w : «expr ᗮ»(«expr ∙ »(exprℝ(), v))) : «expr = »(stereo_to_fun v (stereo_inv_fun hv w), w) :=
begin
  have [] [":", expr «expr = »(«expr * »(«expr * »(«expr / »(2, «expr - »(1, «expr * »(«expr ⁻¹»(«expr + »(«expr ^ »(«expr∥ ∥»((w : E)), 2), 4)), «expr - »(«expr ^ »(«expr∥ ∥»((w : E)), 2), 4)))), «expr ⁻¹»(«expr + »(«expr ^ »(«expr∥ ∥»((w : E)), 2), 4))), 4), 1)] [],
  { have [] [":", expr «expr ≠ »(«expr + »(«expr ^ »(«expr∥ ∥»((w : E)), 2), 4), 0)] [":=", expr by nlinarith [] [] []],
    have [] [":", expr «expr ≠ »(«expr + »((4 : exprℝ()), 4), 0)] [":=", expr by nlinarith [] [] []],
    field_simp [] [] [] [],
    ring [] },
  convert [] [expr congr_arg (λ c, «expr • »(c, w)) this] [],
  { have [ident h₁] [":", expr «expr = »(orthogonal_projection «expr ᗮ»(«expr ∙ »(exprℝ(), v)) v, 0)] [":=", expr orthogonal_projection_orthogonal_complement_singleton_eq_zero v],
    have [ident h₂] [":", expr «expr = »(orthogonal_projection «expr ᗮ»(«expr ∙ »(exprℝ(), v)) w, w)] [":=", expr orthogonal_projection_mem_subspace_eq_self w],
    have [ident h₃] [":", expr «expr = »(inner_right v w, (0 : exprℝ()))] [":=", expr inner_right_of_mem_orthogonal_singleton v w.2],
    have [ident h₄] [":", expr «expr = »(inner_right v v, (1 : exprℝ()))] [":=", expr by simp [] [] [] ["[", expr real_inner_self_eq_norm_mul_norm, ",", expr hv, "]"] [] []],
    simp [] [] [] ["[", expr h₁, ",", expr h₂, ",", expr h₃, ",", expr h₄, ",", expr continuous_linear_map.map_add, ",", expr continuous_linear_map.map_smul, ",", expr mul_smul, "]"] [] [] },
  { simp [] [] [] [] [] [] }
end

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`; this
is the version as a local homeomorphism. -/
def stereographic (hv : ∥v∥ = 1) : LocalHomeomorph (sphere (0 : E) 1) (ℝ∙v)ᗮ :=
  { toFun := stereoToFun v ∘ coeₓ, invFun := stereoInvFun hv,
    Source :=
      «expr ᶜ»
        {⟨v,
            by 
              simp [hv]⟩},
    Target := Set.Univ,
    map_source' :=
      by 
        simp ,
    map_target' := fun w _ => stereo_inv_fun_ne_north_pole hv w,
    left_inv' := fun _ hx => stereo_left_inv hv fun h => hx (Subtype.ext h),
    right_inv' := fun w _ => stereo_right_inv hv w, open_source := is_open_compl_singleton, open_target := is_open_univ,
    continuous_to_fun :=
      continuous_on_stereo_to_fun.comp continuous_subtype_coe.ContinuousOn
        fun w h =>
          h ∘
            Subtype.ext ∘
              Eq.symm ∘
                (inner_eq_norm_mul_iff_of_norm_one hv
                    (by 
                      simp )).mp,
    continuous_inv_fun := (continuous_stereo_inv_fun hv).ContinuousOn }

@[simp]
theorem stereographic_source (hv : ∥v∥ = 1) :
  (stereographic hv).Source =
    «expr ᶜ»
      {⟨v,
          by 
            simp [hv]⟩} :=
  rfl

@[simp]
theorem stereographic_target (hv : ∥v∥ = 1) : (stereographic hv).Target = Set.Univ :=
  rfl

end StereographicProjection

section ChartedSpace

/-!
### Charted space structure on the sphere

In this section we construct a charted space structure on the unit sphere in a finite-dimensional
real inner product space `E`; that is, we show that it is locally homeomorphic to the Euclidean
space of dimension one less than `E`.

The restriction to finite dimension is for convenience.  The most natural `charted_space`
structure for the sphere uses the stereographic projection from the antipodes of a point as the
canonical chart at this point.  However, the codomain of the stereographic projection constructed
in the previous section is `(ℝ ∙ v)ᗮ`, the orthogonal complement of the vector `v` in `E` which is
the "north pole" of the projection, so a priori these charts all have different codomains.

So it is necessary to prove that these codomains are all continuously linearly equivalent to a
fixed normed space.  This could be proved in general by a simple case of Gram-Schmidt
orthogonalization, but in the finite-dimensional case it follows more easily by dimension-counting.
-/


/-- Variant of the stereographic projection, for the sphere in an `n + 1`-dimensional inner product
space `E`.  This version has codomain the Euclidean space of dimension `n`, and is obtained by
composing the original sterographic projection (`stereographic`) with an arbitrary linear isometry
from `(ℝ ∙ v)ᗮ` to the Euclidean space. -/
def stereographic' (n : ℕ) [Fact (finrank ℝ E = n+1)] (v : sphere (0 : E) 1) :
  LocalHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Finₓ n)) :=
  stereographic (norm_eq_of_mem_sphere v) ≫ₕ
    (LinearIsometryEquiv.fromOrthogonalSpanSingleton n (nonzero_of_mem_unit_sphere v)).toHomeomorph.toLocalHomeomorph

@[simp]
theorem stereographic'_source {n : ℕ} [Fact (finrank ℝ E = n+1)] (v : sphere (0 : E) 1) :
  (stereographic' n v).Source = «expr ᶜ» {v} :=
  by 
    simp [stereographic']

@[simp]
theorem stereographic'_target {n : ℕ} [Fact (finrank ℝ E = n+1)] (v : sphere (0 : E) 1) :
  (stereographic' n v).Target = Set.Univ :=
  by 
    simp [stereographic']

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a charted space
modelled on the Euclidean space of dimension `n`. -/
instance  {n : ℕ} [Fact (finrank ℝ E = n+1)] : ChartedSpace (EuclideanSpace ℝ (Finₓ n)) (sphere (0 : E) 1) :=
  { Atlas := { f | ∃ v : sphere (0 : E) 1, f = stereographic' n v }, chartAt := fun v => stereographic' n (-v),
    mem_chart_source :=
      fun v =>
        by 
          simpa using ne_neg_of_mem_unit_sphere ℝ v,
    chart_mem_atlas := fun v => ⟨-v, rfl⟩ }

end ChartedSpace

section SmoothManifold

/-! ### Smooth manifold structure on the sphere -/


-- error in Geometry.Manifold.Instances.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a smooth manifold,
modelled on the Euclidean space of dimension `n`. -/
instance
{n : exprℕ()}
[fact «expr = »(finrank exprℝ() E, «expr + »(n, 1))] : smooth_manifold_with_corners «expr𝓡 »(n) (sphere (0 : E) 1) :=
smooth_manifold_with_corners_of_times_cont_diff_on «expr𝓡 »(n) (sphere (0 : E) 1) (begin
   rintros ["_", "_", "⟨", ident v, ",", ident rfl, "⟩", "⟨", ident v', ",", ident rfl, "⟩"],
   let [ident U] [":", expr «expr ≃ₗᵢ[ ] »(«expr ᗮ»(«expr ∙ »(exprℝ(), (v : E))), exprℝ(), euclidean_space exprℝ() (fin n))] [":=", expr linear_isometry_equiv.from_orthogonal_span_singleton n (nonzero_of_mem_unit_sphere v)],
   let [ident U'] [":", expr «expr ≃ₗᵢ[ ] »(«expr ᗮ»(«expr ∙ »(exprℝ(), (v' : E))), exprℝ(), euclidean_space exprℝ() (fin n))] [":=", expr linear_isometry_equiv.from_orthogonal_span_singleton n (nonzero_of_mem_unit_sphere v')],
   have [ident hUv] [":", expr «expr = »(stereographic' n v, «expr ≫ₕ »(stereographic (norm_eq_of_mem_sphere v), U.to_homeomorph.to_local_homeomorph))] [":=", expr rfl],
   have [ident hU'v'] [":", expr «expr = »(stereographic' n v', (stereographic (norm_eq_of_mem_sphere v')).trans U'.to_homeomorph.to_local_homeomorph)] [":=", expr rfl],
   have [ident H₁] [] [":=", expr U'.times_cont_diff.comp_times_cont_diff_on times_cont_diff_on_stereo_to_fun],
   have [ident H₂] [] [":=", expr (times_cont_diff_stereo_inv_fun_aux.comp «expr ᗮ»(«expr ∙ »(exprℝ(), (v : E))).subtypeL.times_cont_diff).comp U.symm.times_cont_diff],
   convert [] [expr H₁.comp' (H₂.times_cont_diff_on : times_cont_diff_on exprℝ() «expr⊤»() _ set.univ)] ["using", 1],
   have [ident h_set] [":", expr ∀
    p : sphere (0 : E) 1, «expr ↔ »(«expr = »(p, v'), «expr = »(«expr⟪ , ⟫_ℝ»((p : E), v'), 1))] [],
   { simp [] [] [] ["[", expr subtype.ext_iff, ",", expr inner_eq_norm_mul_iff_of_norm_one, "]"] [] [] },
   ext [] [] [],
   simp [] [] [] ["[", expr h_set, ",", expr hUv, ",", expr hU'v', ",", expr stereographic, ",", expr real_inner_comm, "]"] [] []
 end)

/-- The inclusion map (i.e., `coe`) from the sphere in `E` to `E` is smooth.  -/
theorem times_cont_mdiff_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n+1)] :
  TimesContMdiff (𝓡 n) 𝓘(ℝ, E) ∞ (coeₓ : sphere (0 : E) 1 → E) :=
  by 
    rw [times_cont_mdiff_iff]
    split 
    ·
      exact continuous_subtype_coe
    ·
      intro v _ 
      let U : (ℝ∙(-v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Finₓ n) :=
        LinearIsometryEquiv.fromOrthogonalSpanSingleton n (nonzero_of_mem_unit_sphere (-v))
      exact
        ((times_cont_diff_stereo_inv_fun_aux.comp (ℝ∙(-v : E))ᗮ.subtypeL.TimesContDiff).comp
            U.symm.times_cont_diff).TimesContDiffOn

variable{F : Type _}[NormedGroup F][NormedSpace ℝ F]

variable{H : Type _}[TopologicalSpace H]{I : ModelWithCorners ℝ F H}

variable{M : Type _}[TopologicalSpace M][ChartedSpace H M][SmoothManifoldWithCorners I M]

-- error in Geometry.Manifold.Instances.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a `times_cont_mdiff` function `f : M → E`, where `M` is some manifold, takes values in the
sphere, then it restricts to a `times_cont_mdiff` function from `M` to the sphere. -/
theorem times_cont_mdiff.cod_restrict_sphere
{n : exprℕ()}
[fact «expr = »(finrank exprℝ() E, «expr + »(n, 1))]
{m : with_top exprℕ()}
{f : M → E}
(hf : times_cont_mdiff I «expr𝓘( , )»(exprℝ(), E) m f)
(hf' : ∀
 x, «expr ∈ »(f x, sphere (0 : E) 1)) : times_cont_mdiff I «expr𝓡 »(n) m (set.cod_restrict _ _ hf' : M → sphere (0 : E) 1) :=
begin
  rw [expr times_cont_mdiff_iff_target] [],
  refine [expr ⟨continuous_induced_rng hf.continuous, _⟩],
  intros [ident v],
  let [ident U] [":", expr «expr ≃ₗᵢ[ ] »(«expr ᗮ»(«expr ∙ »(exprℝ(), («expr- »(v) : E))), exprℝ(), euclidean_space exprℝ() (fin n))] [":=", expr linear_isometry_equiv.from_orthogonal_span_singleton n (nonzero_of_mem_unit_sphere «expr- »(v))],
  have [ident h] [":", expr times_cont_diff_on exprℝ() «expr⊤»() U set.univ] [":=", expr U.times_cont_diff.times_cont_diff_on],
  have [ident H₁] [] [":=", expr (h.comp' times_cont_diff_on_stereo_to_fun).times_cont_mdiff_on],
  have [ident H₂] [":", expr times_cont_mdiff_on _ _ _ _ set.univ] [":=", expr hf.times_cont_mdiff_on],
  convert [] [expr (H₁.of_le le_top).comp' H₂] ["using", 1],
  ext [] [ident x] [],
  have [ident hfxv] [":", expr «expr ↔ »(«expr = »(f x, «expr- »(«expr↑ »(v))), «expr = »(«expr⟪ , ⟫_ℝ»(f x, «expr- »(«expr↑ »(v))), 1))] [],
  { have [ident hfx] [":", expr «expr = »(«expr∥ ∥»(f x), 1)] [":=", expr by simpa [] [] [] [] [] ["using", expr hf' x]],
    rw [expr inner_eq_norm_mul_iff_of_norm_one hfx] [],
    exact [expr norm_eq_of_mem_sphere «expr- »(v)] },
  dsimp [] ["[", expr chart_at, "]"] [] [],
  simp [] [] [] ["[", expr not_iff_not, ",", expr subtype.ext_iff, ",", expr hfxv, ",", expr real_inner_comm, "]"] [] []
end

/-- The antipodal map is smooth. -/
theorem times_cont_mdiff_neg_sphere {n : ℕ} [Fact (finrank ℝ E = n+1)] :
  TimesContMdiff (𝓡 n) (𝓡 n) ∞ fun x : sphere (0 : E) 1 => -x :=
  (times_cont_diff_neg.TimesContMdiff.comp times_cont_mdiff_coe_sphere).cod_restrict_sphere _

end SmoothManifold

section circle

open Complex

attribute [local instance] finrank_real_complex_fact

/-- The unit circle in `ℂ` is a charted space modelled on `euclidean_space ℝ (fin 1)`.  This
follows by definition from the corresponding result for `metric.sphere`. -/
instance  : ChartedSpace (EuclideanSpace ℝ (Finₓ 1)) circle :=
  Metric.Sphere.chartedSpace

instance  : SmoothManifoldWithCorners (𝓡 1) circle :=
  Metric.Sphere.smooth_manifold_with_corners

-- error in Geometry.Manifold.Instances.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The unit circle in `ℂ` is a Lie group. -/ instance : lie_group «expr𝓡 »(1) circle :=
{ smooth_mul := begin
    let [ident c] [":", expr circle → exprℂ()] [":=", expr coe],
    have [ident h₁] [":", expr times_cont_mdiff _ _ _ (prod.map c c)] [":=", expr times_cont_mdiff_coe_sphere.prod_map times_cont_mdiff_coe_sphere],
    have [ident h₂] [":", expr times_cont_mdiff («expr𝓘( , )»(exprℝ(), exprℂ()).prod «expr𝓘( , )»(exprℝ(), exprℂ())) «expr𝓘( , )»(exprℝ(), exprℂ()) «expr∞»() (λ
      z : «expr × »(exprℂ(), exprℂ()), «expr * »(z.fst, z.snd))] [],
    { rw [expr times_cont_mdiff_iff] [],
      exact [expr ⟨continuous_mul, λ x y, (times_cont_diff_mul.restrict_scalars exprℝ()).times_cont_diff_on⟩] },
    exact [expr (h₂.comp h₁).cod_restrict_sphere _]
  end,
  smooth_inv := (complex.conj_cle.times_cont_diff.times_cont_mdiff.comp times_cont_mdiff_coe_sphere).cod_restrict_sphere _,
  ..metric.sphere.smooth_manifold_with_corners }

/-- The map `λ t, exp (t * I)` from `ℝ` to the unit circle in `ℂ` is smooth. -/
theorem times_cont_mdiff_exp_map_circle : TimesContMdiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ expMapCircle :=
  ((times_cont_diff_exp.restrictScalars ℝ).comp
          (times_cont_diff_id.smul times_cont_diff_const)).TimesContMdiff.cod_restrict_sphere
    _

end circle

