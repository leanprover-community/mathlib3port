import Mathbin.LinearAlgebra.FiniteDimensional 
import Mathbin.Geometry.Manifold.SmoothManifoldWithCorners 
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Constructing examples of manifolds over ℝ

We introduce the necessary bits to be able to define manifolds modelled over `ℝ^n`, boundaryless
or with boundary or with corners. As a concrete example, we construct explicitly the manifold with
boundary structure on the real interval `[x, y]`.

More specifically, we introduce
* `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_half_space n)` for the model space
  used to define `n`-dimensional real manifolds with boundary
* `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_quadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

## Notations

In the locale `manifold`, we introduce the notations
* `𝓡 n` for the identity model with corners on `euclidean_space ℝ (fin n)`
* `𝓡∂ n` for `model_with_corners ℝ (euclidean_space ℝ (fin n)) (euclidean_half_space n)`.

For instance, if a manifold `M` is boundaryless, smooth and modelled on `euclidean_space ℝ (fin m)`,
and `N` is smooth with boundary modelled on `euclidean_half_space n`, and `f : M → N` is a smooth
map, then the derivative of `f` can be written simply as `mfderiv (𝓡 m) (𝓡∂ n) f` (as to why the
model with corners can not be implicit, see the discussion in `smooth_manifold_with_corners.lean`).

## Implementation notes

The manifold structure on the interval `[x, y] = Icc x y` requires the assumption `x < y` as a
typeclass. We provide it as `[fact (x < y)]`.
-/


noncomputable theory

open Set Function

open_locale Manifold

attribute [local instance] fact_one_le_two_real

/--
The half-space in `ℝ^n`, used to model manifolds with boundary. We only define it when
`1 ≤ n`, as the definition only makes sense in this case.
-/
def EuclideanHalfSpace (n : ℕ) [HasZero (Finₓ n)] : Type :=
  { x : EuclideanSpace ℝ (Finₓ n) // 0 ≤ x 0 }

/--
The quadrant in `ℝ^n`, used to model manifolds with corners, made of all vectors with nonnegative
coordinates.
-/
def EuclideanQuadrant (n : ℕ) : Type :=
  { x : EuclideanSpace ℝ (Finₓ n) // ∀ i : Finₓ n, 0 ≤ x i }

section 

attribute [local reducible] EuclideanHalfSpace EuclideanQuadrant

variable {n : ℕ}

instance [HasZero (Finₓ n)] : TopologicalSpace (EuclideanHalfSpace n) :=
  by 
    infer_instance

instance : TopologicalSpace (EuclideanQuadrant n) :=
  by 
    infer_instance

instance [HasZero (Finₓ n)] : Inhabited (EuclideanHalfSpace n) :=
  ⟨⟨0, le_reflₓ _⟩⟩

instance : Inhabited (EuclideanQuadrant n) :=
  ⟨⟨0, fun i => le_reflₓ _⟩⟩

theorem range_half_space (n : ℕ) [HasZero (Finₓ n)] : (range fun x : EuclideanHalfSpace n => x.val) = { y | 0 ≤ y 0 } :=
  by 
    simp 

theorem range_quadrant (n : ℕ) : (range fun x : EuclideanQuadrant n => x.val) = { y | ∀ i : Finₓ n, 0 ≤ y i } :=
  by 
    simp 

end 

/--
Definition of the model with corners `(euclidean_space ℝ (fin n), euclidean_half_space n)`, used as
a model for manifolds with boundary. In the locale `manifold`, use the shortcut `𝓡∂ n`.
-/
def modelWithCornersEuclideanHalfSpace (n : ℕ) [HasZero (Finₓ n)] :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Finₓ n)) (EuclideanHalfSpace n) :=
  { toFun := Subtype.val,
    invFun :=
      fun x =>
        ⟨update x 0 (max (x 0) 0),
          by 
            simp [le_reflₓ]⟩,
    Source := univ, Target := { x | 0 ≤ x 0 }, map_source' := fun x hx => x.property,
    map_target' := fun x hx => mem_univ _,
    left_inv' :=
      fun ⟨xval, xprop⟩ hx =>
        by 
          rw [Subtype.mk_eq_mk, update_eq_iff]
          exact ⟨max_eq_leftₓ xprop, fun i _ => rfl⟩,
    right_inv' := fun x hx => update_eq_iff.2 ⟨max_eq_leftₓ hx, fun i _ => rfl⟩, source_eq := rfl,
    unique_diff' :=
      have this : UniqueDiffOn ℝ _ :=
        UniqueDiffOn.pi (Finₓ n) (fun _ => ℝ) _ _ fun i _ : i ∈ ({0} : Set (Finₓ n)) => unique_diff_on_Ici 0 
      by 
        simpa only [singleton_pi] using this,
    continuous_to_fun := continuous_subtype_val,
    continuous_inv_fun := continuous_subtype_mk _$ continuous_id.update 0$ (continuous_apply 0).max continuous_const }

/--
Definition of the model with corners `(euclidean_space ℝ (fin n), euclidean_quadrant n)`, used as a
model for manifolds with corners -/
def modelWithCornersEuclideanQuadrant (n : ℕ) : ModelWithCorners ℝ (EuclideanSpace ℝ (Finₓ n)) (EuclideanQuadrant n) :=
  { toFun := Subtype.val,
    invFun :=
      fun x =>
        ⟨fun i => max (x i) 0,
          fun i =>
            by 
              simp only [le_reflₓ, or_trueₓ, le_max_iff]⟩,
    Source := univ, Target := { x | ∀ i, 0 ≤ x i },
    map_source' :=
      fun x hx =>
        by 
          simpa only [Subtype.range_val] using x.property,
    map_target' := fun x hx => mem_univ _,
    left_inv' :=
      fun ⟨xval, xprop⟩ hx =>
        by 
          ext i 
          simp only [Subtype.coe_mk, xprop i, max_eq_leftₓ],
    right_inv' :=
      fun x hx =>
        by 
          ext1 i 
          simp only [hx i, max_eq_leftₓ],
    source_eq := rfl,
    unique_diff' :=
      have this : UniqueDiffOn ℝ _ := UniqueDiffOn.univ_pi (Finₓ n) (fun _ => ℝ) _ fun i => unique_diff_on_Ici 0 
      by 
        simpa only [pi_univ_Ici] using this,
    continuous_to_fun := continuous_subtype_val,
    continuous_inv_fun :=
      continuous_subtype_mk _$ continuous_pi$ fun i => (continuous_id.max continuous_const).comp (continuous_apply i) }

localized [Manifold] notation "𝓡 " n => modelWithCornersSelf ℝ (EuclideanSpace ℝ (Finₓ n))

localized [Manifold] notation "𝓡∂ " n => modelWithCornersEuclideanHalfSpace n

-- error in Geometry.Manifold.Instances.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The left chart for the topological space `[x, y]`, defined on `[x,y)` and sending `x` to `0` in
`euclidean_half_space 1`.
-/ def Icc_left_chart (x y : exprℝ()) [fact «expr < »(x, y)] : local_homeomorph (Icc x y) (euclidean_half_space 1) :=
{ source := {z : Icc x y | «expr < »(z.val, y)},
  target := {z : euclidean_half_space 1 | «expr < »(z.val 0, «expr - »(y, x))},
  to_fun := λ z : Icc x y, ⟨λ i, «expr - »(z.val, x), sub_nonneg.mpr z.property.1⟩,
  inv_fun := λ
  z, ⟨min «expr + »(z.val 0, x) y, by simp [] [] [] ["[", expr le_refl, ",", expr z.prop, ",", expr le_of_lt (fact.out «expr < »(x, y)), "]"] [] []⟩,
  map_source' := by simp [] [] ["only"] ["[", expr imp_self, ",", expr sub_lt_sub_iff_right, ",", expr mem_set_of_eq, ",", expr forall_true_iff, "]"] [] [],
  map_target' := by { simp [] [] ["only"] ["[", expr min_lt_iff, ",", expr mem_set_of_eq, "]"] [] [],
    assume [binders (z hz)],
    left,
    dsimp [] ["[", "-", ident subtype.val_eq_coe, "]"] [] ["at", ident hz],
    linarith [] [] [] },
  left_inv' := begin
    rintros ["⟨", ident z, ",", ident hz, "⟩", ident h'z],
    simp [] [] ["only"] ["[", expr mem_set_of_eq, ",", expr mem_Icc, "]"] [] ["at", ident hz, ident h'z],
    simp [] [] ["only"] ["[", expr hz, ",", expr min_eq_left, ",", expr sub_add_cancel, "]"] [] []
  end,
  right_inv' := begin
    rintros ["⟨", ident z, ",", ident hz, "⟩", ident h'z],
    rw [expr subtype.mk_eq_mk] [],
    funext [],
    dsimp [] [] [] ["at", ident hz, ident h'z],
    have [ident A] [":", expr «expr ≤ »(«expr + »(x, z 0), y)] [],
    by linarith [] [] [],
    rw [expr subsingleton.elim i 0] [],
    simp [] [] ["only"] ["[", expr A, ",", expr add_comm, ",", expr add_sub_cancel', ",", expr min_eq_left, "]"] [] []
  end,
  open_source := begin
    have [] [":", expr is_open {z : exprℝ() | «expr < »(z, y)}] [":=", expr is_open_Iio],
    exact [expr this.preimage continuous_subtype_val]
  end,
  open_target := begin
    have [] [":", expr is_open {z : exprℝ() | «expr < »(z, «expr - »(y, x))}] [":=", expr is_open_Iio],
    have [] [":", expr is_open {z : euclidean_space exprℝ() (fin 1) | «expr < »(z 0, «expr - »(y, x))}] [":=", expr this.preimage (@continuous_apply (fin 1) (λ
       _, exprℝ()) _ 0)],
    exact [expr this.preimage continuous_subtype_val]
  end,
  continuous_to_fun := begin
    apply [expr continuous.continuous_on],
    apply [expr continuous_subtype_mk],
    have [] [":", expr continuous (λ
      (z : exprℝ())
      (i : fin 1), «expr - »(z, x))] [":=", expr continuous.sub «expr $ »(continuous_pi, λ
      i, continuous_id) continuous_const],
    exact [expr this.comp continuous_subtype_val]
  end,
  continuous_inv_fun := begin
    apply [expr continuous.continuous_on],
    apply [expr continuous_subtype_mk],
    have [ident A] [":", expr continuous (λ
      z : exprℝ(), min «expr + »(z, x) y)] [":=", expr (continuous_id.add continuous_const).min continuous_const],
    have [ident B] [":", expr continuous (λ z : euclidean_space exprℝ() (fin 1), z 0)] [":=", expr continuous_apply 0],
    exact [expr (A.comp B).comp continuous_subtype_val]
  end }

-- error in Geometry.Manifold.Instances.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The right chart for the topological space `[x, y]`, defined on `(x,y]` and sending `y` to `0` in
`euclidean_half_space 1`.
-/ def Icc_right_chart (x y : exprℝ()) [fact «expr < »(x, y)] : local_homeomorph (Icc x y) (euclidean_half_space 1) :=
{ source := {z : Icc x y | «expr < »(x, z.val)},
  target := {z : euclidean_half_space 1 | «expr < »(z.val 0, «expr - »(y, x))},
  to_fun := λ z : Icc x y, ⟨λ i, «expr - »(y, z.val), sub_nonneg.mpr z.property.2⟩,
  inv_fun := λ
  z, ⟨max «expr - »(y, z.val 0) x, by simp [] [] [] ["[", expr le_refl, ",", expr z.prop, ",", expr le_of_lt (fact.out «expr < »(x, y)), ",", expr sub_eq_add_neg, "]"] [] []⟩,
  map_source' := by simp [] [] ["only"] ["[", expr imp_self, ",", expr mem_set_of_eq, ",", expr sub_lt_sub_iff_left, ",", expr forall_true_iff, "]"] [] [],
  map_target' := by { simp [] [] ["only"] ["[", expr lt_max_iff, ",", expr mem_set_of_eq, "]"] [] [],
    assume [binders (z hz)],
    left,
    dsimp [] ["[", "-", ident subtype.val_eq_coe, "]"] [] ["at", ident hz],
    linarith [] [] [] },
  left_inv' := begin
    rintros ["⟨", ident z, ",", ident hz, "⟩", ident h'z],
    simp [] [] ["only"] ["[", expr mem_set_of_eq, ",", expr mem_Icc, "]"] [] ["at", ident hz, ident h'z],
    simp [] [] ["only"] ["[", expr hz, ",", expr sub_eq_add_neg, ",", expr max_eq_left, ",", expr add_add_neg_cancel'_right, ",", expr neg_add_rev, ",", expr neg_neg, "]"] [] []
  end,
  right_inv' := begin
    rintros ["⟨", ident z, ",", ident hz, "⟩", ident h'z],
    rw [expr subtype.mk_eq_mk] [],
    funext [],
    dsimp [] [] [] ["at", ident hz, ident h'z],
    have [ident A] [":", expr «expr ≤ »(x, «expr - »(y, z 0))] [],
    by linarith [] [] [],
    rw [expr subsingleton.elim i 0] [],
    simp [] [] ["only"] ["[", expr A, ",", expr sub_sub_cancel, ",", expr max_eq_left, "]"] [] []
  end,
  open_source := begin
    have [] [":", expr is_open {z : exprℝ() | «expr < »(x, z)}] [":=", expr is_open_Ioi],
    exact [expr this.preimage continuous_subtype_val]
  end,
  open_target := begin
    have [] [":", expr is_open {z : exprℝ() | «expr < »(z, «expr - »(y, x))}] [":=", expr is_open_Iio],
    have [] [":", expr is_open {z : euclidean_space exprℝ() (fin 1) | «expr < »(z 0, «expr - »(y, x))}] [":=", expr this.preimage (@continuous_apply (fin 1) (λ
       _, exprℝ()) _ 0)],
    exact [expr this.preimage continuous_subtype_val]
  end,
  continuous_to_fun := begin
    apply [expr continuous.continuous_on],
    apply [expr continuous_subtype_mk],
    have [] [":", expr continuous (λ
      (z : exprℝ())
      (i : fin 1), «expr - »(y, z))] [":=", expr continuous_const.sub (continuous_pi (λ i, continuous_id))],
    exact [expr this.comp continuous_subtype_val]
  end,
  continuous_inv_fun := begin
    apply [expr continuous.continuous_on],
    apply [expr continuous_subtype_mk],
    have [ident A] [":", expr continuous (λ
      z : exprℝ(), max «expr - »(y, z) x)] [":=", expr (continuous_const.sub continuous_id).max continuous_const],
    have [ident B] [":", expr continuous (λ z : euclidean_space exprℝ() (fin 1), z 0)] [":=", expr continuous_apply 0],
    exact [expr (A.comp B).comp continuous_subtype_val]
  end }

/--
Charted space structure on `[x, y]`, using only two charts taking values in
`euclidean_half_space 1`.
-/
instance iccManifold (x y : ℝ) [Fact (x < y)] : ChartedSpace (EuclideanHalfSpace 1) (Icc x y) :=
  { Atlas := {iccLeftChart x y, iccRightChart x y},
    chartAt := fun z => if z.val < y then iccLeftChart x y else iccRightChart x y,
    mem_chart_source :=
      fun z =>
        by 
          byCases' h' : z.val < y
          ·
            simp only [h', if_true]
            exact h'
          ·
            simp only [h', if_false]
            apply lt_of_lt_of_leₓ (Fact.out (x < y))
            simpa only [not_ltₓ] using h',
    chart_mem_atlas :=
      fun z =>
        by 
          byCases' h' : z.val < y <;> simp [h'] }

-- error in Geometry.Manifold.Instances.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The manifold structure on `[x, y]` is smooth.
-/
instance Icc_smooth_manifold
(x y : exprℝ())
[fact «expr < »(x, y)] : smooth_manifold_with_corners «expr𝓡∂ »(1) (Icc x y) :=
begin
  have [ident M] [":", expr times_cont_diff_on exprℝ() «expr∞»() (λ
    z : euclidean_space exprℝ() (fin 1), «expr + »(«expr- »(z), λ i, «expr - »(y, x))) univ] [],
  { rw [expr times_cont_diff_on_univ] [],
    exact [expr times_cont_diff_id.neg.add times_cont_diff_const] },
  apply [expr smooth_manifold_with_corners_of_times_cont_diff_on],
  assume [binders (e e' he he')],
  simp [] [] ["only"] ["[", expr atlas, ",", expr mem_singleton_iff, ",", expr mem_insert_iff, "]"] [] ["at", ident he, ident he'],
  rcases [expr he, "with", ident rfl, "|", ident rfl]; rcases [expr he', "with", ident rfl, "|", ident rfl],
  { exact [expr (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_times_cont_diff_groupoid _ _ _)).1] },
  { apply [expr M.congr_mono _ (subset_univ _)],
    rintro ["_", "⟨", "⟨", ident hz₁, ",", ident hz₂, "⟩", ",", "⟨", "⟨", ident z, ",", ident hz₀, "⟩", ",", ident rfl, "⟩", "⟩"],
    simp [] [] ["only"] ["[", expr model_with_corners_euclidean_half_space, ",", expr Icc_left_chart, ",", expr Icc_right_chart, ",", expr update_same, ",", expr max_eq_left, ",", expr hz₀, ",", expr lt_sub_iff_add_lt, "]"] ["with", ident mfld_simps] ["at", ident hz₁, ident hz₂],
    rw ["[", expr min_eq_left hz₁.le, ",", expr lt_add_iff_pos_left, "]"] ["at", ident hz₂],
    ext [] [ident i] [],
    rw [expr subsingleton.elim i 0] [],
    simp [] [] ["only"] ["[", expr model_with_corners_euclidean_half_space, ",", expr Icc_left_chart, ",", expr Icc_right_chart, ",", "*", ",", expr pi_Lp.add_apply, ",", expr pi_Lp.neg_apply, ",", expr max_eq_left, ",", expr min_eq_left hz₁.le, ",", expr update_same, "]"] ["with", ident mfld_simps] [],
    abel [] [] [] },
  { apply [expr M.congr_mono _ (subset_univ _)],
    rintro ["_", "⟨", "⟨", ident hz₁, ",", ident hz₂, "⟩", ",", "⟨", ident z, ",", ident hz₀, "⟩", ",", ident rfl, "⟩"],
    simp [] [] ["only"] ["[", expr model_with_corners_euclidean_half_space, ",", expr Icc_left_chart, ",", expr Icc_right_chart, ",", expr max_lt_iff, ",", expr update_same, ",", expr max_eq_left hz₀, "]"] ["with", ident mfld_simps] ["at", ident hz₁, ident hz₂],
    rw [expr lt_sub] ["at", ident hz₁],
    ext [] [ident i] [],
    rw [expr subsingleton.elim i 0] [],
    simp [] [] ["only"] ["[", expr model_with_corners_euclidean_half_space, ",", expr Icc_left_chart, ",", expr Icc_right_chart, ",", expr pi_Lp.add_apply, ",", expr pi_Lp.neg_apply, ",", expr update_same, ",", expr max_eq_left, ",", expr hz₀, ",", expr hz₁.le, "]"] ["with", ident mfld_simps] [],
    abel [] [] [] },
  { exact [expr (mem_groupoid_of_pregroupoid.mpr (symm_trans_mem_times_cont_diff_groupoid _ _ _)).1] }
end

/-! Register the manifold structure on `Icc 0 1`, and also its zero and one. -/


section 

theorem fact_zero_lt_one : Fact ((0 : ℝ) < 1) :=
  ⟨zero_lt_one⟩

attribute [local instance] fact_zero_lt_one

instance : ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1) :=
  by 
    infer_instance

instance : SmoothManifoldWithCorners (𝓡∂ 1) (Icc (0 : ℝ) 1) :=
  by 
    infer_instance

end 

