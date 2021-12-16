import Mathbin.Analysis.NormedSpace.Basic 
import Mathbin.LinearAlgebra.AffineSpace.Midpoint 
import Mathbin.Topology.Instances.RealVectorSpace

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.

-/


noncomputable section 

open_locale Nnreal TopologicalSpace

open Filter

/-- A `semi_normed_add_torsor V P` is a torsor of an additive seminormed group
action by a `semi_normed_group V` on points `P`. We bundle the pseudometric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a pseudometric space, but
bundling just the distance and using an instance for the pseudometric space
results in type class problems). -/
class SemiNormedAddTorsor (V : outParam$ Type _) (P : Type _) [outParam$ SemiNormedGroup V]
  [PseudoMetricSpace P] extends AddTorsor V P where 
  dist_eq_norm' : ∀ x y : P, dist x y = ∥(x -ᵥ y : V)∥

/-- A `normed_add_torsor V P` is a torsor of an additive normed group
action by a `normed_group V` on points `P`. We bundle the metric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a metric space, but
bundling just the distance and using an instance for the metric space
results in type class problems). -/
class NormedAddTorsor (V : outParam$ Type _) (P : Type _) [outParam$ NormedGroup V] [MetricSpace P] extends
  AddTorsor V P where 
  dist_eq_norm' : ∀ x y : P, dist x y = ∥(x -ᵥ y : V)∥

/-- A `normed_add_torsor` is a `semi_normed_add_torsor`. -/
instance (priority := 100) NormedAddTorsor.toSemiNormedAddTorsor {V P : Type _} [NormedGroup V] [MetricSpace P]
  [β : NormedAddTorsor V P] : SemiNormedAddTorsor V P :=
  { β with  }

variable {α V P : Type _} [SemiNormedGroup V] [PseudoMetricSpace P] [SemiNormedAddTorsor V P]

variable {W Q : Type _} [NormedGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

/-- A `semi_normed_group` is a `semi_normed_add_torsor` over itself. -/
instance (priority := 100) SemiNormedGroup.normedAddTorsor : SemiNormedAddTorsor V V :=
  { dist_eq_norm' := dist_eq_norm }

/-- A `normed_group` is a `normed_add_torsor` over itself. -/
instance (priority := 100) NormedGroup.normedAddTorsor : NormedAddTorsor W W :=
  { dist_eq_norm' := dist_eq_norm }

include V

section 

variable (V W)

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
theorem dist_eq_norm_vsub (x y : P) : dist x y = ∥x -ᵥ y∥ :=
  SemiNormedAddTorsor.dist_eq_norm' x y

end 

@[simp]
theorem dist_vadd_cancel_left (v : V) (x y : P) : dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
  by 
    rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, vadd_vsub_vadd_cancel_left]

@[simp]
theorem dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ :=
  by 
    rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]

@[simp]
theorem dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ∥v∥ :=
  by 
    simp [dist_eq_norm_vsub V _ x]

@[simp]
theorem dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ∥v∥ :=
  by 
    rw [dist_comm, dist_vadd_left]

@[simp]
theorem dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z :=
  by 
    rw [dist_eq_norm, vsub_sub_vsub_cancel_left, dist_comm, dist_eq_norm_vsub V]

@[simp]
theorem dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
  by 
    rw [dist_eq_norm, vsub_sub_vsub_cancel_right, dist_eq_norm_vsub V]

theorem dist_vadd_vadd_le (v v' : V) (p p' : P) : dist (v +ᵥ p) (v' +ᵥ p') ≤ dist v v'+dist p p' :=
  by 
    simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')

theorem dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) : dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ dist p₁ p₃+dist p₂ p₄ :=
  by 
    rw [dist_eq_norm, vsub_sub_vsub_comm, dist_eq_norm_vsub V, dist_eq_norm_vsub V]
    exact norm_sub_le _ _

theorem nndist_vadd_vadd_le (v v' : V) (p p' : P) : nndist (v +ᵥ p) (v' +ᵥ p') ≤ nndist v v'+nndist p p' :=
  by 
    simp only [←Nnreal.coe_le_coe, Nnreal.coe_add, ←dist_nndist, dist_vadd_vadd_le]

theorem nndist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) : nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ nndist p₁ p₃+nndist p₂ p₄ :=
  by 
    simp only [←Nnreal.coe_le_coe, Nnreal.coe_add, ←dist_nndist, dist_vsub_vsub_le]

theorem edist_vadd_vadd_le (v v' : V) (p p' : P) : edist (v +ᵥ p) (v' +ᵥ p') ≤ edist v v'+edist p p' :=
  by 
    simp only [edist_nndist]
    applyModCast nndist_vadd_vadd_le

theorem edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) : edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ edist p₁ p₃+edist p₂ p₄ :=
  by 
    simp only [edist_nndist]
    applyModCast nndist_vsub_vsub_le

omit V

/-- The pseudodistance defines a pseudometric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def pseudoMetricSpaceOfNormedGroupOfAddTorsor (V P : Type _) [SemiNormedGroup V] [AddTorsor V P] :
  PseudoMetricSpace P :=
  { dist := fun x y => ∥(x -ᵥ y : V)∥,
    dist_self :=
      fun x =>
        by 
          simp ,
    dist_comm :=
      fun x y =>
        by 
          simp only [←neg_vsub_eq_vsub_rev y x, norm_neg],
    dist_triangle :=
      by 
        intro x y z 
        change ∥x -ᵥ z∥ ≤ ∥x -ᵥ y∥+∥y -ᵥ z∥
        rw [←vsub_add_vsub_cancel]
        apply norm_add_le }

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def metricSpaceOfNormedGroupOfAddTorsor (V P : Type _) [NormedGroup V] [AddTorsor V P] : MetricSpace P :=
  { dist := fun x y => ∥(x -ᵥ y : V)∥,
    dist_self :=
      fun x =>
        by 
          simp ,
    eq_of_dist_eq_zero :=
      fun x y h =>
        by 
          simpa using h,
    dist_comm :=
      fun x y =>
        by 
          simp only [←neg_vsub_eq_vsub_rev y x, norm_neg],
    dist_triangle :=
      by 
        intro x y z 
        change ∥x -ᵥ z∥ ≤ ∥x -ᵥ y∥+∥y -ᵥ z∥
        rw [←vsub_add_vsub_cancel]
        apply norm_add_le }

include V

theorem LipschitzWith.vadd [PseudoEmetricSpace α] {f : α → V} {g : α → P} {Kf Kg :  ℝ≥0 } (hf : LipschitzWith Kf f)
  (hg : LipschitzWith Kg g) : LipschitzWith (Kf+Kg) (f +ᵥ g) :=
  fun x y =>
    calc edist (f x +ᵥ g x) (f y +ᵥ g y) ≤ edist (f x) (f y)+edist (g x) (g y) := edist_vadd_vadd_le _ _ _ _ 
      _ ≤ (Kf*edist x y)+Kg*edist x y := add_le_add (hf x y) (hg x y)
      _ = (Kf+Kg)*edist x y := (add_mulₓ _ _ _).symm
      

theorem LipschitzWith.vsub [PseudoEmetricSpace α] {f g : α → P} {Kf Kg :  ℝ≥0 } (hf : LipschitzWith Kf f)
  (hg : LipschitzWith Kg g) : LipschitzWith (Kf+Kg) (f -ᵥ g) :=
  fun x y =>
    calc edist (f x -ᵥ g x) (f y -ᵥ g y) ≤ edist (f x) (f y)+edist (g x) (g y) := edist_vsub_vsub_le _ _ _ _ 
      _ ≤ (Kf*edist x y)+Kg*edist x y := add_le_add (hf x y) (hg x y)
      _ = (Kf+Kg)*edist x y := (add_mulₓ _ _ _).symm
      

theorem uniform_continuous_vadd : UniformContinuous fun x : V × P => x.1 +ᵥ x.2 :=
  (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).UniformContinuous

theorem uniform_continuous_vsub : UniformContinuous fun x : P × P => x.1 -ᵥ x.2 :=
  (LipschitzWith.prod_fst.vsub LipschitzWith.prod_snd).UniformContinuous

instance (priority := 100) SemiNormedAddTorsor.has_continuous_vadd : HasContinuousVadd V P :=
  { continuous_vadd := uniform_continuous_vadd.Continuous }

theorem continuous_vsub : Continuous fun x : P × P => x.1 -ᵥ x.2 :=
  uniform_continuous_vsub.Continuous

theorem Filter.Tendsto.vsub {l : Filter α} {f g : α → P} {x y : P} (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
  (continuous_vsub.Tendsto (x, y)).comp (hf.prod_mk_nhds hg)

section 

variable [TopologicalSpace α]

theorem Continuous.vsub {f g : α → P} (hf : Continuous f) (hg : Continuous g) : Continuous (f -ᵥ g) :=
  continuous_vsub.comp (hf.prod_mk hg : _)

theorem ContinuousAt.vsub {f g : α → P} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
  ContinuousAt (f -ᵥ g) x :=
  hf.vsub hg

theorem ContinuousWithinAt.vsub {f g : α → P} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
  (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f -ᵥ g) s x :=
  hf.vsub hg

end 

section 

variable {R : Type _} [Ringₓ R] [TopologicalSpace R] [Module R V] [HasContinuousSmul R V]

theorem Filter.Tendsto.line_map {l : Filter α} {f₁ f₂ : α → P} {g : α → R} {p₁ p₂ : P} {c : R}
  (h₁ : tendsto f₁ l (𝓝 p₁)) (h₂ : tendsto f₂ l (𝓝 p₂)) (hg : tendsto g l (𝓝 c)) :
  tendsto (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) l (𝓝$ AffineMap.lineMap p₁ p₂ c) :=
  (hg.smul (h₂.vsub h₁)).vadd h₁

theorem Filter.Tendsto.midpoint [Invertible (2 : R)] {l : Filter α} {f₁ f₂ : α → P} {p₁ p₂ : P}
  (h₁ : tendsto f₁ l (𝓝 p₁)) (h₂ : tendsto f₂ l (𝓝 p₂)) :
  tendsto (fun x => midpoint R (f₁ x) (f₂ x)) l (𝓝$ midpoint R p₁ p₂) :=
  h₁.line_map h₂ tendsto_const_nhds

end 

section NormedSpace

variable {𝕜 : Type _} [NormedField 𝕜] [SemiNormedSpace 𝕜 V]

open AffineMap

@[simp]
theorem dist_center_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₁ (homothety p₁ c p₂) = ∥c∥*dist p₁ p₂ :=
  by 
    simp [homothety_def, norm_smul, ←dist_eq_norm_vsub, dist_comm]

@[simp]
theorem dist_homothety_center (p₁ p₂ : P) (c : 𝕜) : dist (homothety p₁ c p₂) p₁ = ∥c∥*dist p₁ p₂ :=
  by 
    rw [dist_comm, dist_center_homothety]

@[simp]
theorem dist_homothety_self (p₁ p₂ : P) (c : 𝕜) : dist (homothety p₁ c p₂) p₂ = ∥1 - c∥*dist p₁ p₂ :=
  by 
    rw [homothety_eq_line_map, ←line_map_apply_one_sub, ←homothety_eq_line_map, dist_homothety_center, dist_comm]

@[simp]
theorem dist_self_homothety (p₁ p₂ : P) (c : 𝕜) : dist p₂ (homothety p₁ c p₂) = ∥1 - c∥*dist p₁ p₂ :=
  by 
    rw [dist_comm, dist_homothety_self]

variable [Invertible (2 : 𝕜)]

@[simp]
theorem dist_left_midpoint (p₁ p₂ : P) : dist p₁ (midpoint 𝕜 p₁ p₂) = ∥(2 : 𝕜)∥⁻¹*dist p₁ p₂ :=
  by 
    rw [midpoint, ←homothety_eq_line_map, dist_center_homothety, inv_of_eq_inv, ←NormedField.norm_inv]

@[simp]
theorem dist_midpoint_left (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₁ = ∥(2 : 𝕜)∥⁻¹*dist p₁ p₂ :=
  by 
    rw [dist_comm, dist_left_midpoint]

@[simp]
theorem dist_midpoint_right (p₁ p₂ : P) : dist (midpoint 𝕜 p₁ p₂) p₂ = ∥(2 : 𝕜)∥⁻¹*dist p₁ p₂ :=
  by 
    rw [midpoint_comm, dist_midpoint_left, dist_comm]

@[simp]
theorem dist_right_midpoint (p₁ p₂ : P) : dist p₂ (midpoint 𝕜 p₁ p₂) = ∥(2 : 𝕜)∥⁻¹*dist p₁ p₂ :=
  by 
    rw [dist_comm, dist_midpoint_right]

theorem dist_midpoint_midpoint_le' (p₁ p₂ p₃ p₄ : P) :
  dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₃ p₄) ≤ (dist p₁ p₃+dist p₂ p₄) / ∥(2 : 𝕜)∥ :=
  by 
    rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint] <;>
      try 
        infer_instance 
    rw [midpoint_eq_smul_add, norm_smul, inv_of_eq_inv, NormedField.norm_inv, ←div_eq_inv_mul]
    exact div_le_div_of_le_of_nonneg (norm_add_le _ _) (norm_nonneg _)

end NormedSpace

variable [SemiNormedSpace ℝ V] [NormedSpace ℝ W]

theorem dist_midpoint_midpoint_le (p₁ p₂ p₃ p₄ : V) :
  dist (midpoint ℝ p₁ p₂) (midpoint ℝ p₃ p₄) ≤ (dist p₁ p₃+dist p₂ p₄) / 2 :=
  by 
    simpa using dist_midpoint_midpoint_le' p₁ p₂ p₃ p₄

include W

/-- A continuous map between two normed affine spaces is an affine map provided that
it sends midpoints to midpoints. -/
def AffineMap.ofMapMidpoint (f : P → Q) (h : ∀ x y, f (midpoint ℝ x y) = midpoint ℝ (f x) (f y)) (hfc : Continuous f) :
  P →ᵃ[ℝ] Q :=
  AffineMap.mk' f
    (↑((AddMonoidHom.ofMapMidpoint ℝ ℝ
            ((AffineEquiv.vaddConst ℝ (f$ Classical.arbitrary P)).symm ∘
              f ∘ AffineEquiv.vaddConst ℝ (Classical.arbitrary P))
            (by 
              simp )
            fun x y =>
              by 
                simp [h]).toRealLinearMap$
        by 
          applyRules [Continuous.vadd, Continuous.vsub, continuous_const, hfc.comp, continuous_id]))
    (Classical.arbitrary P)
    fun p =>
      by 
        simp 

