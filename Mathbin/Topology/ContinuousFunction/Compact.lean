import Mathbin.Topology.ContinuousFunction.Bounded 
import Mathbin.Topology.UniformSpace.CompactSeparated 
import Mathbin.Tactic.EquivRw

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so acquire various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`bounded_continuous_function.equiv_continuous_map_of_compact` to move functions back and forth.

-/


noncomputable theory

open_locale TopologicalSpace Classical Nnreal BoundedContinuousFunction

open Set Filter Metric

open BoundedContinuousFunction

namespace ContinuousMap

variable {α β E : Type _} [TopologicalSpace α] [CompactSpace α] [MetricSpace β] [NormedGroup E]

section 

variable (α β)

/--
When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
@[simps (config := { fullyApplied := ff })]
def equiv_bounded_of_compact : C(α, β) ≃ (α →ᵇ β) :=
  ⟨mk_of_compact, forget_boundedness α β,
    fun f =>
      by 
        ext 
        rfl,
    fun f =>
      by 
        ext 
        rfl⟩

/--
When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps (config := { fullyApplied := ff }) apply symmApply]
def add_equiv_bounded_of_compact [AddMonoidₓ β] [HasLipschitzAdd β] : C(α, β) ≃+ (α →ᵇ β) :=
  ({ forget_boundedness_add_hom α β, (equiv_bounded_of_compact α β).symm with  } : (α →ᵇ β) ≃+ C(α, β)).symm

instance : MetricSpace C(α, β) :=
  MetricSpace.induced (equiv_bounded_of_compact α β) (equiv_bounded_of_compact α β).Injective
    (by 
      infer_instance)

/--
When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps (config := { fullyApplied := ff }) toEquiv apply symmApply]
def isometric_bounded_of_compact : C(α, β) ≃ᵢ (α →ᵇ β) :=
  { isometry_to_fun := fun x y => rfl, toEquiv := equiv_bounded_of_compact α β }

end 

@[simp]
theorem _root_.bounded_continuous_function.dist_mk_of_compact (f g : C(α, β)) :
  dist (mk_of_compact f) (mk_of_compact g) = dist f g :=
  rfl

@[simp]
theorem _root_.bounded_continuous_function.dist_forget_boundedness (f g : α →ᵇ β) :
  dist (f.forget_boundedness _ _) (g.forget_boundedness _ _) = dist f g :=
  rfl

open BoundedContinuousFunction

section 

variable {α β} {f g : C(α, β)} {C : ℝ}

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
theorem dist_apply_le_dist (x : α) : dist (f x) (g x) ≤ dist f g :=
  by 
    simp only [←dist_mk_of_compact, dist_coe_le_dist, ←mk_of_compact_apply]

/-- The distance between two functions is controlled by the supremum of the pointwise distances -/
theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C :=
  by 
    simp only [←dist_mk_of_compact, dist_le C0, mk_of_compact_apply]

theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C :=
  by 
    simp only [←dist_mk_of_compact, dist_le_iff_of_nonempty, mk_of_compact_apply]

theorem dist_lt_iff_of_nonempty [Nonempty α] : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C :=
  by 
    simp only [←dist_mk_of_compact, dist_lt_iff_of_nonempty_compact, mk_of_compact_apply]

theorem dist_lt_of_nonempty [Nonempty α] (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C :=
  dist_lt_iff_of_nonempty.2 w

theorem dist_lt_iff (C0 : (0 : ℝ) < C) : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C :=
  by 
    simp only [←dist_mk_of_compact, dist_lt_iff_of_compact C0, mk_of_compact_apply]

end 

instance [CompleteSpace β] : CompleteSpace C(α, β) :=
  (isometric_bounded_of_compact α β).CompleteSpace

@[continuity]
theorem continuous_eval : Continuous fun p : C(α, β) × α => p.1 p.2 :=
  continuous_eval.comp ((isometric_bounded_of_compact α β).Continuous.prod_map continuous_id)

@[continuity]
theorem continuous_evalx (x : α) : Continuous fun f : C(α, β) => f x :=
  continuous_eval.comp (continuous_id.prod_mk continuous_const)

theorem continuous_coe : @Continuous C(α, β) (α → β) _ _ coeFn :=
  continuous_pi continuous_evalx

instance : HasNorm C(α, E) :=
  { norm := fun x => dist x 0 }

@[simp]
theorem _root_.bounded_continuous_function.norm_mk_of_compact (f : C(α, E)) : ∥mk_of_compact f∥ = ∥f∥ :=
  rfl

@[simp]
theorem _root_.bounded_continuous_function.norm_forget_boundedness_eq (f : α →ᵇ E) : ∥forget_boundedness α E f∥ = ∥f∥ :=
  rfl

open BoundedContinuousFunction

instance : NormedGroup C(α, E) :=
  { dist_eq :=
      fun x y =>
        by 
          rw [←norm_mk_of_compact, ←dist_mk_of_compact, dist_eq_norm]
          congr 1 
          exact ((add_equiv_bounded_of_compact α E).map_sub _ _).symm }

section 

variable (f : C(α, E))

theorem norm_coe_le_norm (x : α) : ∥f x∥ ≤ ∥f∥ :=
  (mk_of_compact f).norm_coe_le_norm x

/-- Distance between the images of any two points is at most twice the norm of the function. -/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2*∥f∥ :=
  (mk_of_compact f).dist_le_two_norm x y

/-- The norm of a function is controlled by the supremum of the pointwise norms -/
theorem norm_le {C : ℝ} (C0 : (0 : ℝ) ≤ C) : ∥f∥ ≤ C ↔ ∀ x : α, ∥f x∥ ≤ C :=
  @BoundedContinuousFunction.norm_le _ _ _ _ (mk_of_compact f) _ C0

theorem norm_le_of_nonempty [Nonempty α] {M : ℝ} : ∥f∥ ≤ M ↔ ∀ x, ∥f x∥ ≤ M :=
  @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mk_of_compact f) _

theorem norm_lt_iff {M : ℝ} (M0 : 0 < M) : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mk_of_compact f) _ M0

theorem norm_lt_iff_of_nonempty [Nonempty α] {M : ℝ} : ∥f∥ < M ↔ ∀ x, ∥f x∥ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mk_of_compact f) _

theorem apply_le_norm (f : C(α, ℝ)) (x : α) : f x ≤ ∥f∥ :=
  le_transₓ (le_abs.mpr (Or.inl (le_reflₓ (f x)))) (f.norm_coe_le_norm x)

theorem neg_norm_le_apply (f : C(α, ℝ)) (x : α) : -∥f∥ ≤ f x :=
  le_transₓ (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs_self (f x)))

theorem norm_eq_supr_norm : ∥f∥ = ⨆x : α, ∥f x∥ :=
  (mk_of_compact f).norm_eq_supr_norm

end 

section 

variable {R : Type _} [NormedRing R]

instance : NormedRing C(α, R) :=
  { (inferInstance : NormedGroup C(α, R)) with norm_mul := fun f g => norm_mul_le (mk_of_compact f) (mk_of_compact g) }

end 

section 

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance : NormedSpace 𝕜 C(α, E) :=
  { norm_smul_le := fun c f => le_of_eqₓ (norm_smul c (mk_of_compact f)) }

section 

variable (α 𝕜 E)

/--
When `α` is compact and `𝕜` is a normed field,
the `𝕜`-algebra of bounded continuous maps `α →ᵇ β` is
`𝕜`-linearly isometric to `C(α, β)`.
-/
def linear_isometry_bounded_of_compact : C(α, E) ≃ₗᵢ[𝕜] α →ᵇ E :=
  { add_equiv_bounded_of_compact α E with
    map_smul' :=
      fun c f =>
        by 
          ext 
          simp ,
    norm_map' := fun f => rfl }

end 

@[simp]
theorem linear_isometry_bounded_of_compact_symm_apply (f : α →ᵇ E) :
  (linear_isometry_bounded_of_compact α E 𝕜).symm f = f.forget_boundedness α E :=
  rfl

@[simp]
theorem linear_isometry_bounded_of_compact_apply_apply (f : C(α, E)) (a : α) :
  (linear_isometry_bounded_of_compact α E 𝕜 f) a = f a :=
  rfl

@[simp]
theorem linear_isometry_bounded_of_compact_to_isometric :
  (linear_isometry_bounded_of_compact α E 𝕜).toIsometric = isometric_bounded_of_compact α E :=
  rfl

@[simp]
theorem linear_isometry_bounded_of_compact_to_add_equiv :
  (linear_isometry_bounded_of_compact α E 𝕜).toLinearEquiv.toAddEquiv = add_equiv_bounded_of_compact α E :=
  rfl

@[simp]
theorem linear_isometry_bounded_of_compact_of_compact_to_equiv :
  (linear_isometry_bounded_of_compact α E 𝕜).toLinearEquiv.toEquiv = equiv_bounded_of_compact α E :=
  rfl

end 

section 

variable {𝕜 : Type _} {γ : Type _} [NormedField 𝕜] [NormedRing γ] [NormedAlgebra 𝕜 γ]

instance [Nonempty α] : NormedAlgebra 𝕜 C(α, γ) :=
  { norm_algebra_map_eq := fun c => (norm_algebra_map_eq (α →ᵇ γ) c : _) }

end 

end ContinuousMap

namespace ContinuousMap

section UniformContinuity

variable {α β : Type _}

variable [MetricSpace α] [CompactSpace α] [MetricSpace β]

/-!
We now set up some declarations making it convenient to use uniform continuity.
-/


theorem uniform_continuity (f : C(α, β)) (ε : ℝ) (h : 0 < ε) :
  ∃ (δ : _)(_ : δ > 0), ∀ {x y}, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniform_continuous_iff.mp (CompactSpace.uniform_continuous_of_continuous f.continuous) ε h

/--
An arbitrarily chosen modulus of uniform continuity for a given function `f` and `ε > 0`.
-/
def modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  Classical.some (uniform_continuity f ε h)

theorem modulus_pos (f : C(α, β)) {ε : ℝ} {h : 0 < ε} : 0 < f.modulus ε h :=
  (Classical.some_spec (uniform_continuity f ε h)).fst

theorem dist_lt_of_dist_lt_modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) {a b : α} (w : dist a b < f.modulus ε h) :
  dist (f a) (f b) < ε :=
  (Classical.some_spec (uniform_continuity f ε h)).snd w

end UniformContinuity

end ContinuousMap

section CompLeft

variable (X : Type _) {𝕜 β γ : Type _} [TopologicalSpace X] [CompactSpace X] [NondiscreteNormedField 𝕜]

variable [NormedGroup β] [NormedSpace 𝕜 β] [NormedGroup γ] [NormedSpace 𝕜 γ]

open ContinuousMap

/--
Postcomposition of continuous functions into a normed module by a continuous linear map is a
continuous linear map.
Transferred version of `continuous_linear_map.comp_left_continuous_bounded`,
upgraded version of `continuous_linear_map.comp_left_continuous`,
similar to `linear_map.comp_left`. -/
protected def ContinuousLinearMap.compLeftContinuousCompact (g : β →L[𝕜] γ) : C(X, β) →L[𝕜] C(X, γ) :=
  (linear_isometry_bounded_of_compact X γ 𝕜).symm.toLinearIsometry.toContinuousLinearMap.comp$
    (g.comp_left_continuous_bounded X).comp$
      (linear_isometry_bounded_of_compact X β 𝕜).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem ContinuousLinearMap.to_linear_comp_left_continuous_compact (g : β →L[𝕜] γ) :
  (g.comp_left_continuous_compact X : C(X, β) →ₗ[𝕜] C(X, γ)) = g.comp_left_continuous 𝕜 X :=
  by 
    ext f 
    rfl

@[simp]
theorem ContinuousLinearMap.comp_left_continuous_compact_apply (g : β →L[𝕜] γ) (f : C(X, β)) (x : X) :
  g.comp_left_continuous_compact X f x = g (f x) :=
  rfl

end CompLeft

namespace ContinuousMap

/-!
We now setup variations on `comp_right_* f`, where `f : C(X, Y)`
(that is, precomposition by a continuous map),
as a morphism `C(Y, T) → C(X, T)`, respecting various types of structure.

In particular:
* `comp_right_continuous_map`, the bundled continuous map (for this we need `X Y` compact).
* `comp_right_homeomorph`, when we precompose by a homeomorphism.
* `comp_right_alg_hom`, when `T = R` is a topological ring.
-/


section CompRight

/--
Precomposition by a continuous map is itself a continuous map between spaces of continuous maps.
-/
def comp_right_continuous_map {X Y : Type _} (T : Type _) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
  [CompactSpace Y] [NormedGroup T] (f : C(X, Y)) : C(C(Y, T), C(X, T)) :=
  { toFun := fun g => g.comp f,
    continuous_to_fun :=
      by 
        refine' metric.continuous_iff.mpr _ 
        intro g ε ε_pos 
        refine' ⟨ε, ε_pos, fun g' h => _⟩
        rw [ContinuousMap.dist_lt_iff ε_pos] at h⊢
        ·
          exact fun x => h (f x) }

@[simp]
theorem comp_right_continuous_map_apply {X Y : Type _} (T : Type _) [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [NormedGroup T] (f : C(X, Y)) (g : C(Y, T)) :
  (comp_right_continuous_map T f) g = g.comp f :=
  rfl

/--
Precomposition by a homeomorphism is itself a homeomorphism between spaces of continuous maps.
-/
def comp_right_homeomorph {X Y : Type _} (T : Type _) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
  [CompactSpace Y] [NormedGroup T] (f : X ≃ₜ Y) : C(Y, T) ≃ₜ C(X, T) :=
  { toFun := comp_right_continuous_map T f.to_continuous_map,
    invFun := comp_right_continuous_map T f.symm.to_continuous_map,
    left_inv :=
      by 
        tidy,
    right_inv :=
      by 
        tidy }

/--
Precomposition of functions into a normed ring by continuous map is an algebra homomorphism.
-/
def comp_right_alg_hom {X Y : Type _} (R : Type _) [TopologicalSpace X] [TopologicalSpace Y] [NormedCommRing R]
  (f : C(X, Y)) : C(Y, R) →ₐ[R] C(X, R) :=
  { toFun := fun g => g.comp f,
    map_zero' :=
      by 
        ext 
        simp ,
    map_add' :=
      fun g₁ g₂ =>
        by 
          ext 
          simp ,
    map_one' :=
      by 
        ext 
        simp ,
    map_mul' :=
      fun g₁ g₂ =>
        by 
          ext 
          simp ,
    commutes' :=
      fun r =>
        by 
          ext 
          simp  }

@[simp]
theorem comp_right_alg_hom_apply {X Y : Type _} (R : Type _) [TopologicalSpace X] [TopologicalSpace Y]
  [NormedCommRing R] (f : C(X, Y)) (g : C(Y, R)) : (comp_right_alg_hom R f) g = g.comp f :=
  rfl

theorem comp_right_alg_hom_continuous {X Y : Type _} (R : Type _) [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [NormedCommRing R] (f : C(X, Y)) : Continuous (comp_right_alg_hom R f) :=
  by 
    change Continuous (comp_right_continuous_map R f)
    continuity

end CompRight

end ContinuousMap

