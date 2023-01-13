/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.isometry
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Antilipschitz

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `pseudo_metric_space` and we specialize to `metric_space` when needed.
-/


noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function Set

open TopologicalSpace Ennreal

/-- An isometry (also known as isometric embedding) is a map preserving the edistance
between pseudoemetric spaces, or equivalently the distance between pseudometric space.  -/
def Isometry [PseudoEmetricSpace α] [PseudoEmetricSpace β] (f : α → β) : Prop :=
  ∀ x1 x2 : α, edist (f x1) (f x2) = edist x1 x2
#align isometry Isometry

/-- On pseudometric spaces, a map is an isometry if and only if it preserves nonnegative
distances. -/
theorem isometry_iff_nndist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, nndist (f x) (f y) = nndist x y := by
  simp only [Isometry, edist_nndist, Ennreal.coe_eq_coe]
#align isometry_iff_nndist_eq isometry_iff_nndist_eq

/-- On pseudometric spaces, a map is an isometry if and only if it preserves distances. -/
theorem isometry_iff_dist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, dist (f x) (f y) = dist x y := by
  simp only [isometry_iff_nndist_eq, ← coe_nndist, Nnreal.coe_eq]
#align isometry_iff_dist_eq isometry_iff_dist_eq

/-- An isometry preserves distances. -/
alias isometry_iff_dist_eq ↔ Isometry.dist_eq _
#align isometry.dist_eq Isometry.dist_eq

/-- A map that preserves distances is an isometry -/
alias isometry_iff_dist_eq ↔ _ Isometry.of_dist_eq
#align isometry.of_dist_eq Isometry.of_dist_eq

/-- An isometry preserves non-negative distances. -/
alias isometry_iff_nndist_eq ↔ Isometry.nndist_eq _
#align isometry.nndist_eq Isometry.nndist_eq

/-- A map that preserves non-negative distances is an isometry. -/
alias isometry_iff_nndist_eq ↔ _ Isometry.of_nndist_eq
#align isometry.of_nndist_eq Isometry.of_nndist_eq

namespace Isometry

section PseudoEmetricIsometry

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] [PseudoEmetricSpace γ]

variable {f : α → β} {x y z : α} {s : Set α}

/-- An isometry preserves edistances. -/
theorem edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f y) = edist x y :=
  hf x y
#align isometry.edist_eq Isometry.edist_eq

theorem lipschitz (h : Isometry f) : LipschitzWith 1 f :=
  LipschitzWith.of_edist_le fun x y => (h x y).le
#align isometry.lipschitz Isometry.lipschitz

theorem antilipschitz (h : Isometry f) : AntilipschitzWith 1 f := fun x y => by
  simp only [h x y, Ennreal.coe_one, one_mul, le_refl]
#align isometry.antilipschitz Isometry.antilipschitz

/-- Any map on a subsingleton is an isometry -/
@[nontriviality]
theorem isometry_subsingleton [Subsingleton α] : Isometry f := fun x y => by
  rw [Subsingleton.elim x y] <;> simp
#align isometry_subsingleton isometry_subsingleton

/-- The identity is an isometry -/
theorem isometry_id : Isometry (id : α → α) := fun x y => rfl
#align isometry_id isometry_id

/-- The composition of isometries is an isometry -/
theorem comp {g : β → γ} {f : α → β} (hg : Isometry g) (hf : Isometry f) : Isometry (g ∘ f) :=
  fun x y => (hg _ _).trans (hf _ _)
#align isometry.comp Isometry.comp

/-- An isometry from a metric space is a uniform continuous map -/
protected theorem uniform_continuous (hf : Isometry f) : UniformContinuous f :=
  hf.lipschitz.UniformContinuous
#align isometry.uniform_continuous Isometry.uniform_continuous

/-- An isometry from a metric space is a uniform inducing map -/
protected theorem uniform_inducing (hf : Isometry f) : UniformInducing f :=
  hf.antilipschitz.UniformInducing hf.UniformContinuous
#align isometry.uniform_inducing Isometry.uniform_inducing

theorem tendsto_nhds_iff {ι : Type _} {f : α → β} {g : ι → α} {a : Filter ι} {b : α}
    (hf : Isometry f) : Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto (f ∘ g) a (𝓝 (f b)) :=
  hf.UniformInducing.Inducing.tendsto_nhds_iff
#align isometry.tendsto_nhds_iff Isometry.tendsto_nhds_iff

/-- An isometry is continuous. -/
protected theorem continuous (hf : Isometry f) : Continuous f :=
  hf.lipschitz.Continuous
#align isometry.continuous Isometry.continuous

/-- The right inverse of an isometry is an isometry. -/
theorem right_inv {f : α → β} {g : β → α} (h : Isometry f) (hg : RightInverse g f) : Isometry g :=
  fun x y => by rw [← h, hg _, hg _]
#align isometry.right_inv Isometry.right_inv

theorem preimage_emetric_closed_ball (h : Isometry f) (x : α) (r : ℝ≥0∞) :
    f ⁻¹' Emetric.closedBall (f x) r = Emetric.closedBall x r :=
  by
  ext y
  simp [h.edist_eq]
#align isometry.preimage_emetric_closed_ball Isometry.preimage_emetric_closed_ball

theorem preimage_emetric_ball (h : Isometry f) (x : α) (r : ℝ≥0∞) :
    f ⁻¹' Emetric.ball (f x) r = Emetric.ball x r :=
  by
  ext y
  simp [h.edist_eq]
#align isometry.preimage_emetric_ball Isometry.preimage_emetric_ball

/-- Isometries preserve the diameter in pseudoemetric spaces. -/
theorem ediam_image (hf : Isometry f) (s : Set α) : Emetric.diam (f '' s) = Emetric.diam s :=
  eq_of_forall_ge_iff fun d => by simp only [Emetric.diam_le_iff, ball_image_iff, hf.edist_eq]
#align isometry.ediam_image Isometry.ediam_image

theorem ediam_range (hf : Isometry f) : Emetric.diam (range f) = Emetric.diam (univ : Set α) :=
  by
  rw [← image_univ]
  exact hf.ediam_image univ
#align isometry.ediam_range Isometry.ediam_range

theorem maps_to_emetric_ball (hf : Isometry f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (Emetric.ball x r) (Emetric.ball (f x) r) :=
  (hf.preimage_emetric_ball x r).ge
#align isometry.maps_to_emetric_ball Isometry.maps_to_emetric_ball

theorem maps_to_emetric_closed_ball (hf : Isometry f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (Emetric.closedBall x r) (Emetric.closedBall (f x) r) :=
  (hf.preimage_emetric_closed_ball x r).ge
#align isometry.maps_to_emetric_closed_ball Isometry.maps_to_emetric_closed_ball

/-- The injection from a subtype is an isometry -/
theorem isometry_subtype_coe {s : Set α} : Isometry (coe : s → α) := fun x y => rfl
#align isometry_subtype_coe isometry_subtype_coe

theorem comp_continuous_on_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ → α} {s : Set γ} :
    ContinuousOn (f ∘ g) s ↔ ContinuousOn g s :=
  hf.UniformInducing.Inducing.continuous_on_iff.symm
#align isometry.comp_continuous_on_iff Isometry.comp_continuous_on_iff

theorem comp_continuous_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ → α} :
    Continuous (f ∘ g) ↔ Continuous g :=
  hf.UniformInducing.Inducing.continuous_iff.symm
#align isometry.comp_continuous_iff Isometry.comp_continuous_iff

end PseudoEmetricIsometry

--section
section EmetricIsometry

variable [EmetricSpace α] [PseudoEmetricSpace β] {f : α → β}

/-- An isometry from an emetric space is injective -/
protected theorem injective (h : Isometry f) : Injective f :=
  h.antilipschitz.Injective
#align isometry.injective Isometry.injective

/-- An isometry from an emetric space is a uniform embedding -/
protected theorem uniform_embedding (hf : Isometry f) : UniformEmbedding f :=
  hf.antilipschitz.UniformEmbedding hf.lipschitz.UniformContinuous
#align isometry.uniform_embedding Isometry.uniform_embedding

/-- An isometry from an emetric space is an embedding -/
protected theorem embedding (hf : Isometry f) : Embedding f :=
  hf.UniformEmbedding.Embedding
#align isometry.embedding Isometry.embedding

/-- An isometry from a complete emetric space is a closed embedding -/
theorem closed_embedding [CompleteSpace α] [EmetricSpace γ] {f : α → γ} (hf : Isometry f) :
    ClosedEmbedding f :=
  hf.antilipschitz.ClosedEmbedding hf.lipschitz.UniformContinuous
#align isometry.closed_embedding Isometry.closed_embedding

end EmetricIsometry

--section
section PseudoMetricIsometry

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}

/-- An isometry preserves the diameter in pseudometric spaces. -/
theorem diam_image (hf : Isometry f) (s : Set α) : Metric.diam (f '' s) = Metric.diam s := by
  rw [Metric.diam, Metric.diam, hf.ediam_image]
#align isometry.diam_image Isometry.diam_image

theorem diam_range (hf : Isometry f) : Metric.diam (range f) = Metric.diam (univ : Set α) :=
  by
  rw [← image_univ]
  exact hf.diam_image univ
#align isometry.diam_range Isometry.diam_range

theorem preimage_set_of_dist (hf : Isometry f) (x : α) (p : ℝ → Prop) :
    f ⁻¹' { y | p (dist y (f x)) } = { y | p (dist y x) } :=
  by
  ext y
  simp [hf.dist_eq]
#align isometry.preimage_set_of_dist Isometry.preimage_set_of_dist

theorem preimage_closed_ball (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r :=
  hf.preimage_set_of_dist x (· ≤ r)
#align isometry.preimage_closed_ball Isometry.preimage_closed_ball

theorem preimage_ball (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.ball (f x) r = Metric.ball x r :=
  hf.preimage_set_of_dist x (· < r)
#align isometry.preimage_ball Isometry.preimage_ball

theorem preimage_sphere (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  hf.preimage_set_of_dist x (· = r)
#align isometry.preimage_sphere Isometry.preimage_sphere

theorem maps_to_ball (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.ball x r) (Metric.ball (f x) r) :=
  (hf.preimage_ball x r).ge
#align isometry.maps_to_ball Isometry.maps_to_ball

theorem maps_to_sphere (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.sphere x r) (Metric.sphere (f x) r) :=
  (hf.preimage_sphere x r).ge
#align isometry.maps_to_sphere Isometry.maps_to_sphere

theorem maps_to_closed_ball (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) r) :=
  (hf.preimage_closed_ball x r).ge
#align isometry.maps_to_closed_ball Isometry.maps_to_closed_ball

end PseudoMetricIsometry

-- section
end Isometry

-- namespace
/-- A uniform embedding from a uniform space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
theorem UniformEmbedding.to_isometry {α β} [UniformSpace α] [MetricSpace β] {f : α → β}
    (h : UniformEmbedding f) :
    @Isometry α β
      (@PseudoMetricSpace.toPseudoEmetricSpace α
        (@MetricSpace.toPseudoMetricSpace α (h.comapMetricSpace f)))
      (by infer_instance) f :=
  by
  apply Isometry.of_dist_eq
  intro x y
  rfl
#align uniform_embedding.to_isometry UniformEmbedding.to_isometry

/-- An embedding from a topological space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
theorem Embedding.to_isometry {α β} [TopologicalSpace α] [MetricSpace β] {f : α → β}
    (h : Embedding f) :
    @Isometry α β
      (@PseudoMetricSpace.toPseudoEmetricSpace α
        (@MetricSpace.toPseudoMetricSpace α (h.comapMetricSpace f)))
      (by infer_instance) f :=
  by
  apply Isometry.of_dist_eq
  intro x y
  rfl
#align embedding.to_isometry Embedding.to_isometry

-- such a bijection need not exist
/-- `α` and `β` are isometric if there is an isometric bijection between them. -/
@[nolint has_nonempty_instance]
structure Isometric (α : Type _) (β : Type _) [PseudoEmetricSpace α] [PseudoEmetricSpace β] extends
  α ≃ β where
  isometry_to_fun : Isometry to_fun
#align isometric Isometric

-- mathport name: «expr ≃ᵢ »
infixl:25 " ≃ᵢ " => Isometric

namespace Isometric

section PseudoEmetricSpace

variable [PseudoEmetricSpace α] [PseudoEmetricSpace β] [PseudoEmetricSpace γ]

instance : CoeFun (α ≃ᵢ β) fun _ => α → β :=
  ⟨fun e => e.toEquiv⟩

theorem coe_eq_to_equiv (h : α ≃ᵢ β) (a : α) : h a = h.toEquiv a :=
  rfl
#align isometric.coe_eq_to_equiv Isometric.coe_eq_to_equiv

@[simp]
theorem coe_to_equiv (h : α ≃ᵢ β) : ⇑h.toEquiv = h :=
  rfl
#align isometric.coe_to_equiv Isometric.coe_to_equiv

protected theorem isometry (h : α ≃ᵢ β) : Isometry h :=
  h.isometry_to_fun
#align isometric.isometry Isometric.isometry

protected theorem bijective (h : α ≃ᵢ β) : Bijective h :=
  h.toEquiv.Bijective
#align isometric.bijective Isometric.bijective

protected theorem injective (h : α ≃ᵢ β) : Injective h :=
  h.toEquiv.Injective
#align isometric.injective Isometric.injective

protected theorem surjective (h : α ≃ᵢ β) : Surjective h :=
  h.toEquiv.Surjective
#align isometric.surjective Isometric.surjective

protected theorem edist_eq (h : α ≃ᵢ β) (x y : α) : edist (h x) (h y) = edist x y :=
  h.Isometry.edist_eq x y
#align isometric.edist_eq Isometric.edist_eq

protected theorem dist_eq {α β : Type _} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
    (x y : α) : dist (h x) (h y) = dist x y :=
  h.Isometry.dist_eq x y
#align isometric.dist_eq Isometric.dist_eq

protected theorem nndist_eq {α β : Type _} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
    (x y : α) : nndist (h x) (h y) = nndist x y :=
  h.Isometry.nndist_eq x y
#align isometric.nndist_eq Isometric.nndist_eq

protected theorem continuous (h : α ≃ᵢ β) : Continuous h :=
  h.Isometry.Continuous
#align isometric.continuous Isometric.continuous

@[simp]
theorem ediam_image (h : α ≃ᵢ β) (s : Set α) : Emetric.diam (h '' s) = Emetric.diam s :=
  h.Isometry.ediam_image s
#align isometric.ediam_image Isometric.ediam_image

theorem to_equiv_inj : ∀ ⦃h₁ h₂ : α ≃ᵢ β⦄, h₁.toEquiv = h₂.toEquiv → h₁ = h₂
  | ⟨e₁, h₁⟩, ⟨e₂, h₂⟩, H => by
    dsimp at H
    subst e₁
#align isometric.to_equiv_inj Isometric.to_equiv_inj

@[ext]
theorem ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ :=
  to_equiv_inj <| Equiv.ext H
#align isometric.ext Isometric.ext

/-- Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse. -/
def mk' {α : Type u} [EmetricSpace α] (f : α → β) (g : β → α) (hfg : ∀ x, f (g x) = x)
    (hf : Isometry f) : α ≃ᵢ β where
  toFun := f
  invFun := g
  left_inv x := hf.Injective <| hfg _
  right_inv := hfg
  isometry_to_fun := hf
#align isometric.mk' Isometric.mk'

/-- The identity isometry of a space. -/
protected def refl (α : Type _) [PseudoEmetricSpace α] : α ≃ᵢ α :=
  { Equiv.refl α with isometry_to_fun := isometry_id }
#align isometric.refl Isometric.refl

/-- The composition of two isometric isomorphisms, as an isometric isomorphism. -/
protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
  { Equiv.trans h₁.toEquiv h₂.toEquiv with
    isometry_to_fun := h₂.isometry_to_fun.comp h₁.isometry_to_fun }
#align isometric.trans Isometric.trans

@[simp]
theorem trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl
#align isometric.trans_apply Isometric.trans_apply

/-- The inverse of an isometric isomorphism, as an isometric isomorphism. -/
protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α
    where
  isometry_to_fun := h.Isometry.right_inv h.right_inv
  toEquiv := h.toEquiv.symm
#align isometric.symm Isometric.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵢ β) : α → β :=
  h
#align isometric.simps.apply Isometric.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symmApply (h : α ≃ᵢ β) : β → α :=
  h.symm
#align isometric.simps.symm_apply Isometric.Simps.symmApply

initialize_simps_projections Isometric (to_equiv_to_fun → apply, to_equiv_inv_fun → symmApply)

@[simp]
theorem symm_symm (h : α ≃ᵢ β) : h.symm.symm = h :=
  to_equiv_inj h.toEquiv.symm_symm
#align isometric.symm_symm Isometric.symm_symm

@[simp]
theorem apply_symm_apply (h : α ≃ᵢ β) (y : β) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y
#align isometric.apply_symm_apply Isometric.apply_symm_apply

@[simp]
theorem symm_apply_apply (h : α ≃ᵢ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
#align isometric.symm_apply_apply Isometric.symm_apply_apply

theorem symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} : h.symm y = x ↔ y = h x :=
  h.toEquiv.symm_apply_eq
#align isometric.symm_apply_eq Isometric.symm_apply_eq

theorem eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} : x = h.symm y ↔ h x = y :=
  h.toEquiv.eq_symm_apply
#align isometric.eq_symm_apply Isometric.eq_symm_apply

theorem symm_comp_self (h : α ≃ᵢ β) : ⇑h.symm ∘ ⇑h = id :=
  funext fun a => h.toEquiv.left_inv a
#align isometric.symm_comp_self Isometric.symm_comp_self

theorem self_comp_symm (h : α ≃ᵢ β) : ⇑h ∘ ⇑h.symm = id :=
  funext fun a => h.toEquiv.right_inv a
#align isometric.self_comp_symm Isometric.self_comp_symm

@[simp]
theorem range_eq_univ (h : α ≃ᵢ β) : range h = univ :=
  h.toEquiv.range_eq_univ
#align isometric.range_eq_univ Isometric.range_eq_univ

theorem image_symm (h : α ≃ᵢ β) : image h.symm = preimage h :=
  image_eq_preimage_of_inverse h.symm.toEquiv.left_inv h.symm.toEquiv.right_inv
#align isometric.image_symm Isometric.image_symm

theorem preimage_symm (h : α ≃ᵢ β) : preimage h.symm = image h :=
  (image_eq_preimage_of_inverse h.toEquiv.left_inv h.toEquiv.right_inv).symm
#align isometric.preimage_symm Isometric.preimage_symm

@[simp]
theorem symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) :
    (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) :=
  rfl
#align isometric.symm_trans_apply Isometric.symm_trans_apply

theorem ediam_univ (h : α ≃ᵢ β) : Emetric.diam (univ : Set α) = Emetric.diam (univ : Set β) := by
  rw [← h.range_eq_univ, h.isometry.ediam_range]
#align isometric.ediam_univ Isometric.ediam_univ

@[simp]
theorem ediam_preimage (h : α ≃ᵢ β) (s : Set β) : Emetric.diam (h ⁻¹' s) = Emetric.diam s := by
  rw [← image_symm, ediam_image]
#align isometric.ediam_preimage Isometric.ediam_preimage

@[simp]
theorem preimage_emetric_ball (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
    h ⁻¹' Emetric.ball x r = Emetric.ball (h.symm x) r := by
  rw [← h.isometry.preimage_emetric_ball (h.symm x) r, h.apply_symm_apply]
#align isometric.preimage_emetric_ball Isometric.preimage_emetric_ball

@[simp]
theorem preimage_emetric_closed_ball (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
    h ⁻¹' Emetric.closedBall x r = Emetric.closedBall (h.symm x) r := by
  rw [← h.isometry.preimage_emetric_closed_ball (h.symm x) r, h.apply_symm_apply]
#align isometric.preimage_emetric_closed_ball Isometric.preimage_emetric_closed_ball

@[simp]
theorem image_emetric_ball (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
    h '' Emetric.ball x r = Emetric.ball (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_emetric_ball, symm_symm]
#align isometric.image_emetric_ball Isometric.image_emetric_ball

@[simp]
theorem image_emetric_closed_ball (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
    h '' Emetric.closedBall x r = Emetric.closedBall (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_emetric_closed_ball, symm_symm]
#align isometric.image_emetric_closed_ball Isometric.image_emetric_closed_ball

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
@[simps toEquiv]
protected def toHomeomorph (h : α ≃ᵢ β) : α ≃ₜ β
    where
  continuous_to_fun := h.Continuous
  continuous_inv_fun := h.symm.Continuous
  toEquiv := h.toEquiv
#align isometric.to_homeomorph Isometric.toHomeomorph

@[simp]
theorem coe_to_homeomorph (h : α ≃ᵢ β) : ⇑h.toHomeomorph = h :=
  rfl
#align isometric.coe_to_homeomorph Isometric.coe_to_homeomorph

@[simp]
theorem coe_to_homeomorph_symm (h : α ≃ᵢ β) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl
#align isometric.coe_to_homeomorph_symm Isometric.coe_to_homeomorph_symm

@[simp]
theorem comp_continuous_on_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ → α} {s : Set γ} :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.toHomeomorph.comp_continuous_on_iff _ _
#align isometric.comp_continuous_on_iff Isometric.comp_continuous_on_iff

@[simp]
theorem comp_continuous_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ → α} :
    Continuous (h ∘ f) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff
#align isometric.comp_continuous_iff Isometric.comp_continuous_iff

@[simp]
theorem comp_continuous_iff' {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : β → γ} :
    Continuous (f ∘ h) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff'
#align isometric.comp_continuous_iff' Isometric.comp_continuous_iff'

/-- The group of isometries. -/
instance : Group (α ≃ᵢ α) where
  one := Isometric.refl _
  mul e₁ e₂ := e₂.trans e₁
  inv := Isometric.symm
  mul_assoc e₁ e₂ e₃ := rfl
  one_mul e := ext fun _ => rfl
  mul_one e := ext fun _ => rfl
  mul_left_inv e := ext e.symm_apply_apply

@[simp]
theorem coe_one : ⇑(1 : α ≃ᵢ α) = id :=
  rfl
#align isometric.coe_one Isometric.coe_one

@[simp]
theorem coe_mul (e₁ e₂ : α ≃ᵢ α) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
#align isometric.coe_mul Isometric.coe_mul

theorem mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl
#align isometric.mul_apply Isometric.mul_apply

@[simp]
theorem inv_apply_self (e : α ≃ᵢ α) (x : α) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x
#align isometric.inv_apply_self Isometric.inv_apply_self

@[simp]
theorem apply_inv_self (e : α ≃ᵢ α) (x : α) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x
#align isometric.apply_inv_self Isometric.apply_inv_self

protected theorem complete_space [CompleteSpace β] (e : α ≃ᵢ β) : CompleteSpace α :=
  complete_space_of_is_complete_univ <|
    is_complete_of_complete_image e.Isometry.UniformInducing <| by
      rwa [Set.image_univ, Isometric.range_eq_univ, ← complete_space_iff_is_complete_univ]
#align isometric.complete_space Isometric.complete_space

theorem complete_space_iff (e : α ≃ᵢ β) : CompleteSpace α ↔ CompleteSpace β :=
  by
  constructor <;> intro H
  exacts[e.symm.complete_space, e.complete_space]
#align isometric.complete_space_iff Isometric.complete_space_iff

end PseudoEmetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)

@[simp]
theorem diam_image (s : Set α) : Metric.diam (h '' s) = Metric.diam s :=
  h.Isometry.diam_image s
#align isometric.diam_image Isometric.diam_image

@[simp]
theorem diam_preimage (s : Set β) : Metric.diam (h ⁻¹' s) = Metric.diam s := by
  rw [← image_symm, diam_image]
#align isometric.diam_preimage Isometric.diam_preimage

theorem diam_univ : Metric.diam (univ : Set α) = Metric.diam (univ : Set β) :=
  congr_arg Ennreal.toReal h.ediam_univ
#align isometric.diam_univ Isometric.diam_univ

@[simp]
theorem preimage_ball (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.ball x r = Metric.ball (h.symm x) r := by
  rw [← h.isometry.preimage_ball (h.symm x) r, h.apply_symm_apply]
#align isometric.preimage_ball Isometric.preimage_ball

@[simp]
theorem preimage_sphere (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.sphere x r = Metric.sphere (h.symm x) r := by
  rw [← h.isometry.preimage_sphere (h.symm x) r, h.apply_symm_apply]
#align isometric.preimage_sphere Isometric.preimage_sphere

@[simp]
theorem preimage_closed_ball (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.closedBall x r = Metric.closedBall (h.symm x) r := by
  rw [← h.isometry.preimage_closed_ball (h.symm x) r, h.apply_symm_apply]
#align isometric.preimage_closed_ball Isometric.preimage_closed_ball

@[simp]
theorem image_ball (h : α ≃ᵢ β) (x : α) (r : ℝ) : h '' Metric.ball x r = Metric.ball (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_ball, symm_symm]
#align isometric.image_ball Isometric.image_ball

@[simp]
theorem image_sphere (h : α ≃ᵢ β) (x : α) (r : ℝ) :
    h '' Metric.sphere x r = Metric.sphere (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_sphere, symm_symm]
#align isometric.image_sphere Isometric.image_sphere

@[simp]
theorem image_closed_ball (h : α ≃ᵢ β) (x : α) (r : ℝ) :
    h '' Metric.closedBall x r = Metric.closedBall (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_closed_ball, symm_symm]
#align isometric.image_closed_ball Isometric.image_closed_ball

end PseudoMetricSpace

end Isometric

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
@[simps (config := { simpRhs := true }) toEquiv apply]
def Isometry.isometricOnRange [EmetricSpace α] [PseudoEmetricSpace β] {f : α → β} (h : Isometry f) :
    α ≃ᵢ range f
    where
  isometry_to_fun x y := by simpa [Subtype.edist_eq] using h x y
  toEquiv := Equiv.ofInjective f h.Injective
#align isometry.isometric_on_range Isometry.isometricOnRange

