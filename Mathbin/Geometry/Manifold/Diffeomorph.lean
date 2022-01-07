import Mathbin.Geometry.Manifold.TimesContMdiffMap

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `diffeomorph I I' M M' n`:  `n`-times continuously differentiable diffeomorphism between
  `M` and `M'` with respect to I and I'; we do not introduce a separate definition for the case
  `n = ∞`; we use notation instead.
* `diffeomorph.to_homeomorph`: reinterpret a diffeomorphism as a homeomorphism.
* `continuous_linear_equiv.to_diffeomorph`: reinterpret a continuous equivalence as
  a diffeomorphism.
* `model_with_corners.trans_diffeomorph`: compose a given `model_with_corners` with a diffeomorphism
  between the old and the new target spaces. Useful, e.g, to turn any finite dimensional manifold
  into a manifold modelled on a Euclidean space.
* `diffeomorph.to_trans_diffeomorph`: the identity diffeomorphism between `M` with model `I` and `M`
  with model `I.trans_diffeomorph e`.

## Notations

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `diffeomorph I J M N ⊤`
* `E ≃ₘ^n[𝕜] E'`      := `E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`
* `E ≃ₘ[𝕜] E'`        := `E ≃ₘ⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ E'`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Keywords

diffeomorphism, manifold
-/


open_locale Manifold TopologicalSpace

open Function Set

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {E' : Type _}
  [NormedGroup E'] [NormedSpace 𝕜 E'] {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F] {H : Type _} [TopologicalSpace H]
  {H' : Type _} [TopologicalSpace H'] {G : Type _} [TopologicalSpace G] {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}

variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type _} [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ}

section Defs

variable (I I' M M' n)

/-- `n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to I and I'
-/
@[protect_proj, nolint has_inhabited_instance]
structure Diffeomorph extends M ≃ M' where
  times_cont_mdiff_to_fun : TimesContMdiff I I' n to_equiv
  times_cont_mdiff_inv_fun : TimesContMdiff I' I n to_equiv.symm

end Defs

localized [Manifold] notation M " ≃ₘ^" n:1000 "⟮" I "," J "⟯ " N => Diffeomorph I J M N n

localized [Manifold] notation M " ≃ₘ⟮" I "," J "⟯ " N => Diffeomorph I J M N ⊤

localized [Manifold]
  notation E " ≃ₘ^" n:1000 "[" 𝕜 "] " E' => Diffeomorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' n

localized [Manifold]
  notation E " ≃ₘ[" 𝕜 "] " E' => Diffeomorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' ⊤

namespace Diffeomorph

instance : CoeFun (M ≃ₘ^n⟮I,I'⟯ M') fun _ => M → M' :=
  ⟨fun e => e.to_equiv⟩

instance : Coe (M ≃ₘ^n⟮I,I'⟯ M') C^n⟮I, M; I', M'⟯ :=
  ⟨fun Φ => ⟨Φ, Φ.times_cont_mdiff_to_fun⟩⟩

@[continuity]
protected theorem Continuous (h : M ≃ₘ^n⟮I,I'⟯ M') : Continuous h :=
  h.times_cont_mdiff_to_fun.continuous

protected theorem TimesContMdiff (h : M ≃ₘ^n⟮I,I'⟯ M') : TimesContMdiff I I' n h :=
  h.times_cont_mdiff_to_fun

protected theorem TimesContMdiffAt (h : M ≃ₘ^n⟮I,I'⟯ M') {x} : TimesContMdiffAt I I' n h x :=
  h.times_cont_mdiff.times_cont_mdiff_at

protected theorem TimesContMdiffWithinAt (h : M ≃ₘ^n⟮I,I'⟯ M') {s x} : TimesContMdiffWithinAt I I' n h s x :=
  h.times_cont_mdiff_at.times_cont_mdiff_within_at

protected theorem TimesContDiff (h : E ≃ₘ^n[𝕜] E') : TimesContDiff 𝕜 n h :=
  h.times_cont_mdiff.times_cont_diff

protected theorem Smooth (h : M ≃ₘ⟮I,I'⟯ M') : Smooth I I' h :=
  h.times_cont_mdiff_to_fun

protected theorem Mdifferentiable (h : M ≃ₘ^n⟮I,I'⟯ M') (hn : 1 ≤ n) : Mdifferentiable I I' h :=
  h.times_cont_mdiff.mdifferentiable hn

protected theorem MdifferentiableOn (h : M ≃ₘ^n⟮I,I'⟯ M') (s : Set M) (hn : 1 ≤ n) : MdifferentiableOn I I' h s :=
  (h.mdifferentiable hn).MdifferentiableOn

@[simp]
theorem coe_to_equiv (h : M ≃ₘ^n⟮I,I'⟯ M') : ⇑h.to_equiv = h :=
  rfl

@[simp, norm_cast]
theorem coe_coe (h : M ≃ₘ^n⟮I,I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h :=
  rfl

theorem to_equiv_injective : injective (Diffeomorph.toEquiv : (M ≃ₘ^n⟮I,I'⟯ M') → M ≃ M')
  | ⟨e, _, _⟩, ⟨e', _, _⟩, rfl => rfl

@[simp]
theorem to_equiv_inj {h h' : M ≃ₘ^n⟮I,I'⟯ M'} : h.to_equiv = h'.to_equiv ↔ h = h' :=
  to_equiv_injective.eq_iff

/-- Coercion to function `λ h : M ≃ₘ^n⟮I, I'⟯ M', (h : M → M')` is injective. -/
theorem coe_fn_injective : injective fun h : M ≃ₘ^n⟮I,I'⟯ M' x : M => h x :=
  Equivₓ.coe_fn_injective.comp to_equiv_injective

@[ext]
theorem ext {h h' : M ≃ₘ^n⟮I,I'⟯ M'} (Heq : ∀ x, h x = h' x) : h = h' :=
  coe_fn_injective $ funext Heq

section

variable (M I n)

/-- Identity map as a diffeomorphism. -/
protected def refl : M ≃ₘ^n⟮I,I⟯ M where
  times_cont_mdiff_to_fun := times_cont_mdiff_id
  times_cont_mdiff_inv_fun := times_cont_mdiff_id
  toEquiv := Equivₓ.refl M

@[simp]
theorem refl_to_equiv : (Diffeomorph.refl I M n).toEquiv = Equivₓ.refl _ :=
  rfl

@[simp]
theorem coe_refl : ⇑Diffeomorph.refl I M n = id :=
  rfl

end

/-- Composition of two diffeomorphisms. -/
protected def trans (h₁ : M ≃ₘ^n⟮I,I'⟯ M') (h₂ : M' ≃ₘ^n⟮I',J⟯ N) : M ≃ₘ^n⟮I,J⟯ N where
  times_cont_mdiff_to_fun := h₂.times_cont_mdiff_to_fun.comp h₁.times_cont_mdiff_to_fun
  times_cont_mdiff_inv_fun := h₁.times_cont_mdiff_inv_fun.comp h₂.times_cont_mdiff_inv_fun
  toEquiv := h₁.to_equiv.trans h₂.to_equiv

@[simp]
theorem trans_refl (h : M ≃ₘ^n⟮I,I'⟯ M') : h.trans (Diffeomorph.refl I' M' n) = h :=
  ext $ fun _ => rfl

@[simp]
theorem refl_trans (h : M ≃ₘ^n⟮I,I'⟯ M') : (Diffeomorph.refl I M n).trans h = h :=
  ext $ fun _ => rfl

@[simp]
theorem coeTransₓ (h₁ : M ≃ₘ^n⟮I,I'⟯ M') (h₂ : M' ≃ₘ^n⟮I',J⟯ N) : ⇑h₁.trans h₂ = h₂ ∘ h₁ :=
  rfl

/-- Inverse of a diffeomorphism. -/
protected def symm (h : M ≃ₘ^n⟮I,J⟯ N) : N ≃ₘ^n⟮J,I⟯ M where
  times_cont_mdiff_to_fun := h.times_cont_mdiff_inv_fun
  times_cont_mdiff_inv_fun := h.times_cont_mdiff_to_fun
  toEquiv := h.to_equiv.symm

@[simp]
theorem apply_symm_apply (h : M ≃ₘ^n⟮I,J⟯ N) (x : N) : h (h.symm x) = x :=
  h.to_equiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (h : M ≃ₘ^n⟮I,J⟯ N) (x : M) : h.symm (h x) = x :=
  h.to_equiv.symm_apply_apply x

@[simp]
theorem symm_refl : (Diffeomorph.refl I M n).symm = Diffeomorph.refl I M n :=
  ext $ fun _ => rfl

@[simp]
theorem self_trans_symm (h : M ≃ₘ^n⟮I,J⟯ N) : h.trans h.symm = Diffeomorph.refl I M n :=
  ext h.symm_apply_apply

@[simp]
theorem symm_trans_self (h : M ≃ₘ^n⟮I,J⟯ N) : h.symm.trans h = Diffeomorph.refl J N n :=
  ext h.apply_symm_apply

@[simp]
theorem symm_trans' (h₁ : M ≃ₘ^n⟮I,I'⟯ M') (h₂ : M' ≃ₘ^n⟮I',J⟯ N) : (h₁.trans h₂).symm = h₂.symm.trans h₁.symm :=
  rfl

@[simp]
theorem symm_to_equiv (h : M ≃ₘ^n⟮I,J⟯ N) : h.symm.to_equiv = h.to_equiv.symm :=
  rfl

@[simp, mfld_simps]
theorem to_equiv_coe_symm (h : M ≃ₘ^n⟮I,J⟯ N) : ⇑h.to_equiv.symm = h.symm :=
  rfl

theorem image_eq_preimage (h : M ≃ₘ^n⟮I,J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s :=
  h.to_equiv.image_eq_preimage s

theorem symm_image_eq_preimage (h : M ≃ₘ^n⟮I,J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s :=
  h.symm.image_eq_preimage s

@[simp, mfld_simps]
theorem range_comp {α} (h : M ≃ₘ^n⟮I,J⟯ N) (f : α → M) : range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp, image_eq_preimage]

@[simp]
theorem image_symm_image (h : M ≃ₘ^n⟮I,J⟯ N) (s : Set N) : h '' (h.symm '' s) = s :=
  h.to_equiv.image_symm_image s

@[simp]
theorem symm_image_image (h : M ≃ₘ^n⟮I,J⟯ N) (s : Set M) : h.symm '' (h '' s) = s :=
  h.to_equiv.symm_image_image s

/-- A diffeomorphism is a homeomorphism. -/
def to_homeomorph (h : M ≃ₘ^n⟮I,J⟯ N) : M ≃ₜ N :=
  ⟨h.to_equiv, h.continuous, h.symm.continuous⟩

@[simp]
theorem to_homeomorph_to_equiv (h : M ≃ₘ^n⟮I,J⟯ N) : h.to_homeomorph.to_equiv = h.to_equiv :=
  rfl

@[simp]
theorem symm_to_homeomorph (h : M ≃ₘ^n⟮I,J⟯ N) : h.symm.to_homeomorph = h.to_homeomorph.symm :=
  rfl

@[simp]
theorem coe_to_homeomorph (h : M ≃ₘ^n⟮I,J⟯ N) : ⇑h.to_homeomorph = h :=
  rfl

@[simp]
theorem coe_to_homeomorph_symm (h : M ≃ₘ^n⟮I,J⟯ N) : ⇑h.to_homeomorph.symm = h.symm :=
  rfl

@[simp]
theorem times_cont_mdiff_within_at_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : N → M'} {s x} (hm : m ≤ n) :
    TimesContMdiffWithinAt I I' m (f ∘ h) s x ↔ TimesContMdiffWithinAt J I' m f (h.symm ⁻¹' s) (h x) := by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh
    simpa only [· ∘ ·, h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.times_cont_mdiff_within_at.of_le hm) (maps_to_preimage _ _)
    
  · rw [← h.image_eq_preimage]
    exact fun hf => hf.comp x (h.times_cont_mdiff_within_at.of_le hm) (maps_to_image _ _)
    

@[simp]
theorem times_cont_mdiff_on_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : N → M'} {s} (hm : m ≤ n) :
    TimesContMdiffOn I I' m (f ∘ h) s ↔ TimesContMdiffOn J I' m f (h.symm ⁻¹' s) :=
  h.to_equiv.forall_congr $ fun x => by
    simp only [hm, coe_to_equiv, symm_apply_apply, times_cont_mdiff_within_at_comp_diffeomorph_iff, mem_preimage]

@[simp]
theorem times_cont_mdiff_at_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : N → M'} {x} (hm : m ≤ n) :
    TimesContMdiffAt I I' m (f ∘ h) x ↔ TimesContMdiffAt J I' m f (h x) :=
  h.times_cont_mdiff_within_at_comp_diffeomorph_iff hm

@[simp]
theorem times_cont_mdiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : N → M'} (hm : m ≤ n) :
    TimesContMdiff I I' m (f ∘ h) ↔ TimesContMdiff J I' m f :=
  h.to_equiv.forall_congr $ fun x => h.times_cont_mdiff_at_comp_diffeomorph_iff hm

@[simp]
theorem times_cont_mdiff_within_at_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : M' → M} (hm : m ≤ n) {s x} :
    TimesContMdiffWithinAt I' J m (h ∘ f) s x ↔ TimesContMdiffWithinAt I' I m f s x :=
  ⟨fun Hhf => by
    simpa only [· ∘ ·, h.symm_apply_apply] using
      (h.symm.times_cont_mdiff_at.of_le hm).comp_times_cont_mdiff_within_at _ Hhf,
    fun Hf => (h.times_cont_mdiff_at.of_le hm).comp_times_cont_mdiff_within_at _ Hf⟩

@[simp]
theorem times_cont_mdiff_at_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : M' → M} (hm : m ≤ n) {x} :
    TimesContMdiffAt I' J m (h ∘ f) x ↔ TimesContMdiffAt I' I m f x :=
  h.times_cont_mdiff_within_at_diffeomorph_comp_iff hm

@[simp]
theorem times_cont_mdiff_on_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : M' → M} (hm : m ≤ n) {s} :
    TimesContMdiffOn I' J m (h ∘ f) s ↔ TimesContMdiffOn I' I m f s :=
  forall_congrₓ $ fun x => forall_congrₓ $ fun hx => h.times_cont_mdiff_within_at_diffeomorph_comp_iff hm

@[simp]
theorem times_cont_mdiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : M' → M} (hm : m ≤ n) :
    TimesContMdiff I' J m (h ∘ f) ↔ TimesContMdiff I' I m f :=
  forall_congrₓ $ fun x => h.times_cont_mdiff_within_at_diffeomorph_comp_iff hm

theorem to_local_homeomorph_mdifferentiable (h : M ≃ₘ^n⟮I,J⟯ N) (hn : 1 ≤ n) :
    h.to_homeomorph.to_local_homeomorph.mdifferentiable I J :=
  ⟨h.mdifferentiable_on _ hn, h.symm.mdifferentiable_on _ hn⟩

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]

theorem unique_mdiff_on_image_aux (h : M ≃ₘ^n⟮I,J⟯ N) (hn : 1 ≤ n) {s : Set M} (hs : UniqueMdiffOn I s) :
    UniqueMdiffOn J (h '' s) := by
  convert hs.unique_mdiff_on_preimage (h.to_local_homeomorph_mdifferentiable hn)
  simp [h.image_eq_preimage]

@[simp]
theorem unique_mdiff_on_image (h : M ≃ₘ^n⟮I,J⟯ N) (hn : 1 ≤ n) {s : Set M} :
    UniqueMdiffOn J (h '' s) ↔ UniqueMdiffOn I s :=
  ⟨fun hs => h.symm_image_image s ▸ h.symm.unique_mdiff_on_image_aux hn hs, h.unique_mdiff_on_image_aux hn⟩

@[simp]
theorem unique_mdiff_on_preimage (h : M ≃ₘ^n⟮I,J⟯ N) (hn : 1 ≤ n) {s : Set N} :
    UniqueMdiffOn I (h ⁻¹' s) ↔ UniqueMdiffOn J s :=
  h.symm_image_eq_preimage s ▸ h.symm.unique_mdiff_on_image hn

@[simp]
theorem unique_diff_on_image (h : E ≃ₘ^n[𝕜] F) (hn : 1 ≤ n) {s : Set E} : UniqueDiffOn 𝕜 (h '' s) ↔ UniqueDiffOn 𝕜 s :=
  by
  simp only [← unique_mdiff_on_iff_unique_diff_on, unique_mdiff_on_image, hn]

@[simp]
theorem unique_diff_on_preimage (h : E ≃ₘ^n[𝕜] F) (hn : 1 ≤ n) {s : Set F} :
    UniqueDiffOn 𝕜 (h ⁻¹' s) ↔ UniqueDiffOn 𝕜 s :=
  h.symm_image_eq_preimage s ▸ h.symm.unique_diff_on_image hn

end Diffeomorph

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] E')

/-- A continuous linear equivalence between normed spaces is a diffeomorphism. -/
def to_diffeomorph : E ≃ₘ[𝕜] E' where
  times_cont_mdiff_to_fun := e.times_cont_diff.times_cont_mdiff
  times_cont_mdiff_inv_fun := e.symm.times_cont_diff.times_cont_mdiff
  toEquiv := e.to_linear_equiv.to_equiv

@[simp]
theorem coe_to_diffeomorph : ⇑e.to_diffeomorph = e :=
  rfl

@[simp]
theorem symm_to_diffeomorph : e.symm.to_diffeomorph = e.to_diffeomorph.symm :=
  rfl

@[simp]
theorem coe_to_diffeomorph_symm : ⇑e.to_diffeomorph.symm = e.symm :=
  rfl

end ContinuousLinearEquiv

namespace ModelWithCorners

variable (I) (e : E ≃ₘ[𝕜] E')

/-- Apply a diffeomorphism (e.g., a continuous linear equivalence) to the model vector space. -/
def trans_diffeomorph (I : ModelWithCorners 𝕜 E H) (e : E ≃ₘ[𝕜] E') : ModelWithCorners 𝕜 E' H where
  toLocalEquiv := I.to_local_equiv.trans e.to_equiv.to_local_equiv
  source_eq := by
    simp
  unique_diff' := by
    simp [range_comp e, I.unique_diff]
  continuous_to_fun := e.continuous.comp I.continuous
  continuous_inv_fun := I.continuous_symm.comp e.symm.continuous

@[simp, mfld_simps]
theorem coe_trans_diffeomorph : ⇑I.trans_diffeomorph e = e ∘ I :=
  rfl

@[simp, mfld_simps]
theorem coe_trans_diffeomorph_symm : ⇑(I.trans_diffeomorph e).symm = I.symm ∘ e.symm :=
  rfl

theorem trans_diffeomorph_range : range (I.trans_diffeomorph e) = e '' range I :=
  range_comp e I

theorem coe_ext_chart_at_trans_diffeomorph (x : M) : ⇑extChartAt (I.trans_diffeomorph e) x = e ∘ extChartAt I x :=
  rfl

theorem coe_ext_chart_at_trans_diffeomorph_symm (x : M) :
    ⇑(extChartAt (I.trans_diffeomorph e) x).symm = (extChartAt I x).symm ∘ e.symm :=
  rfl

theorem ext_chart_at_trans_diffeomorph_target (x : M) :
    (extChartAt (I.trans_diffeomorph e) x).Target = e.symm ⁻¹' (extChartAt I x).Target := by
  simp' only [range_comp e, e.image_eq_preimage, preimage_preimage] with mfld_simps

end ModelWithCorners

namespace Diffeomorph

variable (e : E ≃ₘ[𝕜] F)

instance smooth_manifold_with_corners_trans_diffeomorph [SmoothManifoldWithCorners I M] :
    SmoothManifoldWithCorners (I.trans_diffeomorph e) M := by
  refine' smooth_manifold_with_corners_of_times_cont_diff_on _ _ fun e₁ e₂ h₁ h₂ => _
  refine'
    e.times_cont_diff.comp_times_cont_diff_on
      (((timesContDiffGroupoid ⊤ I).compatible h₁ h₂).1.comp e.symm.times_cont_diff.times_cont_diff_on _)
  mfld_set_tac

variable (I M)

/-- The identity diffeomorphism between a manifold with model `I` and the same manifold
with model `I.trans_diffeomorph e`. -/
def to_trans_diffeomorph (e : E ≃ₘ[𝕜] F) : M ≃ₘ⟮I,I.trans_diffeomorph e⟯ M where
  toEquiv := Equivₓ.refl M
  times_cont_mdiff_to_fun := fun x => by
    refine' times_cont_mdiff_within_at_iff.2 ⟨continuous_within_at_id, _⟩
    refine' e.times_cont_diff.times_cont_diff_within_at.congr' (fun y hy => _) _
    · simp only [Equivₓ.coe_refl, id, · ∘ ·, I.coe_ext_chart_at_trans_diffeomorph, (extChartAt I x).right_inv hy.1]
      
    exact
      ⟨(extChartAt I x).map_source (mem_ext_chart_source I x), trivialₓ, by
        simp' only with mfld_simps⟩
  times_cont_mdiff_inv_fun := fun x => by
    refine' times_cont_mdiff_within_at_iff.2 ⟨continuous_within_at_id, _⟩
    refine' e.symm.times_cont_diff.times_cont_diff_within_at.congr' (fun y hy => _) _
    · simp only [mem_inter_eq, I.ext_chart_at_trans_diffeomorph_target] at hy
      simp only [Equivₓ.coe_refl, Equivₓ.refl_symm, id, · ∘ ·, I.coe_ext_chart_at_trans_diffeomorph_symm,
        (extChartAt I x).right_inv hy.1]
      
    exact
      ⟨(extChartAt _ x).map_source (mem_ext_chart_source _ x), trivialₓ, by
        simp' only [e.symm_apply_apply, Equivₓ.refl_symm, Equivₓ.coe_refl] with mfld_simps⟩

variable {I M}

@[simp]
theorem times_cont_mdiff_within_at_trans_diffeomorph_right {f : M' → M} {x s} :
    TimesContMdiffWithinAt I' (I.trans_diffeomorph e) n f s x ↔ TimesContMdiffWithinAt I' I n f s x :=
  (to_trans_diffeomorph I M e).times_cont_mdiff_within_at_diffeomorph_comp_iff le_top

@[simp]
theorem times_cont_mdiff_at_trans_diffeomorph_right {f : M' → M} {x} :
    TimesContMdiffAt I' (I.trans_diffeomorph e) n f x ↔ TimesContMdiffAt I' I n f x :=
  (to_trans_diffeomorph I M e).times_cont_mdiff_at_diffeomorph_comp_iff le_top

@[simp]
theorem times_cont_mdiff_on_trans_diffeomorph_right {f : M' → M} {s} :
    TimesContMdiffOn I' (I.trans_diffeomorph e) n f s ↔ TimesContMdiffOn I' I n f s :=
  (to_trans_diffeomorph I M e).times_cont_mdiff_on_diffeomorph_comp_iff le_top

@[simp]
theorem times_cont_mdiff_trans_diffeomorph_right {f : M' → M} :
    TimesContMdiff I' (I.trans_diffeomorph e) n f ↔ TimesContMdiff I' I n f :=
  (to_trans_diffeomorph I M e).times_cont_mdiff_diffeomorph_comp_iff le_top

@[simp]
theorem smooth_trans_diffeomorph_right {f : M' → M} : Smooth I' (I.trans_diffeomorph e) f ↔ Smooth I' I f :=
  times_cont_mdiff_trans_diffeomorph_right e

@[simp]
theorem times_cont_mdiff_within_at_trans_diffeomorph_left {f : M → M'} {x s} :
    TimesContMdiffWithinAt (I.trans_diffeomorph e) I' n f s x ↔ TimesContMdiffWithinAt I I' n f s x :=
  ((to_trans_diffeomorph I M e).times_cont_mdiff_within_at_comp_diffeomorph_iff le_top).symm

@[simp]
theorem times_cont_mdiff_at_trans_diffeomorph_left {f : M → M'} {x} :
    TimesContMdiffAt (I.trans_diffeomorph e) I' n f x ↔ TimesContMdiffAt I I' n f x :=
  ((to_trans_diffeomorph I M e).times_cont_mdiff_at_comp_diffeomorph_iff le_top).symm

@[simp]
theorem times_cont_mdiff_on_trans_diffeomorph_left {f : M → M'} {s} :
    TimesContMdiffOn (I.trans_diffeomorph e) I' n f s ↔ TimesContMdiffOn I I' n f s :=
  ((to_trans_diffeomorph I M e).times_cont_mdiff_on_comp_diffeomorph_iff le_top).symm

@[simp]
theorem times_cont_mdiff_trans_diffeomorph_left {f : M → M'} :
    TimesContMdiff (I.trans_diffeomorph e) I' n f ↔ TimesContMdiff I I' n f :=
  ((to_trans_diffeomorph I M e).times_cont_mdiff_comp_diffeomorph_iff le_top).symm

@[simp]
theorem smooth_trans_diffeomorph_left {f : M → M'} : Smooth (I.trans_diffeomorph e) I' f ↔ Smooth I I' f :=
  e.times_cont_mdiff_trans_diffeomorph_left

end Diffeomorph

