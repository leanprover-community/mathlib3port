/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Yury Kudryashov
-/
import Mathbin.Geometry.Manifold.ContMdiffMap

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


open Manifold TopologicalSpace

open Function Set

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type _}
  [TopologicalSpace H] {H' : Type _} [TopologicalSpace H'] {G : Type _} [TopologicalSpace G] {G' : Type _}
  [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {J : ModelWithCorners 𝕜 F G}
  {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type _} [TopologicalSpace N] [ChartedSpace G N] {N' : Type _} [TopologicalSpace N'] [ChartedSpace G' N'] {n : ℕ∞}

section Defs

variable (I I' M M' n)

/-- `n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to I and I'
-/
@[protect_proj, nolint has_nonempty_instance]
structure Diffeomorph extends M ≃ M' where
  cont_mdiff_to_fun : ContMdiff I I' n to_equiv
  cont_mdiff_inv_fun : ContMdiff I' I n to_equiv.symm

end Defs

-- mathport name: «expr ≃ₘ^ ⟮ , ⟯ »
localized [Manifold] notation M " ≃ₘ^" n:1000 "⟮" I "," J "⟯ " N => Diffeomorph I J M N n

-- mathport name: «expr ≃ₘ⟮ , ⟯ »
localized [Manifold] notation M " ≃ₘ⟮" I "," J "⟯ " N => Diffeomorph I J M N ⊤

-- mathport name: «expr ≃ₘ^ [ ] »
localized [Manifold]
  notation E " ≃ₘ^" n:1000 "[" 𝕜 "] " E' => Diffeomorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' n

-- mathport name: «expr ≃ₘ[ ] »
localized [Manifold]
  notation E " ≃ₘ[" 𝕜 "] " E' => Diffeomorph (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') E E' ⊤

namespace Diffeomorph

instance : CoeFun (M ≃ₘ^n⟮I,I'⟯ M') fun _ => M → M' :=
  ⟨fun e => e.toEquiv⟩

instance : Coe (M ≃ₘ^n⟮I,I'⟯ M') C^n⟮I, M; I', M'⟯ :=
  ⟨fun Φ => ⟨Φ, Φ.cont_mdiff_to_fun⟩⟩

@[continuity]
protected theorem continuous (h : M ≃ₘ^n⟮I,I'⟯ M') : Continuous h :=
  h.cont_mdiff_to_fun.Continuous

protected theorem cont_mdiff (h : M ≃ₘ^n⟮I,I'⟯ M') : ContMdiff I I' n h :=
  h.cont_mdiff_to_fun

protected theorem cont_mdiff_at (h : M ≃ₘ^n⟮I,I'⟯ M') {x} : ContMdiffAt I I' n h x :=
  h.ContMdiff.ContMdiffAt

protected theorem cont_mdiff_within_at (h : M ≃ₘ^n⟮I,I'⟯ M') {s x} : ContMdiffWithinAt I I' n h s x :=
  h.ContMdiffAt.ContMdiffWithinAt

protected theorem cont_diff (h : E ≃ₘ^n[𝕜] E') : ContDiff 𝕜 n h :=
  h.ContMdiff.ContDiff

protected theorem smooth (h : M ≃ₘ⟮I,I'⟯ M') : Smooth I I' h :=
  h.cont_mdiff_to_fun

protected theorem mdifferentiable (h : M ≃ₘ^n⟮I,I'⟯ M') (hn : 1 ≤ n) : Mdifferentiable I I' h :=
  h.ContMdiff.Mdifferentiable hn

protected theorem mdifferentiable_on (h : M ≃ₘ^n⟮I,I'⟯ M') (s : Set M) (hn : 1 ≤ n) : MdifferentiableOn I I' h s :=
  (h.Mdifferentiable hn).MdifferentiableOn

@[simp]
theorem coe_to_equiv (h : M ≃ₘ^n⟮I,I'⟯ M') : ⇑h.toEquiv = h :=
  rfl

@[simp, norm_cast]
theorem coe_coe (h : M ≃ₘ^n⟮I,I'⟯ M') : ⇑(h : C^n⟮I, M; I', M'⟯) = h :=
  rfl

theorem to_equiv_injective : Injective (Diffeomorph.toEquiv : (M ≃ₘ^n⟮I,I'⟯ M') → M ≃ M')
  | ⟨e, _, _⟩, ⟨e', _, _⟩, rfl => rfl

@[simp]
theorem to_equiv_inj {h h' : M ≃ₘ^n⟮I,I'⟯ M'} : h.toEquiv = h'.toEquiv ↔ h = h' :=
  to_equiv_injective.eq_iff

/-- Coercion to function `λ h : M ≃ₘ^n⟮I, I'⟯ M', (h : M → M')` is injective. -/
theorem coe_fn_injective : Injective fun (h : M ≃ₘ^n⟮I,I'⟯ M') (x : M) => h x :=
  Equivₓ.coe_fn_injective.comp to_equiv_injective

@[ext]
theorem ext {h h' : M ≃ₘ^n⟮I,I'⟯ M'} (Heq : ∀ x, h x = h' x) : h = h' :=
  coe_fn_injective <| funext Heq

section

variable (M I n)

/-- Identity map as a diffeomorphism. -/
protected def refl : M ≃ₘ^n⟮I,I⟯ M where
  cont_mdiff_to_fun := cont_mdiff_id
  cont_mdiff_inv_fun := cont_mdiff_id
  toEquiv := Equivₓ.refl M

@[simp]
theorem refl_to_equiv : (Diffeomorph.refl I M n).toEquiv = Equivₓ.refl _ :=
  rfl

@[simp]
theorem coe_refl : ⇑(Diffeomorph.refl I M n) = id :=
  rfl

end

/-- Composition of two diffeomorphisms. -/
protected def trans (h₁ : M ≃ₘ^n⟮I,I'⟯ M') (h₂ : M' ≃ₘ^n⟮I',J⟯ N) : M ≃ₘ^n⟮I,J⟯ N where
  cont_mdiff_to_fun := h₂.cont_mdiff_to_fun.comp h₁.cont_mdiff_to_fun
  cont_mdiff_inv_fun := h₁.cont_mdiff_inv_fun.comp h₂.cont_mdiff_inv_fun
  toEquiv := h₁.toEquiv.trans h₂.toEquiv

@[simp]
theorem trans_refl (h : M ≃ₘ^n⟮I,I'⟯ M') : h.trans (Diffeomorph.refl I' M' n) = h :=
  ext fun _ => rfl

@[simp]
theorem refl_trans (h : M ≃ₘ^n⟮I,I'⟯ M') : (Diffeomorph.refl I M n).trans h = h :=
  ext fun _ => rfl

@[simp]
theorem coe_trans (h₁ : M ≃ₘ^n⟮I,I'⟯ M') (h₂ : M' ≃ₘ^n⟮I',J⟯ N) : ⇑(h₁.trans h₂) = h₂ ∘ h₁ :=
  rfl

/-- Inverse of a diffeomorphism. -/
protected def symm (h : M ≃ₘ^n⟮I,J⟯ N) : N ≃ₘ^n⟮J,I⟯ M where
  cont_mdiff_to_fun := h.cont_mdiff_inv_fun
  cont_mdiff_inv_fun := h.cont_mdiff_to_fun
  toEquiv := h.toEquiv.symm

@[simp]
theorem apply_symm_apply (h : M ≃ₘ^n⟮I,J⟯ N) (x : N) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (h : M ≃ₘ^n⟮I,J⟯ N) (x : M) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

@[simp]
theorem symm_refl : (Diffeomorph.refl I M n).symm = Diffeomorph.refl I M n :=
  ext fun _ => rfl

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
theorem symm_to_equiv (h : M ≃ₘ^n⟮I,J⟯ N) : h.symm.toEquiv = h.toEquiv.symm :=
  rfl

@[simp, mfld_simps]
theorem to_equiv_coe_symm (h : M ≃ₘ^n⟮I,J⟯ N) : ⇑h.toEquiv.symm = h.symm :=
  rfl

theorem image_eq_preimage (h : M ≃ₘ^n⟮I,J⟯ N) (s : Set M) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage s

theorem symm_image_eq_preimage (h : M ≃ₘ^n⟮I,J⟯ N) (s : Set N) : h.symm '' s = h ⁻¹' s :=
  h.symm.image_eq_preimage s

@[simp, mfld_simps]
theorem range_comp {α} (h : M ≃ₘ^n⟮I,J⟯ N) (f : α → M) : Range (h ∘ f) = h.symm ⁻¹' Range f := by
  rw [range_comp, image_eq_preimage]

@[simp]
theorem image_symm_image (h : M ≃ₘ^n⟮I,J⟯ N) (s : Set N) : h '' (h.symm '' s) = s :=
  h.toEquiv.image_symm_image s

@[simp]
theorem symm_image_image (h : M ≃ₘ^n⟮I,J⟯ N) (s : Set M) : h.symm '' (h '' s) = s :=
  h.toEquiv.symm_image_image s

/-- A diffeomorphism is a homeomorphism. -/
def toHomeomorph (h : M ≃ₘ^n⟮I,J⟯ N) : M ≃ₜ N :=
  ⟨h.toEquiv, h.Continuous, h.symm.Continuous⟩

@[simp]
theorem to_homeomorph_to_equiv (h : M ≃ₘ^n⟮I,J⟯ N) : h.toHomeomorph.toEquiv = h.toEquiv :=
  rfl

@[simp]
theorem symm_to_homeomorph (h : M ≃ₘ^n⟮I,J⟯ N) : h.symm.toHomeomorph = h.toHomeomorph.symm :=
  rfl

@[simp]
theorem coe_to_homeomorph (h : M ≃ₘ^n⟮I,J⟯ N) : ⇑h.toHomeomorph = h :=
  rfl

@[simp]
theorem coe_to_homeomorph_symm (h : M ≃ₘ^n⟮I,J⟯ N) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl

@[simp]
theorem cont_mdiff_within_at_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : N → M'} {s x} (hm : m ≤ n) :
    ContMdiffWithinAt I I' m (f ∘ h) s x ↔ ContMdiffWithinAt J I' m f (h.symm ⁻¹' s) (h x) := by
  constructor
  · intro Hfh
    rw [← h.symm_apply_apply x] at Hfh
    simpa only [(· ∘ ·), h.apply_symm_apply] using
      Hfh.comp (h x) (h.symm.cont_mdiff_within_at.of_le hm) (maps_to_preimage _ _)
    
  · rw [← h.image_eq_preimage]
    exact fun hf => hf.comp x (h.cont_mdiff_within_at.of_le hm) (maps_to_image _ _)
    

@[simp]
theorem cont_mdiff_on_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : N → M'} {s} (hm : m ≤ n) :
    ContMdiffOn I I' m (f ∘ h) s ↔ ContMdiffOn J I' m f (h.symm ⁻¹' s) :=
  h.toEquiv.forall_congr fun x => by
    simp only [hm, coe_to_equiv, symm_apply_apply, cont_mdiff_within_at_comp_diffeomorph_iff, mem_preimage]

@[simp]
theorem cont_mdiff_at_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : N → M'} {x} (hm : m ≤ n) :
    ContMdiffAt I I' m (f ∘ h) x ↔ ContMdiffAt J I' m f (h x) :=
  h.cont_mdiff_within_at_comp_diffeomorph_iff hm

@[simp]
theorem cont_mdiff_comp_diffeomorph_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : N → M'} (hm : m ≤ n) :
    ContMdiff I I' m (f ∘ h) ↔ ContMdiff J I' m f :=
  h.toEquiv.forall_congr fun x => h.cont_mdiff_at_comp_diffeomorph_iff hm

@[simp]
theorem cont_mdiff_within_at_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : M' → M} (hm : m ≤ n) {s x} :
    ContMdiffWithinAt I' J m (h ∘ f) s x ↔ ContMdiffWithinAt I' I m f s x :=
  ⟨fun Hhf => by
    simpa only [(· ∘ ·), h.symm_apply_apply] using (h.symm.cont_mdiff_at.of_le hm).comp_cont_mdiff_within_at _ Hhf,
    fun Hf => (h.ContMdiffAt.of_le hm).comp_cont_mdiff_within_at _ Hf⟩

@[simp]
theorem cont_mdiff_at_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : M' → M} (hm : m ≤ n) {x} :
    ContMdiffAt I' J m (h ∘ f) x ↔ ContMdiffAt I' I m f x :=
  h.cont_mdiff_within_at_diffeomorph_comp_iff hm

@[simp]
theorem cont_mdiff_on_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : M' → M} (hm : m ≤ n) {s} :
    ContMdiffOn I' J m (h ∘ f) s ↔ ContMdiffOn I' I m f s :=
  forall₂_congrₓ fun x hx => h.cont_mdiff_within_at_diffeomorph_comp_iff hm

@[simp]
theorem cont_mdiff_diffeomorph_comp_iff {m} (h : M ≃ₘ^n⟮I,J⟯ N) {f : M' → M} (hm : m ≤ n) :
    ContMdiff I' J m (h ∘ f) ↔ ContMdiff I' I m f :=
  forall_congrₓ fun x => h.cont_mdiff_within_at_diffeomorph_comp_iff hm

theorem to_local_homeomorph_mdifferentiable (h : M ≃ₘ^n⟮I,J⟯ N) (hn : 1 ≤ n) :
    h.toHomeomorph.toLocalHomeomorph.Mdifferentiable I J :=
  ⟨h.MdifferentiableOn _ hn, h.symm.MdifferentiableOn _ hn⟩

section Constructions

/-- Product of two diffeomorphisms. -/
def prodCongr (h₁ : M ≃ₘ^n⟮I,I'⟯ M') (h₂ : N ≃ₘ^n⟮J,J'⟯ N') : (M × N) ≃ₘ^n⟮I.Prod J,I'.Prod J'⟯ M' × N' where
  cont_mdiff_to_fun := (h₁.ContMdiff.comp cont_mdiff_fst).prod_mk (h₂.ContMdiff.comp cont_mdiff_snd)
  cont_mdiff_inv_fun := (h₁.symm.ContMdiff.comp cont_mdiff_fst).prod_mk (h₂.symm.ContMdiff.comp cont_mdiff_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
theorem prod_congr_symm (h₁ : M ≃ₘ^n⟮I,I'⟯ M') (h₂ : N ≃ₘ^n⟮J,J'⟯ N') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
theorem coe_prod_congr (h₁ : M ≃ₘ^n⟮I,I'⟯ M') (h₂ : N ≃ₘ^n⟮J,J'⟯ N') : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (I J J' M N N' n)

/-- `M × N` is diffeomorphic to `N × M`. -/
def prodComm : (M × N) ≃ₘ^n⟮I.Prod J,J.Prod I⟯ N × M where
  cont_mdiff_to_fun := cont_mdiff_snd.prod_mk cont_mdiff_fst
  cont_mdiff_inv_fun := cont_mdiff_snd.prod_mk cont_mdiff_fst
  toEquiv := Equivₓ.prodComm M N

@[simp]
theorem prod_comm_symm : (prodComm I J M N n).symm = prodComm J I N M n :=
  rfl

@[simp]
theorem coe_prod_comm : ⇑(prodComm I J M N n) = Prod.swap :=
  rfl

/-- `(M × N) × N'` is diffeomorphic to `M × (N × N')`. -/
def prodAssoc : ((M × N) × N') ≃ₘ^n⟮(I.Prod J).Prod J',I.Prod (J.Prod J')⟯ M × N × N' where
  cont_mdiff_to_fun :=
    (cont_mdiff_fst.comp cont_mdiff_fst).prod_mk ((cont_mdiff_snd.comp cont_mdiff_fst).prod_mk cont_mdiff_snd)
  cont_mdiff_inv_fun :=
    (cont_mdiff_fst.prod_mk (cont_mdiff_fst.comp cont_mdiff_snd)).prod_mk (cont_mdiff_snd.comp cont_mdiff_snd)
  toEquiv := Equivₓ.prodAssoc M N N'

end

end Constructions

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
def toDiffeomorph : E ≃ₘ[𝕜] E' where
  cont_mdiff_to_fun := e.ContDiff.ContMdiff
  cont_mdiff_inv_fun := e.symm.ContDiff.ContMdiff
  toEquiv := e.toLinearEquiv.toEquiv

@[simp]
theorem coe_to_diffeomorph : ⇑e.toDiffeomorph = e :=
  rfl

@[simp]
theorem symm_to_diffeomorph : e.symm.toDiffeomorph = e.toDiffeomorph.symm :=
  rfl

@[simp]
theorem coe_to_diffeomorph_symm : ⇑e.toDiffeomorph.symm = e.symm :=
  rfl

end ContinuousLinearEquiv

namespace ModelWithCorners

variable (I) (e : E ≃ₘ[𝕜] E')

/-- Apply a diffeomorphism (e.g., a continuous linear equivalence) to the model vector space. -/
def transDiffeomorph (I : ModelWithCorners 𝕜 E H) (e : E ≃ₘ[𝕜] E') : ModelWithCorners 𝕜 E' H where
  toLocalEquiv := I.toLocalEquiv.trans e.toEquiv.toLocalEquiv
  source_eq := by
    simp
  unique_diff' := by
    simp [range_comp e, I.unique_diff]
  continuous_to_fun := e.Continuous.comp I.Continuous
  continuous_inv_fun := I.continuous_symm.comp e.symm.Continuous

@[simp, mfld_simps]
theorem coe_trans_diffeomorph : ⇑(I.transDiffeomorph e) = e ∘ I :=
  rfl

@[simp, mfld_simps]
theorem coe_trans_diffeomorph_symm : ⇑(I.transDiffeomorph e).symm = I.symm ∘ e.symm :=
  rfl

theorem trans_diffeomorph_range : Range (I.transDiffeomorph e) = e '' Range I :=
  range_comp e I

theorem coe_ext_chart_at_trans_diffeomorph (x : M) : ⇑(extChartAt (I.transDiffeomorph e) x) = e ∘ extChartAt I x :=
  rfl

theorem coe_ext_chart_at_trans_diffeomorph_symm (x : M) :
    ⇑(extChartAt (I.transDiffeomorph e) x).symm = (extChartAt I x).symm ∘ e.symm :=
  rfl

theorem ext_chart_at_trans_diffeomorph_target (x : M) :
    (extChartAt (I.transDiffeomorph e) x).Target = e.symm ⁻¹' (extChartAt I x).Target := by
  simp' only [range_comp e, e.image_eq_preimage, preimage_preimage] with mfld_simps

end ModelWithCorners

namespace Diffeomorph

variable (e : E ≃ₘ[𝕜] F)

instance smooth_manifold_with_corners_trans_diffeomorph [SmoothManifoldWithCorners I M] :
    SmoothManifoldWithCorners (I.transDiffeomorph e) M := by
  refine' smooth_manifold_with_corners_of_cont_diff_on _ _ fun e₁ e₂ h₁ h₂ => _
  refine'
    e.cont_diff.comp_cont_diff_on (((contDiffGroupoid ⊤ I).compatible h₁ h₂).1.comp e.symm.cont_diff.cont_diff_on _)
  mfld_set_tac

variable (I M)

/-- The identity diffeomorphism between a manifold with model `I` and the same manifold
with model `I.trans_diffeomorph e`. -/
def toTransDiffeomorph (e : E ≃ₘ[𝕜] F) : M ≃ₘ⟮I,I.transDiffeomorph e⟯ M where
  toEquiv := Equivₓ.refl M
  cont_mdiff_to_fun := fun x => by
    refine' cont_mdiff_within_at_iff'.2 ⟨continuous_within_at_id, _⟩
    refine' e.cont_diff.cont_diff_within_at.congr' (fun y hy => _) _
    · simp only [Equivₓ.coe_refl, id, (· ∘ ·), I.coe_ext_chart_at_trans_diffeomorph, (extChartAt I x).right_inv hy.1]
      
    exact
      ⟨(extChartAt I x).map_source (mem_ext_chart_source I x), trivialₓ, by
        simp' only with mfld_simps⟩
  cont_mdiff_inv_fun := fun x => by
    refine' cont_mdiff_within_at_iff'.2 ⟨continuous_within_at_id, _⟩
    refine' e.symm.cont_diff.cont_diff_within_at.congr' (fun y hy => _) _
    · simp only [mem_inter_eq, I.ext_chart_at_trans_diffeomorph_target] at hy
      simp only [Equivₓ.coe_refl, Equivₓ.refl_symm, id, (· ∘ ·), I.coe_ext_chart_at_trans_diffeomorph_symm,
        (extChartAt I x).right_inv hy.1]
      
    exact
      ⟨(extChartAt _ x).map_source (mem_ext_chart_source _ x), trivialₓ, by
        simp' only [e.symm_apply_apply, Equivₓ.refl_symm, Equivₓ.coe_refl] with mfld_simps⟩

variable {I M}

@[simp]
theorem cont_mdiff_within_at_trans_diffeomorph_right {f : M' → M} {x s} :
    ContMdiffWithinAt I' (I.transDiffeomorph e) n f s x ↔ ContMdiffWithinAt I' I n f s x :=
  (toTransDiffeomorph I M e).cont_mdiff_within_at_diffeomorph_comp_iff le_top

@[simp]
theorem cont_mdiff_at_trans_diffeomorph_right {f : M' → M} {x} :
    ContMdiffAt I' (I.transDiffeomorph e) n f x ↔ ContMdiffAt I' I n f x :=
  (toTransDiffeomorph I M e).cont_mdiff_at_diffeomorph_comp_iff le_top

@[simp]
theorem cont_mdiff_on_trans_diffeomorph_right {f : M' → M} {s} :
    ContMdiffOn I' (I.transDiffeomorph e) n f s ↔ ContMdiffOn I' I n f s :=
  (toTransDiffeomorph I M e).cont_mdiff_on_diffeomorph_comp_iff le_top

@[simp]
theorem cont_mdiff_trans_diffeomorph_right {f : M' → M} :
    ContMdiff I' (I.transDiffeomorph e) n f ↔ ContMdiff I' I n f :=
  (toTransDiffeomorph I M e).cont_mdiff_diffeomorph_comp_iff le_top

@[simp]
theorem smooth_trans_diffeomorph_right {f : M' → M} : Smooth I' (I.transDiffeomorph e) f ↔ Smooth I' I f :=
  cont_mdiff_trans_diffeomorph_right e

@[simp]
theorem cont_mdiff_within_at_trans_diffeomorph_left {f : M → M'} {x s} :
    ContMdiffWithinAt (I.transDiffeomorph e) I' n f s x ↔ ContMdiffWithinAt I I' n f s x :=
  ((toTransDiffeomorph I M e).cont_mdiff_within_at_comp_diffeomorph_iff le_top).symm

@[simp]
theorem cont_mdiff_at_trans_diffeomorph_left {f : M → M'} {x} :
    ContMdiffAt (I.transDiffeomorph e) I' n f x ↔ ContMdiffAt I I' n f x :=
  ((toTransDiffeomorph I M e).cont_mdiff_at_comp_diffeomorph_iff le_top).symm

@[simp]
theorem cont_mdiff_on_trans_diffeomorph_left {f : M → M'} {s} :
    ContMdiffOn (I.transDiffeomorph e) I' n f s ↔ ContMdiffOn I I' n f s :=
  ((toTransDiffeomorph I M e).cont_mdiff_on_comp_diffeomorph_iff le_top).symm

@[simp]
theorem cont_mdiff_trans_diffeomorph_left {f : M → M'} : ContMdiff (I.transDiffeomorph e) I' n f ↔ ContMdiff I I' n f :=
  ((toTransDiffeomorph I M e).cont_mdiff_comp_diffeomorph_iff le_top).symm

@[simp]
theorem smooth_trans_diffeomorph_left {f : M → M'} : Smooth (I.transDiffeomorph e) I' f ↔ Smooth I I' f :=
  e.cont_mdiff_trans_diffeomorph_left

end Diffeomorph

