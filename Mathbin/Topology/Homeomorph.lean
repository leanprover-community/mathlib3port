import Mathbin.Topology.DenseEmbedding 
import Mathbin.Data.Equiv.Fin

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

# Main definitions

* `homeomorph α β`: The type of homeomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ₜ β`.

# Main results

* Pretty much every topological property is preserved under homeomorphisms.
* `homeomorph.homeomorph_of_continuous_open`: A continuous bijection that is
  an open map is a homeomorphism.

-/


open Set Filter

open_locale TopologicalSpace

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

/-- Homeomorphism between `α` and `β`, also called topological isomorphism -/
@[nolint has_inhabited_instance]
structure Homeomorph (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] extends α ≃ β where 
  continuous_to_fun : Continuous to_fun :=  by 
  runTac 
    tactic.interactive.continuity' 
  continuous_inv_fun : Continuous inv_fun :=  by 
  runTac 
    tactic.interactive.continuity'

infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

instance : CoeFun (α ≃ₜ β) fun _ => α → β :=
  ⟨fun e => e.to_equiv⟩

@[simp]
theorem homeomorph_mk_coe (a : Equiv α β) b c : (Homeomorph.mk a b c : α → β) = a :=
  rfl

@[simp]
theorem coe_to_equiv (h : α ≃ₜ β) : «expr⇑ » h.to_equiv = h :=
  rfl

/-- Inverse of a homeomorphism. -/
protected def symm (h : α ≃ₜ β) : β ≃ₜ α :=
  { continuous_to_fun := h.continuous_inv_fun, continuous_inv_fun := h.continuous_to_fun, toEquiv := h.to_equiv.symm }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : α ≃ₜ β) : α → β :=
  h

/-- See Note [custom simps projection] -/
def simps.symm_apply (h : α ≃ₜ β) : β → α :=
  h.symm

initialize_simps_projections Homeomorph (to_equiv_to_fun → apply, to_equiv_inv_fun → symmApply, -toEquiv)

theorem to_equiv_injective : Function.Injective (to_equiv : α ≃ₜ β → α ≃ β)
| ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, rfl => rfl

@[ext]
theorem ext {h h' : α ≃ₜ β} (H : ∀ x, h x = h' x) : h = h' :=
  to_equiv_injective$ Equiv.ext H

/-- Identity map as a homeomorphism. -/
@[simps (config := { fullyApplied := ff }) apply]
protected def refl (α : Type _) [TopologicalSpace α] : α ≃ₜ α :=
  { continuous_to_fun := continuous_id, continuous_inv_fun := continuous_id, toEquiv := Equiv.refl α }

/-- Composition of two homeomorphisms. -/
protected def trans (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ :=
  { continuous_to_fun := h₂.continuous_to_fun.comp h₁.continuous_to_fun,
    continuous_inv_fun := h₁.continuous_inv_fun.comp h₂.continuous_inv_fun,
    toEquiv := Equiv.trans h₁.to_equiv h₂.to_equiv }

@[simp]
theorem homeomorph_mk_coe_symm (a : Equiv α β) b c : ((Homeomorph.mk a b c).symm : β → α) = a.symm :=
  rfl

@[simp]
theorem refl_symm : (Homeomorph.refl α).symm = Homeomorph.refl α :=
  rfl

@[continuity]
protected theorem Continuous (h : α ≃ₜ β) : Continuous h :=
  h.continuous_to_fun

@[continuity]
protected theorem continuous_symm (h : α ≃ₜ β) : Continuous h.symm :=
  h.continuous_inv_fun

@[simp]
theorem apply_symm_apply (h : α ≃ₜ β) (x : β) : h (h.symm x) = x :=
  h.to_equiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (h : α ≃ₜ β) (x : α) : h.symm (h x) = x :=
  h.to_equiv.symm_apply_apply x

protected theorem bijective (h : α ≃ₜ β) : Function.Bijective h :=
  h.to_equiv.bijective

protected theorem injective (h : α ≃ₜ β) : Function.Injective h :=
  h.to_equiv.injective

protected theorem surjective (h : α ≃ₜ β) : Function.Surjective h :=
  h.to_equiv.surjective

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def change_inv (f : α ≃ₜ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ₜ β :=
  have  : g = f.symm :=
    funext
      fun x =>
        calc g x = f.symm (f (g x)) := (f.left_inv (g x)).symm 
          _ = f.symm x :=
          by 
            rw [hg x]
          
  { toFun := f, invFun := g,
    left_inv :=
      by 
        convert f.left_inv,
    right_inv :=
      by 
        convert f.right_inv,
    continuous_to_fun := f.continuous,
    continuous_inv_fun :=
      by 
        convert f.symm.continuous }

@[simp]
theorem symm_comp_self (h : α ≃ₜ β) : («expr⇑ » h.symm ∘ «expr⇑ » h) = id :=
  funext h.symm_apply_apply

@[simp]
theorem self_comp_symm (h : α ≃ₜ β) : («expr⇑ » h ∘ «expr⇑ » h.symm) = id :=
  funext h.apply_symm_apply

@[simp]
theorem range_coe (h : α ≃ₜ β) : range h = univ :=
  h.surjective.range_eq

theorem image_symm (h : α ≃ₜ β) : image h.symm = preimage h :=
  funext h.symm.to_equiv.image_eq_preimage

theorem preimage_symm (h : α ≃ₜ β) : preimage h.symm = image h :=
  (funext h.to_equiv.image_eq_preimage).symm

@[simp]
theorem image_preimage (h : α ≃ₜ β) (s : Set β) : h '' (h ⁻¹' s) = s :=
  h.to_equiv.image_preimage s

@[simp]
theorem preimage_image (h : α ≃ₜ β) (s : Set α) : h ⁻¹' (h '' s) = s :=
  h.to_equiv.preimage_image s

protected theorem Inducing (h : α ≃ₜ β) : Inducing h :=
  inducing_of_inducing_compose h.continuous h.symm.continuous$
    by 
      simp only [symm_comp_self, inducing_id]

theorem induced_eq (h : α ≃ₜ β) : TopologicalSpace.induced h ‹_› = ‹_› :=
  h.inducing.1.symm

protected theorem QuotientMap (h : α ≃ₜ β) : QuotientMap h :=
  QuotientMap.of_quotient_map_compose h.symm.continuous h.continuous$
    by 
      simp only [self_comp_symm, QuotientMap.id]

theorem coinduced_eq (h : α ≃ₜ β) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.quotient_map.2.symm

protected theorem Embedding (h : α ≃ₜ β) : Embedding h :=
  ⟨h.inducing, h.injective⟩

/-- Homeomorphism given an embedding. -/
noncomputable def of_embedding (f : α → β) (hf : Embedding f) : α ≃ₜ Set.Range f :=
  { Equiv.ofInjective f hf.inj with continuous_to_fun := continuous_subtype_mk _ hf.continuous,
    continuous_inv_fun :=
      by 
        simp [hf.continuous_iff, continuous_subtype_coe] }

protected theorem second_countable_topology [TopologicalSpace.SecondCountableTopology β] (h : α ≃ₜ β) :
  TopologicalSpace.SecondCountableTopology α :=
  h.inducing.second_countable_topology

theorem compact_image {s : Set α} (h : α ≃ₜ β) : IsCompact (h '' s) ↔ IsCompact s :=
  h.embedding.is_compact_iff_is_compact_image.symm

theorem compact_preimage {s : Set β} (h : α ≃ₜ β) : IsCompact (h ⁻¹' s) ↔ IsCompact s :=
  by 
    rw [←image_symm] <;> exact h.symm.compact_image

theorem CompactSpace [CompactSpace α] (h : α ≃ₜ β) : CompactSpace β :=
  { compact_univ :=
      by 
        rw [←image_univ_of_surjective h.surjective, h.compact_image]
        apply CompactSpace.compact_univ }

theorem T2Space [T2Space α] (h : α ≃ₜ β) : T2Space β :=
  { t2 :=
      by 
        intro x y hxy 
        obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation (h.symm.injective.ne hxy)
        refine'
          ⟨h.symm ⁻¹' u, h.symm ⁻¹' v, h.symm.continuous.is_open_preimage _ hu, h.symm.continuous.is_open_preimage _ hv,
            hxu, hyv, _⟩
        rw [←preimage_inter, huv, preimage_empty] }

protected theorem DenseEmbedding (h : α ≃ₜ β) : DenseEmbedding h :=
  { h.embedding with dense := h.surjective.dense_range }

@[simp]
theorem is_open_preimage (h : α ≃ₜ β) {s : Set β} : IsOpen (h ⁻¹' s) ↔ IsOpen s :=
  h.quotient_map.is_open_preimage

@[simp]
theorem is_open_image (h : α ≃ₜ β) {s : Set α} : IsOpen (h '' s) ↔ IsOpen s :=
  by 
    rw [←preimage_symm, is_open_preimage]

@[simp]
theorem is_closed_preimage (h : α ≃ₜ β) {s : Set β} : IsClosed (h ⁻¹' s) ↔ IsClosed s :=
  by 
    simp only [←is_open_compl_iff, ←preimage_compl, is_open_preimage]

@[simp]
theorem is_closed_image (h : α ≃ₜ β) {s : Set α} : IsClosed (h '' s) ↔ IsClosed s :=
  by 
    rw [←preimage_symm, is_closed_preimage]

theorem preimage_closure (h : α ≃ₜ β) (s : Set β) : h ⁻¹' Closure s = Closure (h ⁻¹' s) :=
  by 
    rw [h.embedding.closure_eq_preimage_closure_image, h.image_preimage]

theorem image_closure (h : α ≃ₜ β) (s : Set α) : h '' Closure s = Closure (h '' s) :=
  by 
    rw [←preimage_symm, preimage_closure]

protected theorem IsOpenMap (h : α ≃ₜ β) : IsOpenMap h :=
  fun s => h.is_open_image.2

protected theorem IsClosedMap (h : α ≃ₜ β) : IsClosedMap h :=
  fun s => h.is_closed_image.2

protected theorem OpenEmbedding (h : α ≃ₜ β) : OpenEmbedding h :=
  open_embedding_of_embedding_open h.embedding h.is_open_map

protected theorem ClosedEmbedding (h : α ≃ₜ β) : ClosedEmbedding h :=
  closed_embedding_of_embedding_closed h.embedding h.is_closed_map

@[simp]
theorem map_nhds_eq (h : α ≃ₜ β) (x : α) : map h (𝓝 x) = 𝓝 (h x) :=
  h.embedding.map_nhds_of_mem _
    (by 
      simp )

theorem symm_map_nhds_eq (h : α ≃ₜ β) (x : α) : map h.symm (𝓝 (h x)) = 𝓝 x :=
  by 
    rw [h.symm.map_nhds_eq, h.symm_apply_apply]

theorem nhds_eq_comap (h : α ≃ₜ β) (x : α) : 𝓝 x = comap h (𝓝 (h x)) :=
  h.embedding.to_inducing.nhds_eq_comap x

@[simp]
theorem comap_nhds_eq (h : α ≃ₜ β) (y : β) : comap h (𝓝 y) = 𝓝 (h.symm y) :=
  by 
    rw [h.nhds_eq_comap, h.apply_symm_apply]

/-- If an bijective map `e : α ≃ β` is continuous and open, then it is a homeomorphism. -/
def homeomorph_of_continuous_open (e : α ≃ β) (h₁ : Continuous e) (h₂ : IsOpenMap e) : α ≃ₜ β :=
  { continuous_to_fun := h₁,
    continuous_inv_fun :=
      by 
        rw [continuous_def]
        intro s hs 
        convert ← h₂ s hs using 1
        apply e.image_eq_preimage,
    toEquiv := e }

@[simp]
theorem comp_continuous_on_iff (h : α ≃ₜ β) (f : γ → α) (s : Set γ) : ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.inducing.continuous_on_iff.symm

@[simp]
theorem comp_continuous_iff (h : α ≃ₜ β) {f : γ → α} : Continuous (h ∘ f) ↔ Continuous f :=
  h.inducing.continuous_iff.symm

@[simp]
theorem comp_continuous_iff' (h : α ≃ₜ β) {f : β → γ} : Continuous (f ∘ h) ↔ Continuous f :=
  h.quotient_map.continuous_iff.symm

theorem comp_continuous_at_iff (h : α ≃ₜ β) (f : γ → α) (x : γ) : ContinuousAt (h ∘ f) x ↔ ContinuousAt f x :=
  h.inducing.continuous_at_iff.symm

theorem comp_continuous_at_iff' (h : α ≃ₜ β) (f : β → γ) (x : α) : ContinuousAt (f ∘ h) x ↔ ContinuousAt f (h x) :=
  h.inducing.continuous_at_iff'
    (by 
      simp )

theorem comp_continuous_within_at_iff (h : α ≃ₜ β) (f : γ → α) (s : Set γ) (x : γ) :
  ContinuousWithinAt f s x ↔ ContinuousWithinAt (h ∘ f) s x :=
  h.inducing.continuous_within_at_iff

@[simp]
theorem comp_is_open_map_iff (h : α ≃ₜ β) {f : γ → α} : IsOpenMap (h ∘ f) ↔ IsOpenMap f :=
  by 
    refine' ⟨_, fun hf => h.is_open_map.comp hf⟩
    intro hf 
    rw [←Function.comp.left_id f, ←h.symm_comp_self, Function.comp.assoc]
    exact h.symm.is_open_map.comp hf

@[simp]
theorem comp_is_open_map_iff' (h : α ≃ₜ β) {f : β → γ} : IsOpenMap (f ∘ h) ↔ IsOpenMap f :=
  by 
    refine' ⟨_, fun hf => hf.comp h.is_open_map⟩
    intro hf 
    rw [←Function.comp.right_id f, ←h.self_comp_symm, ←Function.comp.assoc]
    exact hf.comp h.symm.is_open_map

/-- If two sets are equal, then they are homeomorphic. -/
def set_congr {s t : Set α} (h : s = t) : s ≃ₜ t :=
  { continuous_to_fun := continuous_subtype_mk _ continuous_subtype_val,
    continuous_inv_fun := continuous_subtype_mk _ continuous_subtype_val, toEquiv := Equiv.setCongr h }

/-- Sum of two homeomorphisms. -/
def sum_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : Sum α γ ≃ₜ Sum β δ :=
  { continuous_to_fun :=
      by 
        convert continuous_sum_rec (continuous_inl.comp h₁.continuous) (continuous_inr.comp h₂.continuous)
        ext x 
        cases x <;> rfl,
    continuous_inv_fun :=
      by 
        convert continuous_sum_rec (continuous_inl.comp h₁.symm.continuous) (continuous_inr.comp h₂.symm.continuous)
        ext x 
        cases x <;> rfl,
    toEquiv := h₁.to_equiv.sum_congr h₂.to_equiv }

/-- Product of two homeomorphisms. -/
def prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α × γ ≃ₜ β × δ :=
  { continuous_to_fun := (h₁.continuous.comp continuous_fst).prod_mk (h₂.continuous.comp continuous_snd),
    continuous_inv_fun := (h₁.symm.continuous.comp continuous_fst).prod_mk (h₂.symm.continuous.comp continuous_snd),
    toEquiv := h₁.to_equiv.prod_congr h₂.to_equiv }

@[simp]
theorem prod_congr_symm (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : (h₁.prod_congr h₂).symm = h₁.symm.prod_congr h₂.symm :=
  rfl

@[simp]
theorem coe_prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : «expr⇑ » (h₁.prod_congr h₂) = Prod.map h₁ h₂ :=
  rfl

section 

variable (α β γ)

/-- `α × β` is homeomorphic to `β × α`. -/
def prod_comm : α × β ≃ₜ β × α :=
  { continuous_to_fun := continuous_snd.prod_mk continuous_fst,
    continuous_inv_fun := continuous_snd.prod_mk continuous_fst, toEquiv := Equiv.prodComm α β }

@[simp]
theorem prod_comm_symm : (prod_comm α β).symm = prod_comm β α :=
  rfl

@[simp]
theorem coe_prod_comm : «expr⇑ » (prod_comm α β) = Prod.swap :=
  rfl

/-- `(α × β) × γ` is homeomorphic to `α × (β × γ)`. -/
def prod_assoc : (α × β) × γ ≃ₜ α × β × γ :=
  { continuous_to_fun :=
      (continuous_fst.comp continuous_fst).prod_mk ((continuous_snd.comp continuous_fst).prod_mk continuous_snd),
    continuous_inv_fun :=
      (continuous_fst.prod_mk (continuous_fst.comp continuous_snd)).prod_mk (continuous_snd.comp continuous_snd),
    toEquiv := Equiv.prodAssoc α β γ }

/-- `α × {*}` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := ff }) apply]
def prod_punit : α × PUnit ≃ₜ α :=
  { toEquiv := Equiv.prodPunit α, continuous_to_fun := continuous_fst,
    continuous_inv_fun := continuous_id.prod_mk continuous_const }

/-- `{*} × α` is homeomorphic to `α`. -/
def punit_prod : PUnit × α ≃ₜ α :=
  (prod_comm _ _).trans (prod_punit _)

@[simp]
theorem coe_punit_prod : «expr⇑ » (punit_prod α) = Prod.snd :=
  rfl

end 

/-- `ulift α` is homeomorphic to `α`. -/
def Ulift.{u, v} {α : Type u} [TopologicalSpace α] : Ulift.{v, u} α ≃ₜ α :=
  { continuous_to_fun := continuous_ulift_down, continuous_inv_fun := continuous_ulift_up, toEquiv := Equiv.ulift }

section Distrib

/-- `(α ⊕ β) × γ` is homeomorphic to `α × γ ⊕ β × γ`. -/
def sum_prod_distrib : Sum α β × γ ≃ₜ Sum (α × γ) (β × γ) :=
  by 
    refine' (Homeomorph.homeomorphOfContinuousOpen (Equiv.sumProdDistrib α β γ).symm _ _).symm
    ·
      convert
        continuous_sum_rec ((continuous_inl.comp continuous_fst).prod_mk continuous_snd)
          ((continuous_inr.comp continuous_fst).prod_mk continuous_snd)
      ext1 x 
      cases x <;> rfl
    ·
      exact
        is_open_map_sum (open_embedding_inl.prod open_embedding_id).IsOpenMap
          (open_embedding_inr.prod open_embedding_id).IsOpenMap

/-- `α × (β ⊕ γ)` is homeomorphic to `α × β ⊕ α × γ`. -/
def prod_sum_distrib : α × Sum β γ ≃ₜ Sum (α × β) (α × γ) :=
  (prod_comm _ _).trans$ sum_prod_distrib.trans$ sum_congr (prod_comm _ _) (prod_comm _ _)

variable {ι : Type _} {σ : ι → Type _} [∀ i, TopologicalSpace (σ i)]

/-- `(Σ i, σ i) × β` is homeomorphic to `Σ i, (σ i × β)`. -/
def sigma_prod_distrib : (Σi, σ i) × β ≃ₜ Σi, σ i × β :=
  Homeomorph.symm$
    homeomorph_of_continuous_open (Equiv.sigmaProdDistrib σ β).symm
      (continuous_sigma$ fun i => (continuous_sigma_mk.comp continuous_fst).prod_mk continuous_snd)
      (is_open_map_sigma$ fun i => (open_embedding_sigma_mk.Prod open_embedding_id).IsOpenMap)

end Distrib

/-- If `ι` has a unique element, then `ι → α` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := ff })]
def fun_unique (ι α : Type _) [Unique ι] [TopologicalSpace α] : (ι → α) ≃ₜ α :=
  { toEquiv := Equiv.funUnique ι α, continuous_to_fun := continuous_apply _,
    continuous_inv_fun := continuous_pi fun _ => continuous_id }

/-- Homeomorphism between dependent functions `Π i : fin 2, α i` and `α 0 × α 1`. -/
@[simps (config := { fullyApplied := ff })]
def pi_fin_two.{u} (α : Finₓ 2 → Type u) [∀ i, TopologicalSpace (α i)] : (∀ i, α i) ≃ₜ α 0 × α 1 :=
  { toEquiv := piFinTwoEquiv α, continuous_to_fun := (continuous_apply 0).prod_mk (continuous_apply 1),
    continuous_inv_fun := continuous_pi$ Finₓ.forall_fin_two.2 ⟨continuous_fst, continuous_snd⟩ }

/-- Homeomorphism between `α² = fin 2 → α` and `α × α`. -/
@[simps (config := { fullyApplied := ff })]
def fin_two_arrow : (Finₓ 2 → α) ≃ₜ α × α :=
  { pi_fin_two fun _ => α with toEquiv := finTwoArrowEquiv α }

/--
A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
def image (e : α ≃ₜ β) (s : Set α) : s ≃ₜ e '' s :=
  { e.to_equiv.image s with
    continuous_to_fun :=
      by 
        continuity!,
    continuous_inv_fun :=
      by 
        continuity! }

end Homeomorph

