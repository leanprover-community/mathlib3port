/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton,
Anatole Dedecker
-/
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.Pi

/-!
# Uniform isomorphisms

This file defines uniform isomorphisms between two uniform spaces. They are bijections with both
directions uniformly continuous. We denote uniform isomorphisms with the notation `≃ᵤ`.

# Main definitions

* `uniform_equiv α β`: The type of uniform isomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ᵤ β`.

-/


open Set Filter

universe u v

variable {α : Type u} {β : Type _} {γ : Type _} {δ : Type _}

-- not all spaces are homeomorphic to each other
/-- Uniform isomorphism between `α` and `β` -/
@[nolint has_nonempty_instance]
structure UniformEquiv (α : Type _) (β : Type _) [UniformSpace α] [UniformSpace β] extends α ≃ β where
  uniform_continuous_to_fun : UniformContinuous to_fun
  uniform_continuous_inv_fun : UniformContinuous inv_fun
#align uniform_equiv UniformEquiv

-- mathport name: «expr ≃ᵤ »
infixl:25 " ≃ᵤ " => UniformEquiv

namespace UniformEquiv

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]

instance : CoeFun (α ≃ᵤ β) fun _ => α → β :=
  ⟨fun e => e.toEquiv⟩

@[simp]
theorem uniform_equiv_mk_coe (a : Equiv α β) (b c) : (UniformEquiv.mk a b c : α → β) = a :=
  rfl
#align uniform_equiv.uniform_equiv_mk_coe UniformEquiv.uniform_equiv_mk_coe

/-- Inverse of a uniform isomorphism. -/
protected def symm (h : α ≃ᵤ β) : β ≃ᵤ α where
  uniform_continuous_to_fun := h.uniform_continuous_inv_fun
  uniform_continuous_inv_fun := h.uniform_continuous_to_fun
  toEquiv := h.toEquiv.symm
#align uniform_equiv.symm UniformEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵤ β) : α → β :=
  h
#align uniform_equiv.simps.apply UniformEquiv.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symmApply (h : α ≃ᵤ β) : β → α :=
  h.symm
#align uniform_equiv.simps.symm_apply UniformEquiv.Simps.symmApply

initialize_simps_projections UniformEquiv (to_equiv_to_fun → apply, to_equiv_inv_fun → symmApply, -toEquiv)

@[simp]
theorem coe_to_equiv (h : α ≃ᵤ β) : ⇑h.toEquiv = h :=
  rfl
#align uniform_equiv.coe_to_equiv UniformEquiv.coe_to_equiv

@[simp]
theorem coe_symm_to_equiv (h : α ≃ᵤ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl
#align uniform_equiv.coe_symm_to_equiv UniformEquiv.coe_symm_to_equiv

theorem to_equiv_injective : Function.Injective (toEquiv : α ≃ᵤ β → α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, rfl => rfl
#align uniform_equiv.to_equiv_injective UniformEquiv.to_equiv_injective

@[ext.1]
theorem ext {h h' : α ≃ᵤ β} (H : ∀ x, h x = h' x) : h = h' :=
  to_equiv_injective <| Equiv.ext H
#align uniform_equiv.ext UniformEquiv.ext

/-- Identity map as a uniform isomorphism. -/
@[simps (config := { fullyApplied := false }) apply]
protected def refl (α : Type _) [UniformSpace α] : α ≃ᵤ α where
  uniform_continuous_to_fun := uniform_continuous_id
  uniform_continuous_inv_fun := uniform_continuous_id
  toEquiv := Equiv.refl α
#align uniform_equiv.refl UniformEquiv.refl

/-- Composition of two uniform isomorphisms. -/
protected def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ where
  uniform_continuous_to_fun := h₂.uniform_continuous_to_fun.comp h₁.uniform_continuous_to_fun
  uniform_continuous_inv_fun := h₁.uniform_continuous_inv_fun.comp h₂.uniform_continuous_inv_fun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
#align uniform_equiv.trans UniformEquiv.trans

@[simp]
theorem trans_apply (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl
#align uniform_equiv.trans_apply UniformEquiv.trans_apply

@[simp]
theorem uniform_equiv_mk_coe_symm (a : Equiv α β) (b c) : ((UniformEquiv.mk a b c).symm : β → α) = a.symm :=
  rfl
#align uniform_equiv.uniform_equiv_mk_coe_symm UniformEquiv.uniform_equiv_mk_coe_symm

@[simp]
theorem refl_symm : (UniformEquiv.refl α).symm = UniformEquiv.refl α :=
  rfl
#align uniform_equiv.refl_symm UniformEquiv.refl_symm

protected theorem uniform_continuous (h : α ≃ᵤ β) : UniformContinuous h :=
  h.uniform_continuous_to_fun
#align uniform_equiv.uniform_continuous UniformEquiv.uniform_continuous

@[continuity]
protected theorem continuous (h : α ≃ᵤ β) : Continuous h :=
  h.UniformContinuous.Continuous
#align uniform_equiv.continuous UniformEquiv.continuous

protected theorem uniform_continuous_symm (h : α ≃ᵤ β) : UniformContinuous h.symm :=
  h.uniform_continuous_inv_fun
#align uniform_equiv.uniform_continuous_symm UniformEquiv.uniform_continuous_symm

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : α ≃ᵤ β) : Continuous h.symm :=
  h.uniform_continuous_symm.Continuous
#align uniform_equiv.continuous_symm UniformEquiv.continuous_symm

/-- A uniform isomorphism as a homeomorphism. -/
@[simps]
protected def toHomeomorph (e : α ≃ᵤ β) : α ≃ₜ β :=
  { e.toEquiv with continuous_to_fun := e.Continuous, continuous_inv_fun := e.continuous_symm }
#align uniform_equiv.to_homeomorph UniformEquiv.toHomeomorph

@[simp]
theorem apply_symm_apply (h : α ≃ᵤ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x
#align uniform_equiv.apply_symm_apply UniformEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (h : α ≃ᵤ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
#align uniform_equiv.symm_apply_apply UniformEquiv.symm_apply_apply

protected theorem bijective (h : α ≃ᵤ β) : Function.Bijective h :=
  h.toEquiv.Bijective
#align uniform_equiv.bijective UniformEquiv.bijective

protected theorem injective (h : α ≃ᵤ β) : Function.Injective h :=
  h.toEquiv.Injective
#align uniform_equiv.injective UniformEquiv.injective

protected theorem surjective (h : α ≃ᵤ β) : Function.Surjective h :=
  h.toEquiv.Surjective
#align uniform_equiv.surjective UniformEquiv.surjective

/-- Change the uniform equiv `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : α ≃ᵤ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ᵤ β :=
  have : g = f.symm :=
    funext fun x =>
      calc
        g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
        _ = f.symm x := by rw [hg x]
        
  { toFun := f, invFun := g, left_inv := by convert f.left_inv, right_inv := by convert f.right_inv,
    uniform_continuous_to_fun := f.UniformContinuous,
    uniform_continuous_inv_fun := by convert f.symm.uniform_continuous }
#align uniform_equiv.change_inv UniformEquiv.changeInv

@[simp]
theorem symm_comp_self (h : α ≃ᵤ β) : ⇑h.symm ∘ ⇑h = id :=
  funext h.symm_apply_apply
#align uniform_equiv.symm_comp_self UniformEquiv.symm_comp_self

@[simp]
theorem self_comp_symm (h : α ≃ᵤ β) : ⇑h ∘ ⇑h.symm = id :=
  funext h.apply_symm_apply
#align uniform_equiv.self_comp_symm UniformEquiv.self_comp_symm

@[simp]
theorem range_coe (h : α ≃ᵤ β) : Range h = univ :=
  h.Surjective.range_eq
#align uniform_equiv.range_coe UniformEquiv.range_coe

theorem image_symm (h : α ≃ᵤ β) : Image h.symm = Preimage h :=
  funext h.symm.toEquiv.image_eq_preimage
#align uniform_equiv.image_symm UniformEquiv.image_symm

theorem preimage_symm (h : α ≃ᵤ β) : Preimage h.symm = Image h :=
  (funext h.toEquiv.image_eq_preimage).symm
#align uniform_equiv.preimage_symm UniformEquiv.preimage_symm

@[simp]
theorem image_preimage (h : α ≃ᵤ β) (s : Set β) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s
#align uniform_equiv.image_preimage UniformEquiv.image_preimage

@[simp]
theorem preimage_image (h : α ≃ᵤ β) (s : Set α) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s
#align uniform_equiv.preimage_image UniformEquiv.preimage_image

protected theorem uniform_inducing (h : α ≃ᵤ β) : UniformInducing h :=
  uniform_inducing_of_compose h.UniformContinuous h.symm.UniformContinuous <| by
    simp only [symm_comp_self, uniform_inducing_id]
#align uniform_equiv.uniform_inducing UniformEquiv.uniform_inducing

theorem comap_eq (h : α ≃ᵤ β) : UniformSpace.comap h ‹_› = ‹_› := by
  ext : 1 <;> exact h.uniform_inducing.comap_uniformity
#align uniform_equiv.comap_eq UniformEquiv.comap_eq

protected theorem uniform_embedding (h : α ≃ᵤ β) : UniformEmbedding h :=
  ⟨h.UniformInducing, h.Injective⟩
#align uniform_equiv.uniform_embedding UniformEquiv.uniform_embedding

/-- Uniform equiv given a uniform embedding. -/
noncomputable def ofUniformEmbedding (f : α → β) (hf : UniformEmbedding f) : α ≃ᵤ Set.Range f where
  uniform_continuous_to_fun := hf.to_uniform_inducing.UniformContinuous.subtype_mk _
  uniform_continuous_inv_fun := by simp [hf.to_uniform_inducing.uniform_continuous_iff, uniform_continuous_subtype_coe]
  toEquiv := Equiv.ofInjective f hf.inj
#align uniform_equiv.of_uniform_embedding UniformEquiv.ofUniformEmbedding

/-- If two sets are equal, then they are uniformly equivalent. -/
def setCongr {s t : Set α} (h : s = t) : s ≃ᵤ t where
  uniform_continuous_to_fun := uniform_continuous_subtype_val.subtype_mk _
  uniform_continuous_inv_fun := uniform_continuous_subtype_val.subtype_mk _
  toEquiv := Equiv.setCongr h
#align uniform_equiv.set_congr UniformEquiv.setCongr

/-- Product of two uniform isomorphisms. -/
def prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : α × γ ≃ᵤ β × δ where
  uniform_continuous_to_fun :=
    (h₁.UniformContinuous.comp uniform_continuous_fst).prod_mk (h₂.UniformContinuous.comp uniform_continuous_snd)
  uniform_continuous_inv_fun :=
    (h₁.symm.UniformContinuous.comp uniform_continuous_fst).prod_mk
      (h₂.symm.UniformContinuous.comp uniform_continuous_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv
#align uniform_equiv.prod_congr UniformEquiv.prodCongr

@[simp]
theorem prod_congr_symm (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl
#align uniform_equiv.prod_congr_symm UniformEquiv.prod_congr_symm

@[simp]
theorem coe_prod_congr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl
#align uniform_equiv.coe_prod_congr UniformEquiv.coe_prod_congr

section

variable (α β γ)

/-- `α × β` is uniformly isomorphic to `β × α`. -/
def prodComm : α × β ≃ᵤ β × α where
  uniform_continuous_to_fun := uniform_continuous_snd.prod_mk uniform_continuous_fst
  uniform_continuous_inv_fun := uniform_continuous_snd.prod_mk uniform_continuous_fst
  toEquiv := Equiv.prodComm α β
#align uniform_equiv.prod_comm UniformEquiv.prodComm

@[simp]
theorem prod_comm_symm : (prodComm α β).symm = prodComm β α :=
  rfl
#align uniform_equiv.prod_comm_symm UniformEquiv.prod_comm_symm

@[simp]
theorem coe_prod_comm : ⇑(prodComm α β) = Prod.swap :=
  rfl
#align uniform_equiv.coe_prod_comm UniformEquiv.coe_prod_comm

/-- `(α × β) × γ` is uniformly isomorphic to `α × (β × γ)`. -/
def prodAssoc : (α × β) × γ ≃ᵤ α × β × γ where
  uniform_continuous_to_fun :=
    (uniform_continuous_fst.comp uniform_continuous_fst).prod_mk
      ((uniform_continuous_snd.comp uniform_continuous_fst).prod_mk uniform_continuous_snd)
  uniform_continuous_inv_fun :=
    (uniform_continuous_fst.prod_mk (uniform_continuous_fst.comp uniform_continuous_snd)).prod_mk
      (uniform_continuous_snd.comp uniform_continuous_snd)
  toEquiv := Equiv.prodAssoc α β γ
#align uniform_equiv.prod_assoc UniformEquiv.prodAssoc

/-- `α × {*}` is uniformly isomorphic to `α`. -/
@[simps (config := { fullyApplied := false }) apply]
def prodPunit : α × PUnit ≃ᵤ α where
  toEquiv := Equiv.prodPunit α
  uniform_continuous_to_fun := uniform_continuous_fst
  uniform_continuous_inv_fun := uniform_continuous_id.prod_mk uniform_continuous_const
#align uniform_equiv.prod_punit UniformEquiv.prodPunit

/-- `{*} × α` is uniformly isomorphic to `α`. -/
def punitProd : PUnit × α ≃ᵤ α :=
  (prodComm _ _).trans (prodPunit _)
#align uniform_equiv.punit_prod UniformEquiv.punitProd

@[simp]
theorem coe_punit_prod : ⇑(punitProd α) = Prod.snd :=
  rfl
#align uniform_equiv.coe_punit_prod UniformEquiv.coe_punit_prod

/-- Uniform equivalence between `ulift α` and `α`. -/
def ulift : ULift.{v, u} α ≃ᵤ α :=
  { Equiv.ulift with uniform_continuous_to_fun := uniform_continuous_comap,
    uniform_continuous_inv_fun := by
      have hf : UniformInducing (@Equiv.ulift.{v, u} α).toFun := ⟨rfl⟩
      simp_rw [hf.uniform_continuous_iff]
      exact uniform_continuous_id }
#align uniform_equiv.ulift UniformEquiv.ulift

end

/-- If `ι` has a unique element, then `ι → α` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (ι α : Type _) [Unique ι] [UniformSpace α] : (ι → α) ≃ᵤ α where
  toEquiv := Equiv.funUnique ι α
  uniform_continuous_to_fun := PiCat.uniform_continuous_proj _ _
  uniform_continuous_inv_fun := uniform_continuous_pi.mpr fun _ => uniform_continuous_id
#align uniform_equiv.fun_unique UniformEquiv.funUnique

/-- Uniform isomorphism between dependent functions `Π i : fin 2, α i` and `α 0 × α 1`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwo (α : Fin 2 → Type u) [∀ i, UniformSpace (α i)] : (∀ i, α i) ≃ᵤ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  uniform_continuous_to_fun := (PiCat.uniform_continuous_proj _ 0).prod_mk (PiCat.uniform_continuous_proj _ 1)
  uniform_continuous_inv_fun :=
    uniform_continuous_pi.mpr <| Fin.forall_fin_two.2 ⟨uniform_continuous_fst, uniform_continuous_snd⟩
#align uniform_equiv.pi_fin_two UniformEquiv.piFinTwo

/-- Uniform isomorphism between `α² = fin 2 → α` and `α × α`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrow : (Fin 2 → α) ≃ᵤ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }
#align uniform_equiv.fin_two_arrow UniformEquiv.finTwoArrow

/-- A subset of a uniform space is uniformly isomorphic to its image under a uniform isomorphism.
-/
def image (e : α ≃ᵤ β) (s : Set α) : s ≃ᵤ e '' s where
  uniform_continuous_to_fun := (e.UniformContinuous.comp uniform_continuous_subtype_val).subtype_mk _
  uniform_continuous_inv_fun := (e.symm.UniformContinuous.comp uniform_continuous_subtype_val).subtype_mk _
  toEquiv := e.toEquiv.Image s
#align uniform_equiv.image UniformEquiv.image

end UniformEquiv

/-- A uniform inducing equiv between uniform spaces is a uniform isomorphism. -/
@[simps]
def Equiv.toUniformEquivOfUniformInducing [UniformSpace α] [UniformSpace β] (f : α ≃ β) (hf : UniformInducing f) :
    α ≃ᵤ β :=
  { f with uniform_continuous_to_fun := hf.UniformContinuous,
    uniform_continuous_inv_fun := hf.uniform_continuous_iff.2 <| by simpa using uniform_continuous_id }
#align equiv.to_uniform_equiv_of_uniform_inducing Equiv.toUniformEquivOfUniformInducing

