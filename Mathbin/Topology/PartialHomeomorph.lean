/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Logic.Equiv.PartialEquiv
import Topology.Sets.Opens

#align_import topology.local_homeomorph from "leanprover-community/mathlib"@"431589bce478b2229eba14b14a283250428217db"

/-!
# Local homeomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`local_homeomorph α β` is an extension of `local_equiv α β`, i.e., it is a pair of functions
`e.to_fun` and `e.inv_fun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.to_fun x` and `e.inv_fun x`.

## Main definitions

`homeomorph.to_local_homeomorph`: associating a local homeomorphism to a homeomorphism, with
                                  source = target = univ
`local_homeomorph.symm`  : the inverse of a local homeomorphism
`local_homeomorph.trans` : the composition of two local homeomorphisms
`local_homeomorph.refl`  : the identity local homeomorphism
`local_homeomorph.of_set`: the identity on a set `s`
`eq_on_source`           : equivalence relation describing the "right" notion of equality for local
                           homeomorphisms

## Implementation notes

Most statements are copied from their local_equiv versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `local_equiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `local_equiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/


open Function Set Filter

open TopologicalSpace (SecondCountableTopology)

open scoped Topology

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

#print PartialHomeomorph /-
/-- local homeomorphisms, defined on open subsets of the space -/
@[nolint has_nonempty_instance]
structure PartialHomeomorph (α : Type _) (β : Type _) [TopologicalSpace α]
    [TopologicalSpace β] extends PartialEquiv α β where
  open_source : IsOpen source
  open_target : IsOpen target
  continuous_toFun : ContinuousOn to_fun source
  continuous_invFun : ContinuousOn inv_fun target
#align local_homeomorph PartialHomeomorph
-/

namespace PartialHomeomorph

variable (e : PartialHomeomorph α β) (e' : PartialHomeomorph β γ)

instance : CoeFun (PartialHomeomorph α β) fun _ => α → β :=
  ⟨fun e => e.toFun⟩

#print PartialHomeomorph.symm /-
/-- The inverse of a local homeomorphism -/
protected def symm : PartialHomeomorph β α :=
  { e.toPartialEquiv.symm with
    open_source := e.open_target
    open_target := e.open_source
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }
#align local_homeomorph.symm PartialHomeomorph.symm
-/

#print PartialHomeomorph.Simps.apply /-
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : PartialHomeomorph α β) : α → β :=
  e
#align local_homeomorph.simps.apply PartialHomeomorph.Simps.apply
-/

#print PartialHomeomorph.Simps.symm_apply /-
/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : PartialHomeomorph α β) : β → α :=
  e.symm
#align local_homeomorph.simps.symm_apply PartialHomeomorph.Simps.symm_apply
-/

initialize_simps_projections PartialHomeomorph (to_local_equiv_to_fun → apply,
  to_local_equiv_inv_fun → symm_apply, toPartialEquiv_source → source, toPartialEquiv_target →
  target, -toPartialEquiv)

#print PartialHomeomorph.continuousOn /-
protected theorem continuousOn : ContinuousOn e e.source :=
  e.continuous_toFun
#align local_homeomorph.continuous_on PartialHomeomorph.continuousOn
-/

#print PartialHomeomorph.continuousOn_symm /-
theorem continuousOn_symm : ContinuousOn e.symm e.target :=
  e.continuous_invFun
#align local_homeomorph.continuous_on_symm PartialHomeomorph.continuousOn_symm
-/

#print PartialHomeomorph.mk_coe /-
@[simp, mfld_simps]
theorem mk_coe (e : PartialEquiv α β) (a b c d) : (PartialHomeomorph.mk e a b c d : α → β) = e :=
  rfl
#align local_homeomorph.mk_coe PartialHomeomorph.mk_coe
-/

#print PartialHomeomorph.mk_coe_symm /-
@[simp, mfld_simps]
theorem mk_coe_symm (e : PartialEquiv α β) (a b c d) :
    ((PartialHomeomorph.mk e a b c d).symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.mk_coe_symm PartialHomeomorph.mk_coe_symm
-/

#print PartialHomeomorph.toPartialEquiv_injective /-
theorem toPartialEquiv_injective :
    Injective (toLocalEquiv : PartialHomeomorph α β → PartialEquiv α β)
  | ⟨e, h₁, h₂, h₃, h₄⟩, ⟨e', h₁', h₂', h₃', h₄'⟩, rfl => rfl
#align local_homeomorph.to_local_equiv_injective PartialHomeomorph.toPartialEquiv_injective
-/

#print PartialHomeomorph.toFun_eq_coe /-
/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem toFun_eq_coe (e : PartialHomeomorph α β) : e.toFun = e :=
  rfl
#align local_homeomorph.to_fun_eq_coe PartialHomeomorph.toFun_eq_coe
-/

#print PartialHomeomorph.invFun_eq_coe /-
@[simp, mfld_simps]
theorem invFun_eq_coe (e : PartialHomeomorph α β) : e.invFun = e.symm :=
  rfl
#align local_homeomorph.inv_fun_eq_coe PartialHomeomorph.invFun_eq_coe
-/

#print PartialHomeomorph.coe_coe /-
@[simp, mfld_simps]
theorem coe_coe : (e.toPartialEquiv : α → β) = e :=
  rfl
#align local_homeomorph.coe_coe PartialHomeomorph.coe_coe
-/

#print PartialHomeomorph.coe_coe_symm /-
@[simp, mfld_simps]
theorem coe_coe_symm : (e.toPartialEquiv.symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.coe_coe_symm PartialHomeomorph.coe_coe_symm
-/

#print PartialHomeomorph.map_source /-
@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h
#align local_homeomorph.map_source PartialHomeomorph.map_source
-/

#print PartialHomeomorph.map_target /-
@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h
#align local_homeomorph.map_target PartialHomeomorph.map_target
-/

#print PartialHomeomorph.left_inv /-
@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h
#align local_homeomorph.left_inv PartialHomeomorph.left_inv
-/

#print PartialHomeomorph.right_inv /-
@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
#align local_homeomorph.right_inv PartialHomeomorph.right_inv
-/

#print PartialHomeomorph.eq_symm_apply /-
theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toPartialEquiv.eq_symm_apply hx hy
#align local_homeomorph.eq_symm_apply PartialHomeomorph.eq_symm_apply
-/

#print PartialHomeomorph.mapsTo /-
protected theorem mapsTo : MapsTo e e.source e.target := fun x => e.map_source
#align local_homeomorph.maps_to PartialHomeomorph.mapsTo
-/

#print PartialHomeomorph.symm_mapsTo /-
protected theorem symm_mapsTo : MapsTo e.symm e.target e.source :=
  e.symm.MapsTo
#align local_homeomorph.symm_maps_to PartialHomeomorph.symm_mapsTo
-/

#print PartialHomeomorph.leftInvOn /-
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun x => e.left_inv
#align local_homeomorph.left_inv_on PartialHomeomorph.leftInvOn
-/

#print PartialHomeomorph.rightInvOn /-
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun x => e.right_inv
#align local_homeomorph.right_inv_on PartialHomeomorph.rightInvOn
-/

#print PartialHomeomorph.invOn /-
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.LeftInvOn, e.RightInvOn⟩
#align local_homeomorph.inv_on PartialHomeomorph.invOn
-/

#print PartialHomeomorph.injOn /-
protected theorem injOn : InjOn e e.source :=
  e.LeftInvOn.InjOn
#align local_homeomorph.inj_on PartialHomeomorph.injOn
-/

#print PartialHomeomorph.bijOn /-
protected theorem bijOn : BijOn e e.source e.target :=
  e.InvOn.BijOn e.MapsTo e.symm_mapsTo
#align local_homeomorph.bij_on PartialHomeomorph.bijOn
-/

#print PartialHomeomorph.surjOn /-
protected theorem surjOn : SurjOn e e.source e.target :=
  e.BijOn.SurjOn
#align local_homeomorph.surj_on PartialHomeomorph.surjOn
-/

#print Homeomorph.toPartialHomeomorph /-
/-- A homeomorphism induces a local homeomorphism on the whole space -/
@[simps (config := { mfld_cfg with simpRhs := true })]
def Homeomorph.toPartialHomeomorph (e : α ≃ₜ β) : PartialHomeomorph α β :=
  { e.toEquiv.toPartialEquiv with
    open_source := isOpen_univ
    open_target := isOpen_univ
    continuous_toFun := by erw [← continuous_iff_continuousOn_univ]; exact e.continuous_to_fun
    continuous_invFun := by erw [← continuous_iff_continuousOn_univ]; exact e.continuous_inv_fun }
#align homeomorph.to_local_homeomorph Homeomorph.toPartialHomeomorph
-/

#print PartialHomeomorph.replaceEquiv /-
/-- Replace `to_local_equiv` field to provide better definitional equalities. -/
def replaceEquiv (e : PartialHomeomorph α β) (e' : PartialEquiv α β) (h : e.toPartialEquiv = e') :
    PartialHomeomorph α β where
  toPartialEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuous_toFun := h ▸ e.continuous_toFun
  continuous_invFun := h ▸ e.continuous_invFun
#align local_homeomorph.replace_equiv PartialHomeomorph.replaceEquiv
-/

#print PartialHomeomorph.replaceEquiv_eq_self /-
theorem replaceEquiv_eq_self (e : PartialHomeomorph α β) (e' : PartialEquiv α β)
    (h : e.toPartialEquiv = e') : e.replaceEquiv e' h = e := by cases e; subst e'; rfl
#align local_homeomorph.replace_equiv_eq_self PartialHomeomorph.replaceEquiv_eq_self
-/

#print PartialHomeomorph.source_preimage_target /-
theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.MapsTo
#align local_homeomorph.source_preimage_target PartialHomeomorph.source_preimage_target
-/

#print PartialHomeomorph.eq_of_partialEquiv_eq /-
theorem eq_of_partialEquiv_eq {e e' : PartialHomeomorph α β}
    (h : e.toPartialEquiv = e'.toPartialEquiv) : e = e' := by cases e; cases e'; cases h; rfl
#align local_homeomorph.eq_of_local_equiv_eq PartialHomeomorph.eq_of_partialEquiv_eq
-/

#print PartialHomeomorph.eventually_left_inverse /-
theorem eventually_left_inverse (e : PartialHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'
#align local_homeomorph.eventually_left_inverse PartialHomeomorph.eventually_left_inverse
-/

#print PartialHomeomorph.eventually_left_inverse' /-
theorem eventually_left_inverse' (e : PartialHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)
#align local_homeomorph.eventually_left_inverse' PartialHomeomorph.eventually_left_inverse'
-/

#print PartialHomeomorph.eventually_right_inverse /-
theorem eventually_right_inverse (e : PartialHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'
#align local_homeomorph.eventually_right_inverse PartialHomeomorph.eventually_right_inverse
-/

#print PartialHomeomorph.eventually_right_inverse' /-
theorem eventually_right_inverse' (e : PartialHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)
#align local_homeomorph.eventually_right_inverse' PartialHomeomorph.eventually_right_inverse'
-/

#print PartialHomeomorph.eventually_ne_nhdsWithin /-
theorem eventually_ne_nhdsWithin (e : PartialHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhdsWithin_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']
#align local_homeomorph.eventually_ne_nhds_within PartialHomeomorph.eventually_ne_nhdsWithin
-/

#print PartialHomeomorph.nhdsWithin_source_inter /-
theorem nhdsWithin_source_inter {x} (hx : x ∈ e.source) (s : Set α) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)
#align local_homeomorph.nhds_within_source_inter PartialHomeomorph.nhdsWithin_source_inter
-/

#print PartialHomeomorph.nhdsWithin_target_inter /-
theorem nhdsWithin_target_inter {x} (hx : x ∈ e.target) (s : Set β) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhdsWithin_source_inter hx s
#align local_homeomorph.nhds_within_target_inter PartialHomeomorph.nhdsWithin_target_inter
-/

#print PartialHomeomorph.image_eq_target_inter_inv_preimage /-
theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h
#align local_homeomorph.image_eq_target_inter_inv_preimage PartialHomeomorph.image_eq_target_inter_inv_preimage
-/

#print PartialHomeomorph.image_source_inter_eq' /-
theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s
#align local_homeomorph.image_source_inter_eq' PartialHomeomorph.image_source_inter_eq'
-/

#print PartialHomeomorph.image_source_inter_eq /-
theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toPartialEquiv.image_source_inter_eq s
#align local_homeomorph.image_source_inter_eq PartialHomeomorph.image_source_inter_eq
-/

#print PartialHomeomorph.symm_image_eq_source_inter_preimage /-
theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
#align local_homeomorph.symm_image_eq_source_inter_preimage PartialHomeomorph.symm_image_eq_source_inter_preimage
-/

#print PartialHomeomorph.symm_image_target_inter_eq /-
theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
#align local_homeomorph.symm_image_target_inter_eq PartialHomeomorph.symm_image_target_inter_eq
-/

#print PartialHomeomorph.source_inter_preimage_inv_preimage /-
theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s
#align local_homeomorph.source_inter_preimage_inv_preimage PartialHomeomorph.source_inter_preimage_inv_preimage
-/

#print PartialHomeomorph.target_inter_inv_preimage_preimage /-
theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
#align local_homeomorph.target_inter_inv_preimage_preimage PartialHomeomorph.target_inter_inv_preimage_preimage
-/

#print PartialHomeomorph.source_inter_preimage_target_inter /-
theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s
#align local_homeomorph.source_inter_preimage_target_inter PartialHomeomorph.source_inter_preimage_target_inter
-/

#print PartialHomeomorph.image_source_eq_target /-
theorem image_source_eq_target (e : PartialHomeomorph α β) : e '' e.source = e.target :=
  e.toPartialEquiv.image_source_eq_target
#align local_homeomorph.image_source_eq_target PartialHomeomorph.image_source_eq_target
-/

#print PartialHomeomorph.symm_image_target_eq_source /-
theorem symm_image_target_eq_source (e : PartialHomeomorph α β) : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
#align local_homeomorph.symm_image_target_eq_source PartialHomeomorph.symm_image_target_eq_source
-/

#print PartialHomeomorph.ext /-
/-- Two local homeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected theorem ext (e' : PartialHomeomorph α β) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  eq_of_partialEquiv_eq (PartialEquiv.ext h hinv hs)
#align local_homeomorph.ext PartialHomeomorph.ext
-/

#print PartialHomeomorph.ext_iff /-
protected theorem ext_iff {e e' : PartialHomeomorph α β} :
    e = e' ↔ (∀ x, e x = e' x) ∧ (∀ x, e.symm x = e'.symm x) ∧ e.source = e'.source :=
  ⟨by rintro rfl; exact ⟨fun x => rfl, fun x => rfl, rfl⟩, fun h => e.ext e' h.1 h.2.1 h.2.2⟩
#align local_homeomorph.ext_iff PartialHomeomorph.ext_iff
-/

#print PartialHomeomorph.symm_toPartialEquiv /-
@[simp, mfld_simps]
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl
#align local_homeomorph.symm_to_local_equiv PartialHomeomorph.symm_toPartialEquiv
-/

#print PartialHomeomorph.symm_source /-
-- The following lemmas are already simp via local_equiv
theorem symm_source : e.symm.source = e.target :=
  rfl
#align local_homeomorph.symm_source PartialHomeomorph.symm_source
-/

#print PartialHomeomorph.symm_target /-
theorem symm_target : e.symm.target = e.source :=
  rfl
#align local_homeomorph.symm_target PartialHomeomorph.symm_target
-/

#print PartialHomeomorph.symm_symm /-
@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e :=
  eq_of_partialEquiv_eq <| by simp
#align local_homeomorph.symm_symm PartialHomeomorph.symm_symm
-/

#print PartialHomeomorph.continuousAt /-
/-- A local homeomorphism is continuous at any point of its source -/
protected theorem continuousAt {x : α} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.ContinuousOn x h).ContinuousAt (e.open_source.mem_nhds h)
#align local_homeomorph.continuous_at PartialHomeomorph.continuousAt
-/

#print PartialHomeomorph.continuousAt_symm /-
/-- A local homeomorphism inverse is continuous at any point of its target -/
theorem continuousAt_symm {x : β} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.ContinuousAt h
#align local_homeomorph.continuous_at_symm PartialHomeomorph.continuousAt_symm
-/

#print PartialHomeomorph.tendsto_symm /-
theorem tendsto_symm {x} (hx : x ∈ e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuous_at_symm (e.map_source hx)
#align local_homeomorph.tendsto_symm PartialHomeomorph.tendsto_symm
-/

#print PartialHomeomorph.map_nhds_eq /-
theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymm (e.ContinuousAt hx) <|
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)
#align local_homeomorph.map_nhds_eq PartialHomeomorph.map_nhds_eq
-/

#print PartialHomeomorph.symm_map_nhds_eq /-
theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by rw [e.left_inv hx]
#align local_homeomorph.symm_map_nhds_eq PartialHomeomorph.symm_map_nhds_eq
-/

#print PartialHomeomorph.image_mem_nhds /-
theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set α} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs
#align local_homeomorph.image_mem_nhds PartialHomeomorph.image_mem_nhds
-/

#print PartialHomeomorph.map_nhdsWithin_eq /-
theorem map_nhdsWithin_eq (e : PartialHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set α) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :=
      congr_arg (map e) (e.nhdsWithin_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.LeftInvOn.mono <| inter_subset_left _ _).map_nhdsWithin_eq (e.left_inv hx)
        (e.continuousAt_symm (e.map_source hx)).ContinuousWithinAt
        (e.ContinuousAt hx).ContinuousWithinAt
#align local_homeomorph.map_nhds_within_eq PartialHomeomorph.map_nhdsWithin_eq
-/

#print PartialHomeomorph.map_nhdsWithin_preimage_eq /-
theorem map_nhdsWithin_preimage_eq (e : PartialHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set β) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhds_within_target_inter (e.map_source hx)]
#align local_homeomorph.map_nhds_within_preimage_eq PartialHomeomorph.map_nhdsWithin_preimage_eq
-/

#print PartialHomeomorph.eventually_nhds /-
theorem eventually_nhds (e : PartialHomeomorph α β) {x : α} (p : β → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map
#align local_homeomorph.eventually_nhds PartialHomeomorph.eventually_nhds
-/

#print PartialHomeomorph.eventually_nhds' /-
theorem eventually_nhds' (e : PartialHomeomorph α β) {x : α} (p : α → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x :=
  by
  rw [e.eventually_nhds _ hx]
  refine' eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => _)
  rw [hy]
#align local_homeomorph.eventually_nhds' PartialHomeomorph.eventually_nhds'
-/

#print PartialHomeomorph.eventually_nhdsWithin /-
theorem eventually_nhdsWithin (e : PartialHomeomorph α β) {x : α} (p : β → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) :=
  by
  refine' Iff.trans _ eventually_map
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.nhds_within_target_inter (e.maps_to hx)]
#align local_homeomorph.eventually_nhds_within PartialHomeomorph.eventually_nhdsWithin
-/

#print PartialHomeomorph.eventually_nhdsWithin' /-
theorem eventually_nhdsWithin' (e : PartialHomeomorph α β) {x : α} (p : α → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x :=
  by
  rw [e.eventually_nhds_within _ hx]
  refine'
    eventually_congr
      ((eventually_nhdsWithin_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy =>
        _)
  rw [hy]
#align local_homeomorph.eventually_nhds_within' PartialHomeomorph.eventually_nhdsWithin'
-/

#print PartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter /-
/-- This lemma is useful in the manifold library in the case that `e` is a chart. It states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a chart on `γ`).  -/
theorem preimage_eventuallyEq_target_inter_preimage_inter {e : PartialHomeomorph α β} {s : Set α}
    {t : Set γ} {x : α} {f : α → γ} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.source)
    (ht : t ∈ 𝓝 (f x)) : e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set β) :=
  by
  rw [eventually_eq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhds_within_iff_eventually.mp (hf.preimage_mem_nhds_within ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.maps_to hy, true_and_iff, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]
#align local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter PartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter
-/

#print PartialHomeomorph.isOpen_inter_preimage /-
theorem isOpen_inter_preimage {s : Set β} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.ContinuousOn.isOpen_inter_preimage e.open_source hs
#align local_homeomorph.preimage_open_of_open PartialHomeomorph.isOpen_inter_preimage
-/

/-!
### `local_homeomorph.is_image` relation

We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `local_equiv.is_image` for local homeomorphisms. In this section
we transfer API about `local_equiv.is_image` to local homeomorphisms and add a few
`local_homeomorph`-specific lemmas like `local_homeomorph.is_image.closure`.
-/


#print PartialHomeomorph.IsImage /-
/-- We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_homeomorph.is_image PartialHomeomorph.IsImage
-/

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

#print PartialHomeomorph.IsImage.toPartialEquiv /-
theorem toPartialEquiv (h : e.IsImage s t) : e.toPartialEquiv.IsImage s t :=
  h
#align local_homeomorph.is_image.to_local_equiv PartialHomeomorph.IsImage.toPartialEquiv
-/

#print PartialHomeomorph.IsImage.apply_mem_iff /-
theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
#align local_homeomorph.is_image.apply_mem_iff PartialHomeomorph.IsImage.apply_mem_iff
-/

#print PartialHomeomorph.IsImage.symm /-
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toPartialEquiv.symm
#align local_homeomorph.is_image.symm PartialHomeomorph.IsImage.symm
-/

#print PartialHomeomorph.IsImage.symm_apply_mem_iff /-
theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy
#align local_homeomorph.is_image.symm_apply_mem_iff PartialHomeomorph.IsImage.symm_apply_mem_iff
-/

#print PartialHomeomorph.IsImage.symm_iff /-
@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align local_homeomorph.is_image.symm_iff PartialHomeomorph.IsImage.symm_iff
-/

#print PartialHomeomorph.IsImage.mapsTo /-
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toPartialEquiv.MapsTo
#align local_homeomorph.is_image.maps_to PartialHomeomorph.IsImage.mapsTo
-/

#print PartialHomeomorph.IsImage.symm_mapsTo /-
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.MapsTo
#align local_homeomorph.is_image.symm_maps_to PartialHomeomorph.IsImage.symm_mapsTo
-/

#print PartialHomeomorph.IsImage.image_eq /-
theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toPartialEquiv.image_eq
#align local_homeomorph.is_image.image_eq PartialHomeomorph.IsImage.image_eq
-/

#print PartialHomeomorph.IsImage.symm_image_eq /-
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
#align local_homeomorph.is_image.symm_image_eq PartialHomeomorph.IsImage.symm_image_eq
-/

#print PartialHomeomorph.IsImage.iff_preimage_eq /-
theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  PartialEquiv.IsImage.iff_preimage_eq
#align local_homeomorph.is_image.iff_preimage_eq PartialHomeomorph.IsImage.iff_preimage_eq
-/

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq
#align local_homeomorph.is_image.preimage_eq PartialHomeomorph.IsImage.preimage_eq
#align local_homeomorph.is_image.of_preimage_eq PartialHomeomorph.IsImage.of_preimage_eq

#print PartialHomeomorph.IsImage.iff_symm_preimage_eq /-
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq
#align local_homeomorph.is_image.iff_symm_preimage_eq PartialHomeomorph.IsImage.iff_symm_preimage_eq
-/

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq
#align local_homeomorph.is_image.symm_preimage_eq PartialHomeomorph.IsImage.symm_preimage_eq
#align local_homeomorph.is_image.of_symm_preimage_eq PartialHomeomorph.IsImage.of_symm_preimage_eq

#print PartialHomeomorph.IsImage.iff_symm_preimage_eq' /-
theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']
#align local_homeomorph.is_image.iff_symm_preimage_eq' PartialHomeomorph.IsImage.iff_symm_preimage_eq'
-/

alias ⟨symm_preimage_eq', of_symm_preimage_eq'⟩ := iff_symm_preimage_eq'
#align local_homeomorph.is_image.symm_preimage_eq' PartialHomeomorph.IsImage.symm_preimage_eq'
#align local_homeomorph.is_image.of_symm_preimage_eq' PartialHomeomorph.IsImage.of_symm_preimage_eq'

#print PartialHomeomorph.IsImage.iff_preimage_eq' /-
theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'
#align local_homeomorph.is_image.iff_preimage_eq' PartialHomeomorph.IsImage.iff_preimage_eq'
-/

alias ⟨preimage_eq', of_preimage_eq'⟩ := iff_preimage_eq'
#align local_homeomorph.is_image.preimage_eq' PartialHomeomorph.IsImage.preimage_eq'
#align local_homeomorph.is_image.of_preimage_eq' PartialHomeomorph.IsImage.of_preimage_eq'

#print PartialHomeomorph.IsImage.of_image_eq /-
theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  PartialEquiv.IsImage.of_image_eq h
#align local_homeomorph.is_image.of_image_eq PartialHomeomorph.IsImage.of_image_eq
-/

#print PartialHomeomorph.IsImage.of_symm_image_eq /-
theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  PartialEquiv.IsImage.of_symm_image_eq h
#align local_homeomorph.is_image.of_symm_image_eq PartialHomeomorph.IsImage.of_symm_image_eq
-/

#print PartialHomeomorph.IsImage.compl /-
protected theorem compl (h : e.IsImage s t) : e.IsImage (sᶜ) (tᶜ) := fun x hx => not_congr (h hx)
#align local_homeomorph.is_image.compl PartialHomeomorph.IsImage.compl
-/

#print PartialHomeomorph.IsImage.inter /-
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun x hx => and_congr (h hx) (h' hx)
#align local_homeomorph.is_image.inter PartialHomeomorph.IsImage.inter
-/

#print PartialHomeomorph.IsImage.union /-
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun x hx => or_congr (h hx) (h' hx)
#align local_homeomorph.is_image.union PartialHomeomorph.IsImage.union
-/

#print PartialHomeomorph.IsImage.diff /-
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
#align local_homeomorph.is_image.diff PartialHomeomorph.IsImage.diff
-/

#print PartialHomeomorph.IsImage.leftInvOn_piecewise /-
theorem leftInvOn_piecewise {e' : PartialHomeomorph α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toPartialEquiv.leftInvOn_piecewise h'
#align local_homeomorph.is_image.left_inv_on_piecewise PartialHomeomorph.IsImage.leftInvOn_piecewise
-/

#print PartialHomeomorph.IsImage.inter_eq_of_inter_eq_of_eqOn /-
theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialHomeomorph α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toPartialEquiv.inter_eq_of_inter_eq_of_eqOn h' hs Heq
#align local_homeomorph.is_image.inter_eq_of_inter_eq_of_eq_on PartialHomeomorph.IsImage.inter_eq_of_inter_eq_of_eqOn
-/

#print PartialHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOn /-
theorem symm_eqOn_of_inter_eq_of_eqOn {e' : PartialHomeomorph α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toPartialEquiv.symm_eq_on_of_inter_eq_of_eqOn hs Heq
#align local_homeomorph.is_image.symm_eq_on_of_inter_eq_of_eq_on PartialHomeomorph.IsImage.symm_eqOn_of_inter_eq_of_eqOn
-/

#print PartialHomeomorph.IsImage.map_nhdsWithin_eq /-
theorem map_nhdsWithin_eq (h : e.IsImage s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhds_within_eq hx, h.image_eq, e.nhds_within_target_inter (e.map_source hx)]
#align local_homeomorph.is_image.map_nhds_within_eq PartialHomeomorph.IsImage.map_nhdsWithin_eq
-/

#print PartialHomeomorph.IsImage.closure /-
protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhdsWithin_neBot, ← h.map_nhds_within_eq hx, map_ne_bot_iff]
#align local_homeomorph.is_image.closure PartialHomeomorph.IsImage.closure
-/

#print PartialHomeomorph.IsImage.interior /-
protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl
#align local_homeomorph.is_image.interior PartialHomeomorph.IsImage.interior
-/

#print PartialHomeomorph.IsImage.frontier /-
protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diffₓ h.interior
#align local_homeomorph.is_image.frontier PartialHomeomorph.IsImage.frontier
-/

#print PartialHomeomorph.IsImage.isOpen_iff /-
theorem isOpen_iff (h : e.IsImage s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.isOpen_inter_preimage hs, fun hs =>
    h.preimage_eq' ▸ e.isOpen_inter_preimage hs⟩
#align local_homeomorph.is_image.is_open_iff PartialHomeomorph.IsImage.isOpen_iff
-/

#print PartialHomeomorph.IsImage.restr /-
/-- Restrict a `local_homeomorph` to a pair of corresponding open sets. -/
@[simps toPartialEquiv]
def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : PartialHomeomorph α β
    where
  toPartialEquiv := h.toPartialEquiv.restr
  open_source := hs
  open_target := h.isOpen_iff.1 hs
  continuous_toFun := e.ContinuousOn.mono (inter_subset_left _ _)
  continuous_invFun := e.symm.ContinuousOn.mono (inter_subset_left _ _)
#align local_homeomorph.is_image.restr PartialHomeomorph.IsImage.restr
-/

end IsImage

#print PartialHomeomorph.isImage_source_target /-
theorem isImage_source_target : e.IsImage e.source e.target :=
  e.toPartialEquiv.isImage_source_target
#align local_homeomorph.is_image_source_target PartialHomeomorph.isImage_source_target
-/

#print PartialHomeomorph.isImage_source_target_of_disjoint /-
theorem isImage_source_target_of_disjoint (e' : PartialHomeomorph α β)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toPartialEquiv.isImage_source_target_of_disjoint e'.toPartialEquiv hs ht
#align local_homeomorph.is_image_source_target_of_disjoint PartialHomeomorph.isImage_source_target_of_disjoint
-/

#print PartialHomeomorph.preimage_interior /-
/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
theorem preimage_interior (s : Set β) :
    e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq
#align local_homeomorph.preimage_interior PartialHomeomorph.preimage_interior
-/

#print PartialHomeomorph.preimage_closure /-
theorem preimage_closure (s : Set β) : e.source ∩ e ⁻¹' closure s = e.source ∩ closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq
#align local_homeomorph.preimage_closure PartialHomeomorph.preimage_closure
-/

#print PartialHomeomorph.preimage_frontier /-
theorem preimage_frontier (s : Set β) :
    e.source ∩ e ⁻¹' frontier s = e.source ∩ frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq
#align local_homeomorph.preimage_frontier PartialHomeomorph.preimage_frontier
-/

#print PartialHomeomorph.isOpen_inter_preimage_symm /-
theorem isOpen_inter_preimage_symm {s : Set α} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.ContinuousOn.isOpen_inter_preimage e.open_target hs
#align local_homeomorph.preimage_open_of_open_symm PartialHomeomorph.isOpen_inter_preimage_symm
-/

#print PartialHomeomorph.isOpen_image_of_subset_source /-
/-- The image of an open set in the source is open. -/
theorem isOpen_image_of_subset_source {s : Set α} (hs : IsOpen s) (h : s ⊆ e.source) :
    IsOpen (e '' s) :=
  by
  have : e '' s = e.target ∩ e.symm ⁻¹' s := e.to_local_equiv.image_eq_target_inter_inv_preimage h
  rw [this]
  exact e.continuous_on_symm.preimage_open_of_open e.open_target hs
#align local_homeomorph.image_open_of_open PartialHomeomorph.isOpen_image_of_subset_source
-/

#print PartialHomeomorph.isOpen_image_source_inter /-
/-- The image of the restriction of an open set to the source is open. -/
theorem isOpen_image_source_inter {s : Set α} (hs : IsOpen s) : IsOpen (e '' (e.source ∩ s)) :=
  isOpen_image_of_subset_source _ (IsOpen.inter e.open_source hs) (inter_subset_left _ _)
#align local_homeomorph.image_open_of_open' PartialHomeomorph.isOpen_image_source_inter
-/

#print PartialHomeomorph.ofContinuousOpenRestrict /-
/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def ofContinuousOpenRestrict (e : PartialEquiv α β) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : PartialHomeomorph α β
    where
  toPartialEquiv := e
  open_source := hs
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.is_open_range
  continuous_toFun := hc
  continuous_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.LeftInvOn
#align local_homeomorph.of_continuous_open_restrict PartialHomeomorph.ofContinuousOpenRestrict
-/

#print PartialHomeomorph.ofContinuousOpen /-
/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def ofContinuousOpen (e : PartialEquiv α β) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph α β :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs
#align local_homeomorph.of_continuous_open PartialHomeomorph.ofContinuousOpen
-/

#print PartialHomeomorph.restrOpen /-
/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restrOpen (s : Set α) (hs : IsOpen s) : PartialHomeomorph α β :=
  (@IsImage.of_symm_preimage_eq α β _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)
#align local_homeomorph.restr_open PartialHomeomorph.restrOpen
-/

#print PartialHomeomorph.restrOpen_toPartialEquiv /-
@[simp, mfld_simps]
theorem restrOpen_toPartialEquiv (s : Set α) (hs : IsOpen s) :
    (e.restrOpen s hs).toPartialEquiv = e.toPartialEquiv.restr s :=
  rfl
#align local_homeomorph.restr_open_to_local_equiv PartialHomeomorph.restrOpen_toPartialEquiv
-/

#print PartialHomeomorph.restrOpen_source /-
-- Already simp via local_equiv
theorem restrOpen_source (s : Set α) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source ∩ s :=
  rfl
#align local_homeomorph.restr_open_source PartialHomeomorph.restrOpen_source
-/

#print PartialHomeomorph.restr /-
/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
@[simps (config := mfld_cfg) apply symm_apply, simps (config := { attrs := [] }) source target]
protected def restr (s : Set α) : PartialHomeomorph α β :=
  e.restrOpen (interior s) isOpen_interior
#align local_homeomorph.restr PartialHomeomorph.restr
-/

#print PartialHomeomorph.restr_toPartialEquiv /-
@[simp, mfld_simps]
theorem restr_toPartialEquiv (s : Set α) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr (interior s) :=
  rfl
#align local_homeomorph.restr_to_local_equiv PartialHomeomorph.restr_toPartialEquiv
-/

#print PartialHomeomorph.restr_source' /-
theorem restr_source' (s : Set α) (hs : IsOpen s) : (e.restr s).source = e.source ∩ s := by
  rw [e.restr_source, hs.interior_eq]
#align local_homeomorph.restr_source' PartialHomeomorph.restr_source'
-/

#print PartialHomeomorph.restr_toPartialEquiv' /-
theorem restr_toPartialEquiv' (s : Set α) (hs : IsOpen s) :
    (e.restr s).toPartialEquiv = e.toPartialEquiv.restr s := by
  rw [e.restr_to_local_equiv, hs.interior_eq]
#align local_homeomorph.restr_to_local_equiv' PartialHomeomorph.restr_toPartialEquiv'
-/

#print PartialHomeomorph.restr_eq_of_source_subset /-
theorem restr_eq_of_source_subset {e : PartialHomeomorph α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e := by
  apply eq_of_local_equiv_eq
  rw [restr_to_local_equiv]
  apply PartialEquiv.restr_eq_of_source_subset
  exact interior_maximal h e.open_source
#align local_homeomorph.restr_eq_of_source_subset PartialHomeomorph.restr_eq_of_source_subset
-/

#print PartialHomeomorph.restr_univ /-
@[simp, mfld_simps]
theorem restr_univ {e : PartialHomeomorph α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)
#align local_homeomorph.restr_univ PartialHomeomorph.restr_univ
-/

#print PartialHomeomorph.restr_source_inter /-
theorem restr_source_inter (s : Set α) : e.restr (e.source ∩ s) = e.restr s :=
  by
  refine' PartialHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) _
  simp [e.open_source.interior_eq, ← inter_assoc]
#align local_homeomorph.restr_source_inter PartialHomeomorph.restr_source_inter
-/

#print PartialHomeomorph.refl /-
/-- The identity on the whole space as a local homeomorphism. -/
@[simps (config := mfld_cfg) apply, simps (config := { attrs := [] }) source target]
protected def refl (α : Type _) [TopologicalSpace α] : PartialHomeomorph α α :=
  (Homeomorph.refl α).toPartialHomeomorph
#align local_homeomorph.refl PartialHomeomorph.refl
-/

#print PartialHomeomorph.refl_partialEquiv /-
@[simp, mfld_simps]
theorem refl_partialEquiv : (PartialHomeomorph.refl α).toPartialEquiv = PartialEquiv.refl α :=
  rfl
#align local_homeomorph.refl_local_equiv PartialHomeomorph.refl_partialEquiv
-/

#print PartialHomeomorph.refl_symm /-
@[simp, mfld_simps]
theorem refl_symm : (PartialHomeomorph.refl α).symm = PartialHomeomorph.refl α :=
  rfl
#align local_homeomorph.refl_symm PartialHomeomorph.refl_symm
-/

section

variable {s : Set α} (hs : IsOpen s)

#print PartialHomeomorph.ofSet /-
/-- The identity local equiv on a set `s` -/
@[simps (config := mfld_cfg) apply, simps (config := { attrs := [] }) source target]
def ofSet (s : Set α) (hs : IsOpen s) : PartialHomeomorph α α :=
  { PartialEquiv.ofSet s with
    open_source := hs
    open_target := hs
    continuous_toFun := continuous_id.ContinuousOn
    continuous_invFun := continuous_id.ContinuousOn }
#align local_homeomorph.of_set PartialHomeomorph.ofSet
-/

#print PartialHomeomorph.ofSet_toPartialEquiv /-
@[simp, mfld_simps]
theorem ofSet_toPartialEquiv : (ofSet s hs).toPartialEquiv = PartialEquiv.ofSet s :=
  rfl
#align local_homeomorph.of_set_to_local_equiv PartialHomeomorph.ofSet_toPartialEquiv
-/

#print PartialHomeomorph.ofSet_symm /-
@[simp, mfld_simps]
theorem ofSet_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl
#align local_homeomorph.of_set_symm PartialHomeomorph.ofSet_symm
-/

#print PartialHomeomorph.ofSet_univ_eq_refl /-
@[simp, mfld_simps]
theorem ofSet_univ_eq_refl : ofSet univ isOpen_univ = PartialHomeomorph.refl α := by ext <;> simp
#align local_homeomorph.of_set_univ_eq_refl PartialHomeomorph.ofSet_univ_eq_refl
-/

end

#print PartialHomeomorph.trans' /-
/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.target = e'.source) : PartialHomeomorph α γ :=
  {
    PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv
      h with
    open_source := e.open_source
    open_target := e'.open_target
    continuous_toFun := by
      apply e'.continuous_to_fun.comp e.continuous_to_fun
      rw [← h]
      exact e.to_local_equiv.source_subset_preimage_target
    continuous_invFun := by
      apply e.continuous_inv_fun.comp e'.continuous_inv_fun
      rw [h]
      exact e'.to_local_equiv.target_subset_preimage_source }
#align local_homeomorph.trans' PartialHomeomorph.trans'
-/

#print PartialHomeomorph.trans /-
/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : PartialHomeomorph α γ :=
  PartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])
#align local_homeomorph.trans PartialHomeomorph.trans
-/

#print PartialHomeomorph.trans_toPartialEquiv /-
@[simp, mfld_simps]
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  rfl
#align local_homeomorph.trans_to_local_equiv PartialHomeomorph.trans_toPartialEquiv
-/

#print PartialHomeomorph.coe_trans /-
@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl
#align local_homeomorph.coe_trans PartialHomeomorph.coe_trans
-/

#print PartialHomeomorph.coe_trans_symm /-
@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl
#align local_homeomorph.coe_trans_symm PartialHomeomorph.coe_trans_symm
-/

#print PartialHomeomorph.trans_apply /-
theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl
#align local_homeomorph.trans_apply PartialHomeomorph.trans_apply
-/

#print PartialHomeomorph.trans_symm_eq_symm_trans_symm /-
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := by
  cases e <;> cases e' <;> rfl
#align local_homeomorph.trans_symm_eq_symm_trans_symm PartialHomeomorph.trans_symm_eq_symm_trans_symm
-/

#print PartialHomeomorph.trans_source /-
/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv
#align local_homeomorph.trans_source PartialHomeomorph.trans_source
-/

#print PartialHomeomorph.trans_source' /-
theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv
#align local_homeomorph.trans_source' PartialHomeomorph.trans_source'
-/

#print PartialHomeomorph.trans_source'' /-
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv
#align local_homeomorph.trans_source'' PartialHomeomorph.trans_source''
-/

#print PartialHomeomorph.image_trans_source /-
theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv
#align local_homeomorph.image_trans_source PartialHomeomorph.image_trans_source
-/

#print PartialHomeomorph.trans_target /-
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
#align local_homeomorph.trans_target PartialHomeomorph.trans_target
-/

#print PartialHomeomorph.trans_target' /-
theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
#align local_homeomorph.trans_target' PartialHomeomorph.trans_target'
-/

#print PartialHomeomorph.trans_target'' /-
theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
#align local_homeomorph.trans_target'' PartialHomeomorph.trans_target''
-/

#print PartialHomeomorph.inv_image_trans_target /-
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
#align local_homeomorph.inv_image_trans_target PartialHomeomorph.inv_image_trans_target
-/

#print PartialHomeomorph.trans_assoc /-
theorem trans_assoc (e'' : PartialHomeomorph γ δ) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  eq_of_partialEquiv_eq <|
    PartialEquiv.trans_assoc e.toPartialEquiv e'.toPartialEquiv e''.toPartialEquiv
#align local_homeomorph.trans_assoc PartialHomeomorph.trans_assoc
-/

#print PartialHomeomorph.trans_refl /-
@[simp, mfld_simps]
theorem trans_refl : e.trans (PartialHomeomorph.refl β) = e :=
  eq_of_partialEquiv_eq <| PartialEquiv.trans_refl e.toPartialEquiv
#align local_homeomorph.trans_refl PartialHomeomorph.trans_refl
-/

#print PartialHomeomorph.refl_trans /-
@[simp, mfld_simps]
theorem refl_trans : (PartialHomeomorph.refl α).trans e = e :=
  eq_of_partialEquiv_eq <| PartialEquiv.refl_trans e.toPartialEquiv
#align local_homeomorph.refl_trans PartialHomeomorph.refl_trans
-/

#print PartialHomeomorph.trans_ofSet /-
theorem trans_ofSet {s : Set β} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  (PartialHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [PartialEquiv.trans_source, (e.preimage_interior _).symm, hs.interior_eq]
#align local_homeomorph.trans_of_set PartialHomeomorph.trans_ofSet
-/

#print PartialHomeomorph.trans_of_set' /-
theorem trans_of_set' {s : Set β} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_of_set, restr_source_inter]
#align local_homeomorph.trans_of_set' PartialHomeomorph.trans_of_set'
-/

#print PartialHomeomorph.ofSet_trans /-
theorem ofSet_trans {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  (PartialHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [PartialEquiv.trans_source, hs.interior_eq, inter_comm]
#align local_homeomorph.of_set_trans PartialHomeomorph.ofSet_trans
-/

#print PartialHomeomorph.ofSet_trans' /-
theorem ofSet_trans' {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr (e.source ∩ s) :=
  by rw [of_set_trans, restr_source_inter]
#align local_homeomorph.of_set_trans' PartialHomeomorph.ofSet_trans'
-/

#print PartialHomeomorph.ofSet_trans_ofSet /-
@[simp, mfld_simps]
theorem ofSet_trans_ofSet {s : Set α} (hs : IsOpen s) {s' : Set α} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') :=
  by
  rw [(of_set s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]
#align local_homeomorph.of_set_trans_of_set PartialHomeomorph.ofSet_trans_ofSet
-/

#print PartialHomeomorph.restr_trans /-
theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  eq_of_partialEquiv_eq <| PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)
#align local_homeomorph.restr_trans PartialHomeomorph.restr_trans
-/

#print PartialHomeomorph.transHomeomorph /-
/-- Postcompose a local homeomorphism with an homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps (config := { fullyApplied := false })]
def transHomeomorph (e' : β ≃ₜ γ) : PartialHomeomorph α γ
    where
  toPartialEquiv := e.toPartialEquiv.transEquiv e'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.Preimage e'.symm.Continuous
  continuous_toFun := e'.Continuous.comp_continuousOn e.ContinuousOn
  continuous_invFun := e.symm.ContinuousOn.comp e'.symm.Continuous.ContinuousOn fun x h => h
#align local_homeomorph.trans_homeomorph PartialHomeomorph.transHomeomorph
-/

#print PartialHomeomorph.transHomeomorph_eq_trans /-
theorem transHomeomorph_eq_trans (e' : β ≃ₜ γ) :
    e.transHomeomorph e' = e.trans e'.toPartialHomeomorph :=
  toPartialEquiv_injective <| PartialEquiv.transEquiv_eq_trans _ _
#align local_homeomorph.trans_equiv_eq_trans PartialHomeomorph.transHomeomorph_eq_trans
-/

#print Homeomorph.transPartialHomeomorph /-
/-- Precompose a local homeomorphism with an homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps (config := { fullyApplied := false })]
def Homeomorph.transPartialHomeomorph (e : α ≃ₜ β) : PartialHomeomorph α γ
    where
  toPartialEquiv := e.toEquiv.transPartialEquiv e'.toPartialEquiv
  open_source := e'.open_source.Preimage e.Continuous
  open_target := e'.open_target
  continuous_toFun := e'.ContinuousOn.comp e.Continuous.ContinuousOn fun x h => h
  continuous_invFun := e.symm.Continuous.comp_continuousOn e'.symm.ContinuousOn
#align homeomorph.trans_local_homeomorph Homeomorph.transPartialHomeomorph
-/

#print Homeomorph.transPartialHomeomorph_eq_trans /-
theorem Homeomorph.transPartialHomeomorph_eq_trans (e : α ≃ₜ β) :
    e.transPartialHomeomorph e' = e.toPartialHomeomorph.trans e' :=
  toPartialEquiv_injective <| Equiv.transPartialEquiv_eq_trans _ _
#align homeomorph.trans_local_homeomorph_eq_trans Homeomorph.transPartialHomeomorph_eq_trans
-/

#print PartialHomeomorph.EqOnSource /-
/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def EqOnSource (e e' : PartialHomeomorph α β) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source
#align local_homeomorph.eq_on_source PartialHomeomorph.EqOnSource
-/

#print PartialHomeomorph.eqOnSource_iff /-
theorem eqOnSource_iff (e e' : PartialHomeomorph α β) :
    EqOnSource e e' ↔ PartialEquiv.EqOnSource e.toPartialEquiv e'.toPartialEquiv :=
  Iff.rfl
#align local_homeomorph.eq_on_source_iff PartialHomeomorph.eqOnSource_iff
-/

/-- `eq_on_source` is an equivalence relation -/
instance : Setoid (PartialHomeomorph α β)
    where
  R := EqOnSource
  iseqv :=
    ⟨fun e => (@PartialEquiv.eqOnSourceSetoid α β).iseqv.1 e.toPartialEquiv, fun e e' h =>
      (@PartialEquiv.eqOnSourceSetoid α β).iseqv.2.1 ((eqOnSource_iff e e').1 h),
      fun e e' e'' h h' =>
      (@PartialEquiv.eqOnSourceSetoid α β).iseqv.2.2 ((eqOnSource_iff e e').1 h)
        ((eqOnSource_iff e' e'').1 h')⟩

#print PartialHomeomorph.eqOnSource_refl /-
theorem eqOnSource_refl : e ≈ e :=
  Setoid.refl _
#align local_homeomorph.eq_on_source_refl PartialHomeomorph.eqOnSource_refl
-/

#print PartialHomeomorph.EqOnSource.symm' /-
/-- If two local homeomorphisms are equivalent, so are their inverses -/
theorem EqOnSource.symm' {e e' : PartialHomeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
  PartialEquiv.EqOnSource.symm' h
#align local_homeomorph.eq_on_source.symm' PartialHomeomorph.EqOnSource.symm'
-/

#print PartialHomeomorph.EqOnSource.source_eq /-
/-- Two equivalent local homeomorphisms have the same source -/
theorem EqOnSource.source_eq {e e' : PartialHomeomorph α β} (h : e ≈ e') : e.source = e'.source :=
  h.1
#align local_homeomorph.eq_on_source.source_eq PartialHomeomorph.EqOnSource.source_eq
-/

#print PartialHomeomorph.EqOnSource.target_eq /-
/-- Two equivalent local homeomorphisms have the same target -/
theorem EqOnSource.target_eq {e e' : PartialHomeomorph α β} (h : e ≈ e') : e.target = e'.target :=
  h.symm'.1
#align local_homeomorph.eq_on_source.target_eq PartialHomeomorph.EqOnSource.target_eq
-/

#print PartialHomeomorph.EqOnSource.eqOn /-
/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
theorem EqOnSource.eqOn {e e' : PartialHomeomorph α β} (h : e ≈ e') : EqOn e e' e.source :=
  h.2
#align local_homeomorph.eq_on_source.eq_on PartialHomeomorph.EqOnSource.eqOn
-/

#print PartialHomeomorph.EqOnSource.symm_eqOn_target /-
/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
theorem EqOnSource.symm_eqOn_target {e e' : PartialHomeomorph α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2
#align local_homeomorph.eq_on_source.symm_eq_on_target PartialHomeomorph.EqOnSource.symm_eqOn_target
-/

#print PartialHomeomorph.EqOnSource.trans' /-
/-- Composition of local homeomorphisms respects equivalence -/
theorem EqOnSource.trans' {e e' : PartialHomeomorph α β} {f f' : PartialHomeomorph β γ}
    (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  PartialEquiv.EqOnSource.trans' he hf
#align local_homeomorph.eq_on_source.trans' PartialHomeomorph.EqOnSource.trans'
-/

#print PartialHomeomorph.EqOnSource.restr /-
/-- Restriction of local homeomorphisms respects equivalence -/
theorem EqOnSource.restr {e e' : PartialHomeomorph α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s :=
  PartialEquiv.EqOnSource.restr he _
#align local_homeomorph.eq_on_source.restr PartialHomeomorph.EqOnSource.restr
-/

#print PartialHomeomorph.Set.EqOn.restr_eqOn_source /-
theorem Set.EqOn.restr_eqOn_source {e e' : PartialHomeomorph α β}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source :=
  by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine' (eq_on.trans _ h).trans _ <;> simp only [mfld_simps]
#align local_homeomorph.set.eq_on.restr_eq_on_source PartialHomeomorph.Set.EqOn.restr_eqOn_source
-/

/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem trans_self_symm : e.trans e.symm ≈ PartialHomeomorph.ofSet e.source e.open_source :=
  PartialEquiv.trans_self_symm _
#align local_homeomorph.trans_self_symm PartialHomeomorph.trans_self_symm

theorem trans_symm_self : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
  e.symm.trans_self_symm
#align local_homeomorph.trans_symm_self PartialHomeomorph.trans_symm_self

#print PartialHomeomorph.eq_of_eqOnSource_univ /-
theorem eq_of_eqOnSource_univ {e e' : PartialHomeomorph α β} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  eq_of_partialEquiv_eq <| PartialEquiv.eq_of_eqOnSource_univ _ _ h s t
#align local_homeomorph.eq_of_eq_on_source_univ PartialHomeomorph.eq_of_eqOnSource_univ
-/

section Prod

#print PartialHomeomorph.prod /-
/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
@[simps (config := mfld_cfg) toPartialEquiv apply,
  simps (config := { attrs := [] }) source target symm_apply]
def prod (e : PartialHomeomorph α β) (e' : PartialHomeomorph γ δ) :
    PartialHomeomorph (α × γ) (β × δ)
    where
  open_source := e.open_source.Prod e'.open_source
  open_target := e.open_target.Prod e'.open_target
  continuous_toFun := e.ContinuousOn.Prod_map e'.ContinuousOn
  continuous_invFun := e.continuousOn_symm.Prod_map e'.continuousOn_symm
  toPartialEquiv := e.toPartialEquiv.Prod e'.toPartialEquiv
#align local_homeomorph.prod PartialHomeomorph.prod
-/

#print PartialHomeomorph.prod_symm /-
@[simp, mfld_simps]
theorem prod_symm (e : PartialHomeomorph α β) (e' : PartialHomeomorph γ δ) :
    (e.Prod e').symm = e.symm.Prod e'.symm :=
  rfl
#align local_homeomorph.prod_symm PartialHomeomorph.prod_symm
-/

#print PartialHomeomorph.refl_prod_refl /-
@[simp]
theorem refl_prod_refl {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] :
    (PartialHomeomorph.refl α).Prod (PartialHomeomorph.refl β) = PartialHomeomorph.refl (α × β) :=
  by ext1 ⟨x, y⟩; · rfl; · rintro ⟨x, y⟩; rfl; exact univ_prod_univ
#align local_homeomorph.refl_prod_refl PartialHomeomorph.refl_prod_refl
-/

#print PartialHomeomorph.prod_trans /-
@[simp, mfld_simps]
theorem prod_trans {η : Type _} {ε : Type _} [TopologicalSpace η] [TopologicalSpace ε]
    (e : PartialHomeomorph α β) (f : PartialHomeomorph β γ) (e' : PartialHomeomorph δ η)
    (f' : PartialHomeomorph η ε) : (e.Prod e').trans (f.Prod f') = (e.trans f).Prod (e'.trans f') :=
  PartialHomeomorph.eq_of_partialEquiv_eq <| by
    dsimp only [trans_to_local_equiv, prod_to_local_equiv] <;> apply PartialEquiv.prod_trans
#align local_homeomorph.prod_trans PartialHomeomorph.prod_trans
-/

#print PartialHomeomorph.prod_eq_prod_of_nonempty /-
theorem prod_eq_prod_of_nonempty {e₁ e₁' : PartialHomeomorph α β} {e₂ e₂' : PartialHomeomorph γ δ}
    (h : (e₁.Prod e₂).source.Nonempty) : e₁.Prod e₂ = e₁'.Prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' :=
  by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  haveI : Nonempty α := ⟨x⟩
  haveI : Nonempty β := ⟨e₁ x⟩
  haveI : Nonempty γ := ⟨y⟩
  haveI : Nonempty δ := ⟨e₂ y⟩
  simp_rw [PartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const, forall_forall_const,
    and_assoc', and_left_comm]
#align local_homeomorph.prod_eq_prod_of_nonempty PartialHomeomorph.prod_eq_prod_of_nonempty
-/

#print PartialHomeomorph.prod_eq_prod_of_nonempty' /-
theorem prod_eq_prod_of_nonempty' {e₁ e₁' : PartialHomeomorph α β} {e₂ e₂' : PartialHomeomorph γ δ}
    (h : (e₁'.Prod e₂').source.Nonempty) : e₁.Prod e₂ = e₁'.Prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ e₂']
#align local_homeomorph.prod_eq_prod_of_nonempty' PartialHomeomorph.prod_eq_prod_of_nonempty'
-/

end Prod

section Piecewise

#print PartialHomeomorph.piecewise /-
/-- Combine two `local_homeomorph`s using `set.piecewise`. The source of the new `local_homeomorph`
is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The
function sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t`
using `e'`, and similarly for the inverse function. To ensure that the maps `to_fun` and `inv_fun`
are inverse of each other on the new `source` and `target`, the definition assumes that the sets `s`
and `t` are related both by `e.is_image` and `e'.is_image`. To ensure that the new maps are
continuous on `source`/`target`, it also assumes that `e.source` and `e'.source` meet `frontier s`
on the same set and `e x = e' x` on this intersection. -/
@[simps (config := { fullyApplied := false }) toPartialEquiv apply]
def piecewise (e e' : PartialHomeomorph α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : PartialHomeomorph α β
    where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuous_toFun := continuousOn_piecewise_ite e.ContinuousOn e'.ContinuousOn Hs Heq
  continuous_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eq_on_of_inter_eq_of_eqOn Hs Heq)
#align local_homeomorph.piecewise PartialHomeomorph.piecewise
-/

#print PartialHomeomorph.symm_piecewise /-
@[simp]
theorem symm_piecewise (e e' : PartialHomeomorph α β) {s : Set α} {t : Set β}
    [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eq_on_of_inter_eq_of_eqOn Hs Heq) :=
  rfl
#align local_homeomorph.symm_piecewise PartialHomeomorph.symm_piecewise
-/

#print PartialHomeomorph.disjointUnion /-
/-- Combine two `local_homeomorph`s with disjoint sources and disjoint targets. We reuse
`local_homeomorph.piecewise` then override `to_local_equiv` to `local_equiv.disjoint_union`.
This way we have better definitional equalities for `source` and `target`. -/
def disjointUnion (e e' : PartialHomeomorph α β) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : PartialHomeomorph α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by rw [e.open_source.inter_frontier_eq]; exact eq_on_empty _ _)).replaceEquiv
    (e.toPartialEquiv.disjointUnion e'.toPartialEquiv Hs Ht)
    (PartialEquiv.disjointUnion_eq_piecewise _ _ _ _).symm
#align local_homeomorph.disjoint_union PartialHomeomorph.disjointUnion
-/

end Piecewise

section Pi

variable {ι : Type _} [Fintype ι] {Xi Yi : ι → Type _} [∀ i, TopologicalSpace (Xi i)]
  [∀ i, TopologicalSpace (Yi i)] (ei : ∀ i, PartialHomeomorph (Xi i) (Yi i))

#print PartialHomeomorph.pi /-
/-- The product of a finite family of `local_homeomorph`s. -/
@[simps toPartialEquiv]
def pi : PartialHomeomorph (∀ i, Xi i) (∀ i, Yi i)
    where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i hi => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i hi => (ei i).open_target
  continuous_toFun :=
    continuousOn_pi.2 fun i =>
      (ei i).ContinuousOn.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivial
  continuous_invFun :=
    continuousOn_pi.2 fun i =>
      (ei i).continuousOn_symm.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivial
#align local_homeomorph.pi PartialHomeomorph.pi
-/

end Pi

section Continuity

#print PartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_right /-
/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuousWithinAt_iff_continuousWithinAt_comp_right {f : β → γ} {s : Set β} {x : β}
    (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhds_within_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]
#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_right PartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_right
-/

#print PartialHomeomorph.continuousAt_iff_continuousAt_comp_right /-
/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
theorem continuousAt_iff_continuousAt_comp_right {f : β → γ} {x : β} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuousWithinAt_univ, e.continuous_within_at_iff_continuous_within_at_comp_right h,
    preimage_univ, continuousWithinAt_univ]
#align local_homeomorph.continuous_at_iff_continuous_at_comp_right PartialHomeomorph.continuousAt_iff_continuousAt_comp_right
-/

#print PartialHomeomorph.continuousOn_iff_continuousOn_comp_right /-
/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_right {f : β → γ} {s : Set β} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) :=
  by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, ball_image_iff]
  refine' forall₂_congr fun x hx => _
  rw [e.continuous_within_at_iff_continuous_within_at_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuousWithinAt_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))
#align local_homeomorph.continuous_on_iff_continuous_on_comp_right PartialHomeomorph.continuousOn_iff_continuousOn_comp_right
-/

#print PartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_left /-
/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
theorem continuousWithinAt_iff_continuousWithinAt_comp_left {f : γ → α} {s : Set γ} {x : γ}
    (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x :=
  by
  refine' ⟨(e.continuous_at hx).comp_continuousWithinAt, fun fe_cont => _⟩
  rw [← continuousWithinAt_inter' h] at fe_cont ⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuous_at_symm (e.map_source hx)).ContinuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])
#align local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left PartialHomeomorph.continuousWithinAt_iff_continuousWithinAt_comp_left
-/

#print PartialHomeomorph.continuousAt_iff_continuousAt_comp_left /-
/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
theorem continuousAt_iff_continuousAt_comp_left {f : γ → α} {x : γ} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x :=
  by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by rwa [nhdsWithin_univ]
  rw [← continuousWithinAt_univ, ← continuousWithinAt_univ,
    e.continuous_within_at_iff_continuous_within_at_comp_left hx h']
#align local_homeomorph.continuous_at_iff_continuous_at_comp_left PartialHomeomorph.continuousAt_iff_continuousAt_comp_left
-/

#print PartialHomeomorph.continuousOn_iff_continuousOn_comp_left /-
/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuousOn_iff_continuousOn_comp_left {f : γ → α} {s : Set γ} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun x hx =>
    e.continuousWithinAt_iff_continuousWithinAt_comp_left (h hx)
      (mem_of_superset self_mem_nhdsWithin h)
#align local_homeomorph.continuous_on_iff_continuous_on_comp_left PartialHomeomorph.continuousOn_iff_continuousOn_comp_left
-/

#print PartialHomeomorph.continuous_iff_continuous_comp_left /-
/-- A function is continuous if and only if its composition with a local homeomorphism
on the left is continuous and its image is contained in the source. -/
theorem continuous_iff_continuous_comp_left {f : γ → α} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) :=
  by
  simp only [continuous_iff_continuousOn_univ]
  exact e.continuous_on_iff_continuous_on_comp_left (Eq.symm h).Subset
#align local_homeomorph.continuous_iff_continuous_comp_left PartialHomeomorph.continuous_iff_continuous_comp_left
-/

end Continuity

#print PartialHomeomorph.homeomorphOfImageSubsetSource /-
/-- The homeomorphism obtained by restricting a `local_homeomorph` to a subset of the source. -/
@[simps]
def homeomorphOfImageSubsetSource {s : Set α} {t : Set β} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t where
  toFun a := ⟨e a, (congr_arg ((· ∈ ·) (e a)) ht).mp ⟨a, a.2, rfl⟩⟩
  invFun b :=
    ⟨e.symm b,
      let ⟨a, ha1, ha2⟩ := (congr_arg ((· ∈ ·) ↑b) ht).mpr b.2
      ha2 ▸ (e.left_inv (hs ha1)).symm ▸ ha1⟩
  left_inv a := Subtype.ext (e.left_inv (hs a.2))
  right_inv b :=
    let ⟨a, ha1, ha2⟩ := (congr_arg ((· ∈ ·) ↑b) ht).mpr b.2
    Subtype.ext (e.right_inv (ha2 ▸ e.map_source (hs ha1)))
  continuous_toFun :=
    (continuousOn_iff_continuous_restrict.mp (e.ContinuousOn.mono hs)).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_restrict.mp
          (e.continuousOn_symm.mono fun b hb =>
            let ⟨a, ha1, ha2⟩ := show b ∈ e '' s from ht.symm ▸ hb
            ha2 ▸ e.map_source (hs ha1))).subtype_mk
      _
#align local_homeomorph.homeomorph_of_image_subset_source PartialHomeomorph.homeomorphOfImageSubsetSource
-/

#print PartialHomeomorph.toHomeomorphSourceTarget /-
/-- A local homeomrphism defines a homeomorphism between its source and target. -/
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
#align local_homeomorph.to_homeomorph_source_target PartialHomeomorph.toHomeomorphSourceTarget
-/

#print PartialHomeomorph.secondCountableTopology_source /-
theorem secondCountableTopology_source [SecondCountableTopology β] (e : PartialHomeomorph α β) :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.SecondCountableTopology
#align local_homeomorph.second_countable_topology_source PartialHomeomorph.secondCountableTopology_source
-/

#print PartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv /-
/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps (config := mfld_cfg) apply symm_apply]
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set α)) (h' : e.target = univ) :
    α ≃ₜ β where
  toFun := e
  invFun := e.symm
  left_inv x := e.left_inv <| by rw [h]; exact mem_univ _
  right_inv x := e.right_inv <| by rw [h']; exact mem_univ _
  continuous_toFun := by
    rw [continuous_iff_continuousOn_univ]
    convert e.continuous_to_fun
    rw [h]
  continuous_invFun := by
    rw [continuous_iff_continuousOn_univ]
    convert e.continuous_inv_fun
    rw [h']
#align local_homeomorph.to_homeomorph_of_source_eq_univ_target_eq_univ PartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
-/

#print PartialHomeomorph.to_openEmbedding /-
/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `open_embedding.to_local_homeomorph`. -/
theorem to_openEmbedding (h : e.source = Set.univ) : OpenEmbedding e :=
  by
  apply openEmbedding_of_continuous_injective_open
  · apply continuous_iff_continuous_on_univ.mpr
    rw [← h]
    exact e.continuous_to_fun
  · apply set.injective_iff_inj_on_univ.mpr
    rw [← h]
    exact e.inj_on
  · intro U hU
    simpa only [h, subset_univ, mfld_simps] using e.image_open_of_open hU
#align local_homeomorph.to_open_embedding PartialHomeomorph.to_openEmbedding
-/

end PartialHomeomorph

namespace Homeomorph

variable (e : α ≃ₜ β) (e' : β ≃ₜ γ)

#print Homeomorph.refl_toPartialHomeomorph /-
/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/
@[simp, mfld_simps]
theorem refl_toPartialHomeomorph :
    (Homeomorph.refl α).toPartialHomeomorph = PartialHomeomorph.refl α :=
  rfl
#align homeomorph.refl_to_local_homeomorph Homeomorph.refl_toPartialHomeomorph
-/

#print Homeomorph.symm_toPartialHomeomorph /-
@[simp, mfld_simps]
theorem symm_toPartialHomeomorph : e.symm.toPartialHomeomorph = e.toPartialHomeomorph.symm :=
  rfl
#align homeomorph.symm_to_local_homeomorph Homeomorph.symm_toPartialHomeomorph
-/

#print Homeomorph.trans_toPartialHomeomorph /-
@[simp, mfld_simps]
theorem trans_toPartialHomeomorph :
    (e.trans e').toPartialHomeomorph = e.toPartialHomeomorph.trans e'.toPartialHomeomorph :=
  PartialHomeomorph.eq_of_partialEquiv_eq <| Equiv.trans_toPartialEquiv _ _
#align homeomorph.trans_to_local_homeomorph Homeomorph.trans_toPartialHomeomorph
-/

end Homeomorph

namespace OpenEmbedding

variable (f : α → β) (h : OpenEmbedding f)

#print OpenEmbedding.toPartialHomeomorph /-
/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `local_homeomorph.to_open_embedding`. -/
@[simps (config := mfld_cfg) apply source target]
noncomputable def toPartialHomeomorph [Nonempty α] : PartialHomeomorph α β :=
  PartialHomeomorph.ofContinuousOpen ((h.toEmbedding.inj.InjOn univ).toPartialEquiv _ _)
    h.Continuous.ContinuousOn h.IsOpenMap isOpen_univ
#align open_embedding.to_local_homeomorph OpenEmbedding.toPartialHomeomorph
-/

#print OpenEmbedding.continuousAt_iff /-
theorem continuousAt_iff {f : α → β} {g : β → γ} (hf : OpenEmbedding f) {x : α} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  by
  haveI : Nonempty α := ⟨x⟩
  convert ((hf.to_local_homeomorph f).continuousAt_iff_continuousAt_comp_right _).symm
  · apply (PartialHomeomorph.left_inv _ _).symm
    simp
  · simp
#align open_embedding.continuous_at_iff OpenEmbedding.continuousAt_iff
-/

end OpenEmbedding

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (s : Opens α) [Nonempty s]

#print TopologicalSpace.Opens.partialHomeomorphSubtypeCoe /-
/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
noncomputable def partialHomeomorphSubtypeCoe : PartialHomeomorph s α :=
  OpenEmbedding.toPartialHomeomorph _ s.2.openEmbedding_subtype_val
#align topological_space.opens.local_homeomorph_subtype_coe TopologicalSpace.Opens.partialHomeomorphSubtypeCoe
-/

#print TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_coe /-
@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_coe : (s.partialHomeomorphSubtypeCoe : s → α) = coe :=
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_coe TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_coe
-/

#print TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_source /-
@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_source : s.partialHomeomorphSubtypeCoe.source = Set.univ :=
  rfl
#align topological_space.opens.local_homeomorph_subtype_coe_source TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_source
-/

#print TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_target /-
@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_target : s.partialHomeomorphSubtypeCoe.target = s := by
  simp only [local_homeomorph_subtype_coe, Subtype.range_coe_subtype, mfld_simps]; rfl
#align topological_space.opens.local_homeomorph_subtype_coe_target TopologicalSpace.Opens.partialHomeomorphSubtypeCoe_target
-/

end TopologicalSpace.Opens

namespace PartialHomeomorph

open TopologicalSpace

variable (e : PartialHomeomorph α β)

variable (s : Opens α) [Nonempty s]

#print PartialHomeomorph.subtypeRestr /-
/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
noncomputable def subtypeRestr : PartialHomeomorph s β :=
  s.partialHomeomorphSubtypeCoe.trans e
#align local_homeomorph.subtype_restr PartialHomeomorph.subtypeRestr
-/

#print PartialHomeomorph.subtypeRestr_def /-
theorem subtypeRestr_def : e.subtypeRestr s = s.partialHomeomorphSubtypeCoe.trans e :=
  rfl
#align local_homeomorph.subtype_restr_def PartialHomeomorph.subtypeRestr_def
-/

#print PartialHomeomorph.subtypeRestr_coe /-
@[simp, mfld_simps]
theorem subtypeRestr_coe :
    ((e.subtypeRestr s : PartialHomeomorph s β) : s → β) = Set.restrict ↑s (e : α → β) :=
  rfl
#align local_homeomorph.subtype_restr_coe PartialHomeomorph.subtypeRestr_coe
-/

#print PartialHomeomorph.subtypeRestr_source /-
@[simp, mfld_simps]
theorem subtypeRestr_source : (e.subtypeRestr s).source = coe ⁻¹' e.source := by
  simp only [subtype_restr_def, mfld_simps]
#align local_homeomorph.subtype_restr_source PartialHomeomorph.subtypeRestr_source
-/

variable {s}

#print PartialHomeomorph.map_subtype_source /-
theorem map_subtype_source {x : s} (hxe : (x : α) ∈ e.source) : e x ∈ (e.subtypeRestr s).target :=
  by
  refine' ⟨e.map_source hxe, _⟩
  rw [s.local_homeomorph_subtype_coe_target, mem_preimage, e.left_inv_on hxe]
  exact x.prop
#align local_homeomorph.map_subtype_source PartialHomeomorph.map_subtype_source
-/

variable (s)

#print PartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr /-
/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : PartialHomeomorph α β) :
    (f.subtypeRestr s).symm.trans (f'.subtypeRestr s) ≈
      (f.symm.trans f').restr (f.target ∩ f.symm ⁻¹' s) :=
  by
  simp only [subtype_restr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.preimage_open_of_open_symm s.2
  rw [← of_set_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine' eq_on_source.trans' _ (eq_on_source_refl _)
  -- f' has been eliminated !!!
  have sets_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s :=
    by mfld_set_tac
  have openness₂ : IsOpen (s : Set α) := s.2
  rw [of_set_trans', sets_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine' eq_on_source.trans' (eq_on_source_refl _) _
  -- f has been eliminated !!!
  refine' Setoid.trans (trans_symm_self s.local_homeomorph_subtype_coe) _
  simp only [mfld_simps]
#align local_homeomorph.subtype_restr_symm_trans_subtype_restr PartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr
-/

#print PartialHomeomorph.subtypeRestr_symm_eqOn_of_le /-
theorem subtypeRestr_symm_eqOn_of_le {U V : Opens α} [Nonempty U] [Nonempty V] (hUV : U ≤ V) :
    EqOn (e.subtypeRestr V).symm (Set.inclusion hUV ∘ (e.subtypeRestr U).symm)
      (e.subtypeRestr U).target :=
  by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [PartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y ∈ V.local_homeomorph_subtype_coe.target :=
    by
    rw [opens.local_homeomorph_subtype_coe_target] at hy ⊢
    exact hUV hy.2
  refine' V.local_homeomorph_subtype_coe.inj_on _ trivial _
  · rw [← PartialHomeomorph.symm_target]
    apply PartialHomeomorph.map_source
    rw [PartialHomeomorph.symm_source]
    exact hyV
  · rw [V.local_homeomorph_subtype_coe.right_inv hyV]
    show _ = U.local_homeomorph_subtype_coe _
    rw [U.local_homeomorph_subtype_coe.right_inv hy.2]
#align local_homeomorph.subtype_restr_symm_eq_on_of_le PartialHomeomorph.subtypeRestr_symm_eqOn_of_le
-/

end PartialHomeomorph

