/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.local_homeomorph
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.LocalEquiv
import Mathbin.Topology.Sets.Opens

/-!
# Local homeomorphisms

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

open TopologicalSpace

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-- local homeomorphisms, defined on open subsets of the space -/
@[nolint has_nonempty_instance]
structure LocalHomeomorph (α : Type _) (β : Type _) [TopologicalSpace α]
  [TopologicalSpace β] extends LocalEquiv α β where
  open_source : IsOpen source
  open_target : IsOpen target
  continuous_to_fun : ContinuousOn to_fun source
  continuous_inv_fun : ContinuousOn inv_fun target
#align local_homeomorph LocalHomeomorph

namespace LocalHomeomorph

variable (e : LocalHomeomorph α β) (e' : LocalHomeomorph β γ)

instance : CoeFun (LocalHomeomorph α β) fun _ => α → β :=
  ⟨fun e => e.toFun⟩

/-- The inverse of a local homeomorphism -/
protected def symm : LocalHomeomorph β α :=
  { e.toLocalEquiv.symm with
    open_source := e.open_target
    open_target := e.open_source
    continuous_to_fun := e.continuous_inv_fun
    continuous_inv_fun := e.continuous_to_fun }
#align local_homeomorph.symm LocalHomeomorph.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : LocalHomeomorph α β) : α → β :=
  e
#align local_homeomorph.simps.apply LocalHomeomorph.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : LocalHomeomorph α β) : β → α :=
  e.symm
#align local_homeomorph.simps.symm_apply LocalHomeomorph.Simps.symmApply

initialize_simps_projections LocalHomeomorph (to_local_equiv_to_fun → apply,
  to_local_equiv_inv_fun → symmApply, to_local_equiv_source → source, to_local_equiv_target →
  target, -toLocalEquiv)

protected theorem continuous_on : ContinuousOn e e.source :=
  e.continuous_to_fun
#align local_homeomorph.continuous_on LocalHomeomorph.continuous_on

theorem continuous_on_symm : ContinuousOn e.symm e.target :=
  e.continuous_inv_fun
#align local_homeomorph.continuous_on_symm LocalHomeomorph.continuous_on_symm

@[simp, mfld_simps]
theorem mk_coe (e : LocalEquiv α β) (a b c d) : (LocalHomeomorph.mk e a b c d : α → β) = e :=
  rfl
#align local_homeomorph.mk_coe LocalHomeomorph.mk_coe

@[simp, mfld_simps]
theorem mk_coe_symm (e : LocalEquiv α β) (a b c d) :
    ((LocalHomeomorph.mk e a b c d).symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.mk_coe_symm LocalHomeomorph.mk_coe_symm

theorem to_local_equiv_injective : Injective (toLocalEquiv : LocalHomeomorph α β → LocalEquiv α β)
  | ⟨e, h₁, h₂, h₃, h₄⟩, ⟨e', h₁', h₂', h₃', h₄'⟩, rfl => rfl
#align local_homeomorph.to_local_equiv_injective LocalHomeomorph.to_local_equiv_injective

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem to_fun_eq_coe (e : LocalHomeomorph α β) : e.toFun = e :=
  rfl
#align local_homeomorph.to_fun_eq_coe LocalHomeomorph.to_fun_eq_coe

@[simp, mfld_simps]
theorem inv_fun_eq_coe (e : LocalHomeomorph α β) : e.invFun = e.symm :=
  rfl
#align local_homeomorph.inv_fun_eq_coe LocalHomeomorph.inv_fun_eq_coe

@[simp, mfld_simps]
theorem coe_coe : (e.toLocalEquiv : α → β) = e :=
  rfl
#align local_homeomorph.coe_coe LocalHomeomorph.coe_coe

@[simp, mfld_simps]
theorem coe_coe_symm : (e.toLocalEquiv.symm : β → α) = e.symm :=
  rfl
#align local_homeomorph.coe_coe_symm LocalHomeomorph.coe_coe_symm

@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h
#align local_homeomorph.map_source LocalHomeomorph.map_source

@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h
#align local_homeomorph.map_target LocalHomeomorph.map_target

@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h
#align local_homeomorph.left_inv LocalHomeomorph.left_inv

@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
#align local_homeomorph.right_inv LocalHomeomorph.right_inv

theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y :=
  e.toLocalEquiv.eq_symm_apply hx hy
#align local_homeomorph.eq_symm_apply LocalHomeomorph.eq_symm_apply

protected theorem maps_to : MapsTo e e.source e.target := fun x => e.map_source
#align local_homeomorph.maps_to LocalHomeomorph.maps_to

protected theorem symm_maps_to : MapsTo e.symm e.target e.source :=
  e.symm.MapsTo
#align local_homeomorph.symm_maps_to LocalHomeomorph.symm_maps_to

protected theorem left_inv_on : LeftInvOn e.symm e e.source := fun x => e.left_inv
#align local_homeomorph.left_inv_on LocalHomeomorph.left_inv_on

protected theorem right_inv_on : RightInvOn e.symm e e.target := fun x => e.right_inv
#align local_homeomorph.right_inv_on LocalHomeomorph.right_inv_on

protected theorem inv_on : InvOn e.symm e e.source e.target :=
  ⟨e.LeftInvOn, e.RightInvOn⟩
#align local_homeomorph.inv_on LocalHomeomorph.inv_on

protected theorem inj_on : InjOn e e.source :=
  e.LeftInvOn.InjOn
#align local_homeomorph.inj_on LocalHomeomorph.inj_on

protected theorem bij_on : BijOn e e.source e.target :=
  e.InvOn.BijOn e.MapsTo e.symm_maps_to
#align local_homeomorph.bij_on LocalHomeomorph.bij_on

protected theorem surj_on : SurjOn e e.source e.target :=
  e.BijOn.SurjOn
#align local_homeomorph.surj_on LocalHomeomorph.surj_on

/-- A homeomorphism induces a local homeomorphism on the whole space -/
@[simps (config := { mfld_cfg with simpRhs := true })]
def Homeomorph.toLocalHomeomorph (e : α ≃ₜ β) : LocalHomeomorph α β :=
  { e.toEquiv.toLocalEquiv with
    open_source := is_open_univ
    open_target := is_open_univ
    continuous_to_fun := by
      erw [← continuous_iff_continuous_on_univ]
      exact e.continuous_to_fun
    continuous_inv_fun := by
      erw [← continuous_iff_continuous_on_univ]
      exact e.continuous_inv_fun }
#align homeomorph.to_local_homeomorph Homeomorph.toLocalHomeomorph

/-- Replace `to_local_equiv` field to provide better definitional equalities. -/
def replaceEquiv (e : LocalHomeomorph α β) (e' : LocalEquiv α β) (h : e.toLocalEquiv = e') :
    LocalHomeomorph α β where
  toLocalEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuous_to_fun := h ▸ e.continuous_to_fun
  continuous_inv_fun := h ▸ e.continuous_inv_fun
#align local_homeomorph.replace_equiv LocalHomeomorph.replaceEquiv

theorem replace_equiv_eq_self (e : LocalHomeomorph α β) (e' : LocalEquiv α β)
    (h : e.toLocalEquiv = e') : e.replaceEquiv e' h = e :=
  by
  cases e
  subst e'
  rfl
#align local_homeomorph.replace_equiv_eq_self LocalHomeomorph.replace_equiv_eq_self

theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.MapsTo
#align local_homeomorph.source_preimage_target LocalHomeomorph.source_preimage_target

theorem eq_of_local_equiv_eq {e e' : LocalHomeomorph α β} (h : e.toLocalEquiv = e'.toLocalEquiv) :
    e = e' := by
  cases e
  cases e'
  cases h
  rfl
#align local_homeomorph.eq_of_local_equiv_eq LocalHomeomorph.eq_of_local_equiv_eq

theorem eventually_left_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'
#align local_homeomorph.eventually_left_inverse LocalHomeomorph.eventually_left_inverse

theorem eventually_left_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)
#align local_homeomorph.eventually_left_inverse' LocalHomeomorph.eventually_left_inverse'

theorem eventually_right_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'
#align local_homeomorph.eventually_right_inverse LocalHomeomorph.eventually_right_inverse

theorem eventually_right_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)
#align local_homeomorph.eventually_right_inverse' LocalHomeomorph.eventually_right_inverse'

theorem eventually_ne_nhds_within (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhds_within_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']
#align local_homeomorph.eventually_ne_nhds_within LocalHomeomorph.eventually_ne_nhds_within

theorem nhds_within_source_inter {x} (hx : x ∈ e.source) (s : Set α) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhds_within_inter_of_mem (mem_nhds_within_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)
#align local_homeomorph.nhds_within_source_inter LocalHomeomorph.nhds_within_source_inter

theorem nhds_within_target_inter {x} (hx : x ∈ e.target) (s : Set β) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhds_within_source_inter hx s
#align local_homeomorph.nhds_within_target_inter LocalHomeomorph.nhds_within_target_inter

theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toLocalEquiv.image_eq_target_inter_inv_preimage h
#align
  local_homeomorph.image_eq_target_inter_inv_preimage LocalHomeomorph.image_eq_target_inter_inv_preimage

theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toLocalEquiv.image_source_inter_eq' s
#align local_homeomorph.image_source_inter_eq' LocalHomeomorph.image_source_inter_eq'

theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toLocalEquiv.image_source_inter_eq s
#align local_homeomorph.image_source_inter_eq LocalHomeomorph.image_source_inter_eq

theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
#align
  local_homeomorph.symm_image_eq_source_inter_preimage LocalHomeomorph.symm_image_eq_source_inter_preimage

theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
#align local_homeomorph.symm_image_target_inter_eq LocalHomeomorph.symm_image_target_inter_eq

theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toLocalEquiv.source_inter_preimage_inv_preimage s
#align
  local_homeomorph.source_inter_preimage_inv_preimage LocalHomeomorph.source_inter_preimage_inv_preimage

theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
#align
  local_homeomorph.target_inter_inv_preimage_preimage LocalHomeomorph.target_inter_inv_preimage_preimage

theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toLocalEquiv.source_inter_preimage_target_inter s
#align
  local_homeomorph.source_inter_preimage_target_inter LocalHomeomorph.source_inter_preimage_target_inter

theorem image_source_eq_target (e : LocalHomeomorph α β) : e '' e.source = e.target :=
  e.toLocalEquiv.image_source_eq_target
#align local_homeomorph.image_source_eq_target LocalHomeomorph.image_source_eq_target

theorem symm_image_target_eq_source (e : LocalHomeomorph α β) : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
#align local_homeomorph.symm_image_target_eq_source LocalHomeomorph.symm_image_target_eq_source

/-- Two local homeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected theorem ext (e' : LocalHomeomorph α β) (h : ∀ x, e x = e' x)
    (hinv : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' :=
  eq_of_local_equiv_eq (LocalEquiv.ext h hinv hs)
#align local_homeomorph.ext LocalHomeomorph.ext

protected theorem ext_iff {e e' : LocalHomeomorph α β} :
    e = e' ↔ (∀ x, e x = e' x) ∧ (∀ x, e.symm x = e'.symm x) ∧ e.source = e'.source :=
  ⟨by
    rintro rfl
    exact ⟨fun x => rfl, fun x => rfl, rfl⟩, fun h => e.ext e' h.1 h.2.1 h.2.2⟩
#align local_homeomorph.ext_iff LocalHomeomorph.ext_iff

@[simp, mfld_simps]
theorem symm_to_local_equiv : e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
  rfl
#align local_homeomorph.symm_to_local_equiv LocalHomeomorph.symm_to_local_equiv

-- The following lemmas are already simp via local_equiv
theorem symm_source : e.symm.source = e.target :=
  rfl
#align local_homeomorph.symm_source LocalHomeomorph.symm_source

theorem symm_target : e.symm.target = e.source :=
  rfl
#align local_homeomorph.symm_target LocalHomeomorph.symm_target

@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e :=
  eq_of_local_equiv_eq <| by simp
#align local_homeomorph.symm_symm LocalHomeomorph.symm_symm

/-- A local homeomorphism is continuous at any point of its source -/
protected theorem continuous_at {x : α} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.ContinuousOn x h).ContinuousAt (e.open_source.mem_nhds h)
#align local_homeomorph.continuous_at LocalHomeomorph.continuous_at

/-- A local homeomorphism inverse is continuous at any point of its target -/
theorem continuous_at_symm {x : β} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.ContinuousAt h
#align local_homeomorph.continuous_at_symm LocalHomeomorph.continuous_at_symm

theorem tendsto_symm {x} (hx : x ∈ e.source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuous_at_symm (e.map_source hx)
#align local_homeomorph.tendsto_symm LocalHomeomorph.tendsto_symm

theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymm (e.ContinuousAt hx) <|
    le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)
#align local_homeomorph.map_nhds_eq LocalHomeomorph.map_nhds_eq

theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by rw [e.left_inv hx]
#align local_homeomorph.symm_map_nhds_eq LocalHomeomorph.symm_map_nhds_eq

theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set α} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs
#align local_homeomorph.image_mem_nhds LocalHomeomorph.image_mem_nhds

theorem map_nhds_within_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set α) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) :=
      congr_arg (map e) (e.nhds_within_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.LeftInvOn.mono <| inter_subset_left _ _).map_nhds_within_eq (e.left_inv hx)
        (e.continuous_at_symm (e.map_source hx)).ContinuousWithinAt
        (e.ContinuousAt hx).ContinuousWithinAt
    
#align local_homeomorph.map_nhds_within_eq LocalHomeomorph.map_nhds_within_eq

theorem map_nhds_within_preimage_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set β) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhds_within_target_inter (e.map_source hx)]
#align local_homeomorph.map_nhds_within_preimage_eq LocalHomeomorph.map_nhds_within_preimage_eq

theorem eventually_nhds (e : LocalHomeomorph α β) {x : α} (p : β → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans (by rw [e.map_nhds_eq hx]) eventually_map
#align local_homeomorph.eventually_nhds LocalHomeomorph.eventually_nhds

theorem eventually_nhds' (e : LocalHomeomorph α β) {x : α} (p : α → Prop) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x :=
  by
  rw [e.eventually_nhds _ hx]
  refine' eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => _)
  rw [hy]
#align local_homeomorph.eventually_nhds' LocalHomeomorph.eventually_nhds'

theorem eventually_nhds_within (e : LocalHomeomorph α β) {x : α} (p : β → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) :=
  by
  refine' Iff.trans _ eventually_map
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.nhds_within_target_inter (e.maps_to hx)]
#align local_homeomorph.eventually_nhds_within LocalHomeomorph.eventually_nhds_within

theorem eventually_nhds_within' (e : LocalHomeomorph α β) {x : α} (p : α → Prop) {s : Set α}
    (hx : x ∈ e.source) : (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x :=
  by
  rw [e.eventually_nhds_within _ hx]
  refine'
    eventually_congr
      ((eventually_nhds_within_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy =>
        _)
  rw [hy]
#align local_homeomorph.eventually_nhds_within' LocalHomeomorph.eventually_nhds_within'

/-- This lemma is useful in the manifold library in the case that `e` is a chart. It states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a chart on `γ`).  -/
theorem preimage_eventually_eq_target_inter_preimage_inter {e : LocalHomeomorph α β} {s : Set α}
    {t : Set γ} {x : α} {f : α → γ} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.source)
    (ht : t ∈ 𝓝 (f x)) : e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set β) :=
  by
  rw [eventually_eq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe,
    mem_nhds_within_iff_eventually.mp (hf.preimage_mem_nhds_within ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.maps_to hy, true_and_iff, iff_self_and,
    e.left_inv hy, iff_true_intro hyu]
#align
  local_homeomorph.preimage_eventually_eq_target_inter_preimage_inter LocalHomeomorph.preimage_eventually_eq_target_inter_preimage_inter

theorem preimage_open_of_open {s : Set β} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.ContinuousOn.preimage_open_of_open e.open_source hs
#align local_homeomorph.preimage_open_of_open LocalHomeomorph.preimage_open_of_open

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


/-- We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)
#align local_homeomorph.is_image LocalHomeomorph.IsImage

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

theorem to_local_equiv (h : e.IsImage s t) : e.toLocalEquiv.IsImage s t :=
  h
#align local_homeomorph.is_image.to_local_equiv LocalHomeomorph.IsImage.to_local_equiv

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
#align local_homeomorph.is_image.apply_mem_iff LocalHomeomorph.IsImage.apply_mem_iff

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toLocalEquiv.symm
#align local_homeomorph.is_image.symm LocalHomeomorph.IsImage.symm

theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy
#align local_homeomorph.is_image.symm_apply_mem_iff LocalHomeomorph.IsImage.symm_apply_mem_iff

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align local_homeomorph.is_image.symm_iff LocalHomeomorph.IsImage.symm_iff

protected theorem maps_to (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  h.toLocalEquiv.MapsTo
#align local_homeomorph.is_image.maps_to LocalHomeomorph.IsImage.maps_to

theorem symm_maps_to (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.MapsTo
#align local_homeomorph.is_image.symm_maps_to LocalHomeomorph.IsImage.symm_maps_to

theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.toLocalEquiv.image_eq
#align local_homeomorph.is_image.image_eq LocalHomeomorph.IsImage.image_eq

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
#align local_homeomorph.is_image.symm_image_eq LocalHomeomorph.IsImage.symm_image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  LocalEquiv.IsImage.iff_preimage_eq
#align local_homeomorph.is_image.iff_preimage_eq LocalHomeomorph.IsImage.iff_preimage_eq

alias iff_preimage_eq ↔ preimage_eq of_preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq
#align local_homeomorph.is_image.iff_symm_preimage_eq LocalHomeomorph.IsImage.iff_symm_preimage_eq

alias iff_symm_preimage_eq ↔ symm_preimage_eq of_symm_preimage_eq

theorem iff_symm_preimage_eq' :
    e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']
#align local_homeomorph.is_image.iff_symm_preimage_eq' LocalHomeomorph.IsImage.iff_symm_preimage_eq'

alias iff_symm_preimage_eq' ↔ symm_preimage_eq' of_symm_preimage_eq'

theorem iff_preimage_eq' : e.IsImage s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'
#align local_homeomorph.is_image.iff_preimage_eq' LocalHomeomorph.IsImage.iff_preimage_eq'

alias iff_preimage_eq' ↔ preimage_eq' of_preimage_eq'

theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  LocalEquiv.IsImage.of_image_eq h
#align local_homeomorph.is_image.of_image_eq LocalHomeomorph.IsImage.of_image_eq

theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  LocalEquiv.IsImage.of_symm_image_eq h
#align local_homeomorph.is_image.of_symm_image_eq LocalHomeomorph.IsImage.of_symm_image_eq

protected theorem compl (h : e.IsImage s t) : e.IsImage (sᶜ) (tᶜ) := fun x hx => not_congr (h hx)
#align local_homeomorph.is_image.compl LocalHomeomorph.IsImage.compl

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun x hx => and_congr (h hx) (h' hx)
#align local_homeomorph.is_image.inter LocalHomeomorph.IsImage.inter

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun x hx => or_congr (h hx) (h' hx)
#align local_homeomorph.is_image.union LocalHomeomorph.IsImage.union

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
#align local_homeomorph.is_image.diff LocalHomeomorph.IsImage.diff

theorem left_inv_on_piecewise {e' : LocalHomeomorph α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.toLocalEquiv.left_inv_on_piecewise h'
#align local_homeomorph.is_image.left_inv_on_piecewise LocalHomeomorph.IsImage.left_inv_on_piecewise

theorem inter_eq_of_inter_eq_of_eq_on {e' : LocalHomeomorph α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t :=
  h.toLocalEquiv.inter_eq_of_inter_eq_of_eq_on h' hs Heq
#align
  local_homeomorph.is_image.inter_eq_of_inter_eq_of_eq_on LocalHomeomorph.IsImage.inter_eq_of_inter_eq_of_eq_on

theorem symm_eq_on_of_inter_eq_of_eq_on {e' : LocalHomeomorph α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) :=
  h.toLocalEquiv.symm_eq_on_of_inter_eq_of_eq_on hs Heq
#align
  local_homeomorph.is_image.symm_eq_on_of_inter_eq_of_eq_on LocalHomeomorph.IsImage.symm_eq_on_of_inter_eq_of_eq_on

theorem map_nhds_within_eq (h : e.IsImage s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhds_within_eq hx, h.image_eq, e.nhds_within_target_inter (e.map_source hx)]
#align local_homeomorph.is_image.map_nhds_within_eq LocalHomeomorph.IsImage.map_nhds_within_eq

protected theorem closure (h : e.IsImage s t) : e.IsImage (closure s) (closure t) := fun x hx => by
  simp only [mem_closure_iff_nhds_within_ne_bot, ← h.map_nhds_within_eq hx, map_ne_bot_iff]
#align local_homeomorph.is_image.closure LocalHomeomorph.IsImage.closure

protected theorem interior (h : e.IsImage s t) : e.IsImage (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl
#align local_homeomorph.is_image.interior LocalHomeomorph.IsImage.interior

protected theorem frontier (h : e.IsImage s t) : e.IsImage (frontier s) (frontier t) :=
  h.closure.diff h.interior
#align local_homeomorph.is_image.frontier LocalHomeomorph.IsImage.frontier

theorem is_open_iff (h : e.IsImage s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.preimage_open_of_open hs, fun hs =>
    h.preimage_eq' ▸ e.preimage_open_of_open hs⟩
#align local_homeomorph.is_image.is_open_iff LocalHomeomorph.IsImage.is_open_iff

/-- Restrict a `local_homeomorph` to a pair of corresponding open sets. -/
@[simps toLocalEquiv]
def restr (h : e.IsImage s t) (hs : IsOpen (e.source ∩ s)) : LocalHomeomorph α β
    where
  toLocalEquiv := h.toLocalEquiv.restr
  open_source := hs
  open_target := h.is_open_iff.1 hs
  continuous_to_fun := e.ContinuousOn.mono (inter_subset_left _ _)
  continuous_inv_fun := e.symm.ContinuousOn.mono (inter_subset_left _ _)
#align local_homeomorph.is_image.restr LocalHomeomorph.IsImage.restr

end IsImage

theorem is_image_source_target : e.IsImage e.source e.target :=
  e.toLocalEquiv.is_image_source_target
#align local_homeomorph.is_image_source_target LocalHomeomorph.is_image_source_target

theorem is_image_source_target_of_disjoint (e' : LocalHomeomorph α β)
    (hs : Disjoint e.source e'.source) (ht : Disjoint e.target e'.target) :
    e.IsImage e'.source e'.target :=
  e.toLocalEquiv.is_image_source_target_of_disjoint e'.toLocalEquiv hs ht
#align
  local_homeomorph.is_image_source_target_of_disjoint LocalHomeomorph.is_image_source_target_of_disjoint

/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
theorem preimage_interior (s : Set β) :
    e.source ∩ e ⁻¹' interior s = e.source ∩ interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).interior.preimage_eq
#align local_homeomorph.preimage_interior LocalHomeomorph.preimage_interior

theorem preimage_closure (s : Set β) : e.source ∩ e ⁻¹' closure s = e.source ∩ closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq
#align local_homeomorph.preimage_closure LocalHomeomorph.preimage_closure

theorem preimage_frontier (s : Set β) :
    e.source ∩ e ⁻¹' frontier s = e.source ∩ frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).frontier.preimage_eq
#align local_homeomorph.preimage_frontier LocalHomeomorph.preimage_frontier

theorem preimage_open_of_open_symm {s : Set α} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.ContinuousOn.preimage_open_of_open e.open_target hs
#align local_homeomorph.preimage_open_of_open_symm LocalHomeomorph.preimage_open_of_open_symm

/-- The image of an open set in the source is open. -/
theorem image_open_of_open {s : Set α} (hs : IsOpen s) (h : s ⊆ e.source) : IsOpen (e '' s) :=
  by
  have : e '' s = e.target ∩ e.symm ⁻¹' s := e.to_local_equiv.image_eq_target_inter_inv_preimage h
  rw [this]
  exact e.continuous_on_symm.preimage_open_of_open e.open_target hs
#align local_homeomorph.image_open_of_open LocalHomeomorph.image_open_of_open

/-- The image of the restriction of an open set to the source is open. -/
theorem image_open_of_open' {s : Set α} (hs : IsOpen s) : IsOpen (e '' (e.source ∩ s)) :=
  image_open_of_open _ (IsOpen.inter e.open_source hs) (inter_subset_left _ _)
#align local_homeomorph.image_open_of_open' LocalHomeomorph.image_open_of_open'

/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def ofContinuousOpenRestrict (e : LocalEquiv α β) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : LocalHomeomorph α β
    where
  toLocalEquiv := e
  open_source := hs
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.is_open_range
  continuous_to_fun := hc
  continuous_inv_fun := e.image_source_eq_target ▸ ho.continuous_on_image_of_left_inv_on e.LeftInvOn
#align local_homeomorph.of_continuous_open_restrict LocalHomeomorph.ofContinuousOpenRestrict

/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def ofContinuousOpen (e : LocalEquiv α β) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : LocalHomeomorph α β :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs
#align local_homeomorph.of_continuous_open LocalHomeomorph.ofContinuousOpen

/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restrOpen (s : Set α) (hs : IsOpen s) : LocalHomeomorph α β :=
  (@IsImage.of_symm_preimage_eq α β _ _ e s (e.symm ⁻¹' s) rfl).restr
    (IsOpen.inter e.open_source hs)
#align local_homeomorph.restr_open LocalHomeomorph.restrOpen

@[simp, mfld_simps]
theorem restr_open_to_local_equiv (s : Set α) (hs : IsOpen s) :
    (e.restrOpen s hs).toLocalEquiv = e.toLocalEquiv.restr s :=
  rfl
#align local_homeomorph.restr_open_to_local_equiv LocalHomeomorph.restr_open_to_local_equiv

-- Already simp via local_equiv
theorem restr_open_source (s : Set α) (hs : IsOpen s) : (e.restrOpen s hs).source = e.source ∩ s :=
  rfl
#align local_homeomorph.restr_open_source LocalHomeomorph.restr_open_source

/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
@[simps (config := mfld_cfg) apply symmApply, simps (config := { attrs := [] }) source target]
protected def restr (s : Set α) : LocalHomeomorph α β :=
  e.restrOpen (interior s) is_open_interior
#align local_homeomorph.restr LocalHomeomorph.restr

@[simp, mfld_simps]
theorem restr_to_local_equiv (s : Set α) :
    (e.restr s).toLocalEquiv = e.toLocalEquiv.restr (interior s) :=
  rfl
#align local_homeomorph.restr_to_local_equiv LocalHomeomorph.restr_to_local_equiv

theorem restr_source' (s : Set α) (hs : IsOpen s) : (e.restr s).source = e.source ∩ s := by
  rw [e.restr_source, hs.interior_eq]
#align local_homeomorph.restr_source' LocalHomeomorph.restr_source'

theorem restr_to_local_equiv' (s : Set α) (hs : IsOpen s) :
    (e.restr s).toLocalEquiv = e.toLocalEquiv.restr s := by
  rw [e.restr_to_local_equiv, hs.interior_eq]
#align local_homeomorph.restr_to_local_equiv' LocalHomeomorph.restr_to_local_equiv'

theorem restr_eq_of_source_subset {e : LocalHomeomorph α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e := by
  apply eq_of_local_equiv_eq
  rw [restr_to_local_equiv]
  apply LocalEquiv.restr_eq_of_source_subset
  exact interior_maximal h e.open_source
#align local_homeomorph.restr_eq_of_source_subset LocalHomeomorph.restr_eq_of_source_subset

@[simp, mfld_simps]
theorem restr_univ {e : LocalHomeomorph α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)
#align local_homeomorph.restr_univ LocalHomeomorph.restr_univ

theorem restr_source_inter (s : Set α) : e.restr (e.source ∩ s) = e.restr s :=
  by
  refine' LocalHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) _
  simp [e.open_source.interior_eq, ← inter_assoc]
#align local_homeomorph.restr_source_inter LocalHomeomorph.restr_source_inter

/-- The identity on the whole space as a local homeomorphism. -/
@[simps (config := mfld_cfg) apply, simps (config := { attrs := [] }) source target]
protected def refl (α : Type _) [TopologicalSpace α] : LocalHomeomorph α α :=
  (Homeomorph.refl α).toLocalHomeomorph
#align local_homeomorph.refl LocalHomeomorph.refl

@[simp, mfld_simps]
theorem refl_local_equiv : (LocalHomeomorph.refl α).toLocalEquiv = LocalEquiv.refl α :=
  rfl
#align local_homeomorph.refl_local_equiv LocalHomeomorph.refl_local_equiv

@[simp, mfld_simps]
theorem refl_symm : (LocalHomeomorph.refl α).symm = LocalHomeomorph.refl α :=
  rfl
#align local_homeomorph.refl_symm LocalHomeomorph.refl_symm

section

variable {s : Set α} (hs : IsOpen s)

/-- The identity local equiv on a set `s` -/
@[simps (config := mfld_cfg) apply, simps (config := { attrs := [] }) source target]
def ofSet (s : Set α) (hs : IsOpen s) : LocalHomeomorph α α :=
  { LocalEquiv.ofSet s with
    open_source := hs
    open_target := hs
    continuous_to_fun := continuous_id.ContinuousOn
    continuous_inv_fun := continuous_id.ContinuousOn }
#align local_homeomorph.of_set LocalHomeomorph.ofSet

@[simp, mfld_simps]
theorem of_set_to_local_equiv : (ofSet s hs).toLocalEquiv = LocalEquiv.ofSet s :=
  rfl
#align local_homeomorph.of_set_to_local_equiv LocalHomeomorph.of_set_to_local_equiv

@[simp, mfld_simps]
theorem of_set_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl
#align local_homeomorph.of_set_symm LocalHomeomorph.of_set_symm

@[simp, mfld_simps]
theorem of_set_univ_eq_refl : ofSet univ is_open_univ = LocalHomeomorph.refl α := by ext <;> simp
#align local_homeomorph.of_set_univ_eq_refl LocalHomeomorph.of_set_univ_eq_refl

end

/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.target = e'.source) : LocalHomeomorph α γ :=
  {
    LocalEquiv.trans' e.toLocalEquiv e'.toLocalEquiv
      h with
    open_source := e.open_source
    open_target := e'.open_target
    continuous_to_fun := by
      apply e'.continuous_to_fun.comp e.continuous_to_fun
      rw [← h]
      exact e.to_local_equiv.source_subset_preimage_target
    continuous_inv_fun :=
      by
      apply e.continuous_inv_fun.comp e'.continuous_inv_fun
      rw [h]
      exact e'.to_local_equiv.target_subset_preimage_source }
#align local_homeomorph.trans' LocalHomeomorph.trans'

/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : LocalHomeomorph α γ :=
  LocalHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])
#align local_homeomorph.trans LocalHomeomorph.trans

@[simp, mfld_simps]
theorem trans_to_local_equiv : (e.trans e').toLocalEquiv = e.toLocalEquiv.trans e'.toLocalEquiv :=
  rfl
#align local_homeomorph.trans_to_local_equiv LocalHomeomorph.trans_to_local_equiv

@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl
#align local_homeomorph.coe_trans LocalHomeomorph.coe_trans

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl
#align local_homeomorph.coe_trans_symm LocalHomeomorph.coe_trans_symm

theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl
#align local_homeomorph.trans_apply LocalHomeomorph.trans_apply

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := by
  cases e <;> cases e' <;> rfl
#align local_homeomorph.trans_symm_eq_symm_trans_symm LocalHomeomorph.trans_symm_eq_symm_trans_symm

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  LocalEquiv.trans_source e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source LocalHomeomorph.trans_source

theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  LocalEquiv.trans_source' e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source' LocalHomeomorph.trans_source'

theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) :=
  LocalEquiv.trans_source'' e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.trans_source'' LocalHomeomorph.trans_source''

theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  LocalEquiv.image_trans_source e.toLocalEquiv e'.toLocalEquiv
#align local_homeomorph.image_trans_source LocalHomeomorph.image_trans_source

theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
#align local_homeomorph.trans_target LocalHomeomorph.trans_target

theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
#align local_homeomorph.trans_target' LocalHomeomorph.trans_target'

theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
#align local_homeomorph.trans_target'' LocalHomeomorph.trans_target''

theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
#align local_homeomorph.inv_image_trans_target LocalHomeomorph.inv_image_trans_target

theorem trans_assoc (e'' : LocalHomeomorph γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  eq_of_local_equiv_eq <| LocalEquiv.trans_assoc e.toLocalEquiv e'.toLocalEquiv e''.toLocalEquiv
#align local_homeomorph.trans_assoc LocalHomeomorph.trans_assoc

@[simp, mfld_simps]
theorem trans_refl : e.trans (LocalHomeomorph.refl β) = e :=
  eq_of_local_equiv_eq <| LocalEquiv.trans_refl e.toLocalEquiv
#align local_homeomorph.trans_refl LocalHomeomorph.trans_refl

@[simp, mfld_simps]
theorem refl_trans : (LocalHomeomorph.refl α).trans e = e :=
  eq_of_local_equiv_eq <| LocalEquiv.refl_trans e.toLocalEquiv
#align local_homeomorph.refl_trans LocalHomeomorph.refl_trans

theorem trans_of_set {s : Set β} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  (LocalHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [LocalEquiv.trans_source, (e.preimage_interior _).symm, hs.interior_eq]
#align local_homeomorph.trans_of_set LocalHomeomorph.trans_of_set

theorem trans_of_set' {s : Set β} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source ∩ e ⁻¹' s) := by rw [trans_of_set, restr_source_inter]
#align local_homeomorph.trans_of_set' LocalHomeomorph.trans_of_set'

theorem of_set_trans {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  (LocalHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [LocalEquiv.trans_source, hs.interior_eq, inter_comm]
#align local_homeomorph.of_set_trans LocalHomeomorph.of_set_trans

theorem of_set_trans' {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr (e.source ∩ s) :=
  by rw [of_set_trans, restr_source_inter]
#align local_homeomorph.of_set_trans' LocalHomeomorph.of_set_trans'

@[simp, mfld_simps]
theorem of_set_trans_of_set {s : Set α} (hs : IsOpen s) {s' : Set α} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') :=
  by
  rw [(of_set s hs).trans_of_set hs']
  ext <;> simp [hs'.interior_eq]
#align local_homeomorph.of_set_trans_of_set LocalHomeomorph.of_set_trans_of_set

theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  eq_of_local_equiv_eq <| LocalEquiv.restr_trans e.toLocalEquiv e'.toLocalEquiv (interior s)
#align local_homeomorph.restr_trans LocalHomeomorph.restr_trans

/-- Postcompose a local homeomorphism with an homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps (config := { fullyApplied := false })]
def transHomeomorph (e' : β ≃ₜ γ) : LocalHomeomorph α γ
    where
  toLocalEquiv := e.toLocalEquiv.transEquiv e'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.Preimage e'.symm.Continuous
  continuous_to_fun := e'.Continuous.comp_continuous_on e.ContinuousOn
  continuous_inv_fun := e.symm.ContinuousOn.comp e'.symm.Continuous.ContinuousOn fun x h => h
#align local_homeomorph.trans_homeomorph LocalHomeomorph.transHomeomorph

theorem trans_equiv_eq_trans (e' : β ≃ₜ γ) : e.transHomeomorph e' = e.trans e'.toLocalHomeomorph :=
  to_local_equiv_injective <| LocalEquiv.transEquiv_eq_trans _ _
#align local_homeomorph.trans_equiv_eq_trans LocalHomeomorph.trans_equiv_eq_trans

/-- Precompose a local homeomorphism with an homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps (config := { fullyApplied := false })]
def Homeomorph.transLocalHomeomorph (e : α ≃ₜ β) : LocalHomeomorph α γ
    where
  toLocalEquiv := e.toEquiv.transLocalEquiv e'.toLocalEquiv
  open_source := e'.open_source.Preimage e.Continuous
  open_target := e'.open_target
  continuous_to_fun := e'.ContinuousOn.comp e.Continuous.ContinuousOn fun x h => h
  continuous_inv_fun := e.symm.Continuous.comp_continuous_on e'.symm.ContinuousOn
#align homeomorph.trans_local_homeomorph Homeomorph.transLocalHomeomorph

theorem Homeomorph.trans_local_homeomorph_eq_trans (e : α ≃ₜ β) :
    e.transLocalHomeomorph e' = e.toLocalHomeomorph.trans e' :=
  to_local_equiv_injective <| Equiv.trans_localEquiv_eq_trans _ _
#align homeomorph.trans_local_homeomorph_eq_trans Homeomorph.trans_local_homeomorph_eq_trans

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def EqOnSource (e e' : LocalHomeomorph α β) : Prop :=
  e.source = e'.source ∧ EqOn e e' e.source
#align local_homeomorph.eq_on_source LocalHomeomorph.EqOnSource

theorem eq_on_source_iff (e e' : LocalHomeomorph α β) :
    EqOnSource e e' ↔ LocalEquiv.EqOnSource e.toLocalEquiv e'.toLocalEquiv :=
  Iff.rfl
#align local_homeomorph.eq_on_source_iff LocalHomeomorph.eq_on_source_iff

/-- `eq_on_source` is an equivalence relation -/
instance : Setoid (LocalHomeomorph α β)
    where
  R := EqOnSource
  iseqv :=
    ⟨fun e => (@LocalEquiv.eqOnSourceSetoid α β).iseqv.1 e.toLocalEquiv, fun e e' h =>
      (@LocalEquiv.eqOnSourceSetoid α β).iseqv.2.1 ((eq_on_source_iff e e').1 h),
      fun e e' e'' h h' =>
      (@LocalEquiv.eqOnSourceSetoid α β).iseqv.2.2 ((eq_on_source_iff e e').1 h)
        ((eq_on_source_iff e' e'').1 h')⟩

theorem eq_on_source_refl : e ≈ e :=
  Setoid.refl _
#align local_homeomorph.eq_on_source_refl LocalHomeomorph.eq_on_source_refl

/-- If two local homeomorphisms are equivalent, so are their inverses -/
theorem EqOnSource.symm' {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
  LocalEquiv.EqOnSource.symm' h
#align local_homeomorph.eq_on_source.symm' LocalHomeomorph.EqOnSource.symm'

/-- Two equivalent local homeomorphisms have the same source -/
theorem EqOnSource.source_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.source = e'.source :=
  h.1
#align local_homeomorph.eq_on_source.source_eq LocalHomeomorph.EqOnSource.source_eq

/-- Two equivalent local homeomorphisms have the same target -/
theorem EqOnSource.target_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.target = e'.target :=
  h.symm'.1
#align local_homeomorph.eq_on_source.target_eq LocalHomeomorph.EqOnSource.target_eq

/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
theorem EqOnSource.eq_on {e e' : LocalHomeomorph α β} (h : e ≈ e') : EqOn e e' e.source :=
  h.2
#align local_homeomorph.eq_on_source.eq_on LocalHomeomorph.EqOnSource.eq_on

/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
theorem EqOnSource.symm_eq_on_target {e e' : LocalHomeomorph α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  h.symm'.2
#align local_homeomorph.eq_on_source.symm_eq_on_target LocalHomeomorph.EqOnSource.symm_eq_on_target

/-- Composition of local homeomorphisms respects equivalence -/
theorem EqOnSource.trans' {e e' : LocalHomeomorph α β} {f f' : LocalHomeomorph β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  LocalEquiv.EqOnSource.trans' he hf
#align local_homeomorph.eq_on_source.trans' LocalHomeomorph.EqOnSource.trans'

/-- Restriction of local homeomorphisms respects equivalence -/
theorem EqOnSource.restr {e e' : LocalHomeomorph α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s :=
  LocalEquiv.EqOnSource.restr he _
#align local_homeomorph.eq_on_source.restr LocalHomeomorph.EqOnSource.restr

theorem Set.EqOn.restr_eq_on_source {e e' : LocalHomeomorph α β}
    (h : EqOn e e' (e.source ∩ e'.source)) : e.restr e'.source ≈ e'.restr e.source :=
  by
  constructor
  · rw [e'.restr_source' _ e.open_source]
    rw [e.restr_source' _ e'.open_source]
    exact Set.inter_comm _ _
  · rw [e.restr_source' _ e'.open_source]
    refine' (eq_on.trans _ h).trans _ <;> simp only [mfld_simps]
#align local_homeomorph.set.eq_on.restr_eq_on_source LocalHomeomorph.Set.EqOn.restr_eq_on_source

/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem trans_self_symm : e.trans e.symm ≈ LocalHomeomorph.ofSet e.source e.open_source :=
  LocalEquiv.trans_self_symm _
#align local_homeomorph.trans_self_symm LocalHomeomorph.trans_self_symm

theorem trans_symm_self : e.symm.trans e ≈ LocalHomeomorph.ofSet e.target e.open_target :=
  e.symm.trans_self_symm
#align local_homeomorph.trans_symm_self LocalHomeomorph.trans_symm_self

theorem eq_of_eq_on_source_univ {e e' : LocalHomeomorph α β} (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' :=
  eq_of_local_equiv_eq <| LocalEquiv.eq_of_eq_on_source_univ _ _ h s t
#align local_homeomorph.eq_of_eq_on_source_univ LocalHomeomorph.eq_of_eq_on_source_univ

section Prod

/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
@[simps (config := mfld_cfg) toLocalEquiv apply,
  simps (config := { attrs := [] }) source target symmApply]
def prod (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) : LocalHomeomorph (α × γ) (β × δ)
    where
  open_source := e.open_source.Prod e'.open_source
  open_target := e.open_target.Prod e'.open_target
  continuous_to_fun := e.ContinuousOn.prod_map e'.ContinuousOn
  continuous_inv_fun := e.continuous_on_symm.prod_map e'.continuous_on_symm
  toLocalEquiv := e.toLocalEquiv.Prod e'.toLocalEquiv
#align local_homeomorph.prod LocalHomeomorph.prod

@[simp, mfld_simps]
theorem prod_symm (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) :
    (e.Prod e').symm = e.symm.Prod e'.symm :=
  rfl
#align local_homeomorph.prod_symm LocalHomeomorph.prod_symm

@[simp]
theorem refl_prod_refl {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] :
    (LocalHomeomorph.refl α).Prod (LocalHomeomorph.refl β) = LocalHomeomorph.refl (α × β) :=
  by
  ext1 ⟨x, y⟩
  · rfl
  · rintro ⟨x, y⟩
    rfl
  exact univ_prod_univ
#align local_homeomorph.refl_prod_refl LocalHomeomorph.refl_prod_refl

@[simp, mfld_simps]
theorem prod_trans {η : Type _} {ε : Type _} [TopologicalSpace η] [TopologicalSpace ε]
    (e : LocalHomeomorph α β) (f : LocalHomeomorph β γ) (e' : LocalHomeomorph δ η)
    (f' : LocalHomeomorph η ε) : (e.Prod e').trans (f.Prod f') = (e.trans f).Prod (e'.trans f') :=
  LocalHomeomorph.eq_of_local_equiv_eq <| by
    dsimp only [trans_to_local_equiv, prod_to_local_equiv] <;> apply LocalEquiv.prod_trans
#align local_homeomorph.prod_trans LocalHomeomorph.prod_trans

theorem prod_eq_prod_of_nonempty {e₁ e₁' : LocalHomeomorph α β} {e₂ e₂' : LocalHomeomorph γ δ}
    (h : (e₁.Prod e₂).source.Nonempty) : e₁.Prod e₂ = e₁'.Prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' :=
  by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  haveI : Nonempty α := ⟨x⟩
  haveI : Nonempty β := ⟨e₁ x⟩
  haveI : Nonempty γ := ⟨y⟩
  haveI : Nonempty δ := ⟨e₂ y⟩
  simp_rw [LocalHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const, forall_forall_const,
    and_assoc', and_left_comm]
#align local_homeomorph.prod_eq_prod_of_nonempty LocalHomeomorph.prod_eq_prod_of_nonempty

theorem prod_eq_prod_of_nonempty' {e₁ e₁' : LocalHomeomorph α β} {e₂ e₂' : LocalHomeomorph γ δ}
    (h : (e₁'.Prod e₂').source.Nonempty) : e₁.Prod e₂ = e₁'.Prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ e₂']
#align local_homeomorph.prod_eq_prod_of_nonempty' LocalHomeomorph.prod_eq_prod_of_nonempty'

end Prod

section Piecewise

/-- Combine two `local_homeomorph`s using `set.piecewise`. The source of the new `local_homeomorph`
is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The
function sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t`
using `e'`, and similarly for the inverse function. To ensure that the maps `to_fun` and `inv_fun`
are inverse of each other on the new `source` and `target`, the definition assumes that the sets `s`
and `t` are related both by `e.is_image` and `e'.is_image`. To ensure that the new maps are
continuous on `source`/`target`, it also assumes that `e.source` and `e'.source` meet `frontier s`
on the same set and `e x = e' x` on this intersection. -/
@[simps (config := { fullyApplied := false }) toLocalEquiv apply]
def piecewise (e e' : LocalHomeomorph α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) : LocalHomeomorph α β
    where
  toLocalEquiv := e.toLocalEquiv.piecewise e'.toLocalEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
    e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq
  continuous_to_fun := continuous_on_piecewise_ite e.ContinuousOn e'.ContinuousOn Hs Heq
  continuous_inv_fun :=
    continuous_on_piecewise_ite e.continuous_on_symm e'.continuous_on_symm
      (H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq)
      (H.frontier.symm_eq_on_of_inter_eq_of_eq_on Hs Heq)
#align local_homeomorph.piecewise LocalHomeomorph.piecewise

@[simp]
theorem symm_piecewise (e e' : LocalHomeomorph α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source ∩ frontier s = e'.source ∩ frontier s)
    (Heq : EqOn e e' (e.source ∩ frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq)
        (H.frontier.symm_eq_on_of_inter_eq_of_eq_on Hs Heq) :=
  rfl
#align local_homeomorph.symm_piecewise LocalHomeomorph.symm_piecewise

/-- Combine two `local_homeomorph`s with disjoint sources and disjoint targets. We reuse
`local_homeomorph.piecewise` then override `to_local_equiv` to `local_equiv.disjoint_union`.
This way we have better definitional equalities for `source` and `target`. -/
def disjointUnion (e e' : LocalHomeomorph α β) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : LocalHomeomorph α β :=
  (e.piecewise e' e.source e.target e.is_image_source_target
        (e'.is_image_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eq_on_empty _ _)).replaceEquiv
    (e.toLocalEquiv.disjointUnion e'.toLocalEquiv Hs Ht)
    (LocalEquiv.disjoint_union_eq_piecewise _ _ _ _).symm
#align local_homeomorph.disjoint_union LocalHomeomorph.disjointUnion

end Piecewise

section Pi

variable {ι : Type _} [Fintype ι] {Xi Yi : ι → Type _} [∀ i, TopologicalSpace (Xi i)]
  [∀ i, TopologicalSpace (Yi i)] (ei : ∀ i, LocalHomeomorph (Xi i) (Yi i))

/-- The product of a finite family of `local_homeomorph`s. -/
@[simps toLocalEquiv]
def pi : LocalHomeomorph (∀ i, Xi i) (∀ i, Yi i)
    where
  toLocalEquiv := LocalEquiv.pi fun i => (ei i).toLocalEquiv
  open_source := (is_open_set_pi finite_univ) fun i hi => (ei i).open_source
  open_target := (is_open_set_pi finite_univ) fun i hi => (ei i).open_target
  continuous_to_fun :=
    continuous_on_pi.2 fun i =>
      (ei i).ContinuousOn.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivial
  continuous_inv_fun :=
    continuous_on_pi.2 fun i =>
      (ei i).continuous_on_symm.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivial
#align local_homeomorph.pi LocalHomeomorph.pi

end Pi

section Continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuous_within_at_iff_continuous_within_at_comp_right {f : β → γ} {s : Set β} {x : β}
    (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e,
    e.map_nhds_within_preimage_eq (e.map_target h), (· ∘ ·), e.right_inv h]
#align
  local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_right LocalHomeomorph.continuous_within_at_iff_continuous_within_at_comp_right

/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
theorem continuous_at_iff_continuous_at_comp_right {f : β → γ} {x : β} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuous_within_at_univ, e.continuous_within_at_iff_continuous_within_at_comp_right h,
    preimage_univ, continuous_within_at_univ]
#align
  local_homeomorph.continuous_at_iff_continuous_at_comp_right LocalHomeomorph.continuous_at_iff_continuous_at_comp_right

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuous_on_iff_continuous_on_comp_right {f : β → γ} {s : Set β} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) :=
  by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, ball_image_iff]
  refine' forall₂_congr fun x hx => _
  rw [e.continuous_within_at_iff_continuous_within_at_comp_right (h hx),
    e.symm_image_eq_source_inter_preimage h, inter_comm, continuous_within_at_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))
#align
  local_homeomorph.continuous_on_iff_continuous_on_comp_right LocalHomeomorph.continuous_on_iff_continuous_on_comp_right

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
theorem continuous_within_at_iff_continuous_within_at_comp_left {f : γ → α} {s : Set γ} {x : γ}
    (hx : f x ∈ e.source) (h : f ⁻¹' e.source ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x :=
  by
  refine' ⟨(e.continuous_at hx).comp_continuous_within_at, fun fe_cont => _⟩
  rw [← continuous_within_at_inter' h] at fe_cont⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    haveI : ContinuousWithinAt e.symm univ (e (f x)) :=
      (e.continuous_at_symm (e.map_source hx)).ContinuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact this.congr (fun y hy => by simp [e.left_inv hy.2]) (by simp [e.left_inv hx])
#align
  local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left LocalHomeomorph.continuous_within_at_iff_continuous_within_at_comp_left

/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
theorem continuous_at_iff_continuous_at_comp_left {f : γ → α} {x : γ} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x :=
  by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by rwa [nhds_within_univ]
  rw [← continuous_within_at_univ, ← continuous_within_at_univ,
    e.continuous_within_at_iff_continuous_within_at_comp_left hx h']
#align
  local_homeomorph.continuous_at_iff_continuous_at_comp_left LocalHomeomorph.continuous_at_iff_continuous_at_comp_left

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuous_on_iff_continuous_on_comp_left {f : γ → α} {s : Set γ} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congr fun x hx =>
    e.continuous_within_at_iff_continuous_within_at_comp_left (h hx)
      (mem_of_superset self_mem_nhds_within h)
#align
  local_homeomorph.continuous_on_iff_continuous_on_comp_left LocalHomeomorph.continuous_on_iff_continuous_on_comp_left

/-- A function is continuous if and only if its composition with a local homeomorphism
on the left is continuous and its image is contained in the source. -/
theorem continuous_iff_continuous_comp_left {f : γ → α} (h : f ⁻¹' e.source = univ) :
    Continuous f ↔ Continuous (e ∘ f) :=
  by
  simp only [continuous_iff_continuous_on_univ]
  exact e.continuous_on_iff_continuous_on_comp_left (Eq.symm h).Subset
#align
  local_homeomorph.continuous_iff_continuous_comp_left LocalHomeomorph.continuous_iff_continuous_comp_left

end Continuity

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
  continuous_to_fun :=
    (continuous_on_iff_continuous_restrict.mp (e.ContinuousOn.mono hs)).subtype_mk _
  continuous_inv_fun :=
    (continuous_on_iff_continuous_restrict.mp
          (e.continuous_on_symm.mono fun b hb =>
            let ⟨a, ha1, ha2⟩ := show b ∈ e '' s from ht.symm ▸ hb
            ha2 ▸ e.map_source (hs ha1))).subtype_mk
      _
#align
  local_homeomorph.homeomorph_of_image_subset_source LocalHomeomorph.homeomorphOfImageSubsetSource

/-- A local homeomrphism defines a homeomorphism between its source and target. -/
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target
#align local_homeomorph.to_homeomorph_source_target LocalHomeomorph.toHomeomorphSourceTarget

theorem second_countable_topology_source [SecondCountableTopology β] (e : LocalHomeomorph α β) :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.SecondCountableTopology
#align
  local_homeomorph.second_countable_topology_source LocalHomeomorph.second_countable_topology_source

/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps (config := mfld_cfg) apply symmApply]
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set α)) (h' : e.target = univ) :
    α ≃ₜ β where
  toFun := e
  invFun := e.symm
  left_inv x :=
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv x :=
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_to_fun := by
    rw [continuous_iff_continuous_on_univ]
    convert e.continuous_to_fun
    rw [h]
  continuous_inv_fun := by
    rw [continuous_iff_continuous_on_univ]
    convert e.continuous_inv_fun
    rw [h']
#align
  local_homeomorph.to_homeomorph_of_source_eq_univ_target_eq_univ LocalHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv

/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `open_embedding.to_local_homeomorph`. -/
theorem to_open_embedding (h : e.source = Set.univ) : OpenEmbedding e :=
  by
  apply open_embedding_of_continuous_injective_open
  · apply continuous_iff_continuous_on_univ.mpr
    rw [← h]
    exact e.continuous_to_fun
  · apply set.injective_iff_inj_on_univ.mpr
    rw [← h]
    exact e.inj_on
  · intro U hU
    simpa only [h, subset_univ, mfld_simps] using e.image_open_of_open hU
#align local_homeomorph.to_open_embedding LocalHomeomorph.to_open_embedding

end LocalHomeomorph

namespace Homeomorph

variable (e : α ≃ₜ β) (e' : β ≃ₜ γ)

/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/
@[simp, mfld_simps]
theorem refl_to_local_homeomorph : (Homeomorph.refl α).toLocalHomeomorph = LocalHomeomorph.refl α :=
  rfl
#align homeomorph.refl_to_local_homeomorph Homeomorph.refl_to_local_homeomorph

@[simp, mfld_simps]
theorem symm_to_local_homeomorph : e.symm.toLocalHomeomorph = e.toLocalHomeomorph.symm :=
  rfl
#align homeomorph.symm_to_local_homeomorph Homeomorph.symm_to_local_homeomorph

@[simp, mfld_simps]
theorem trans_to_local_homeomorph :
    (e.trans e').toLocalHomeomorph = e.toLocalHomeomorph.trans e'.toLocalHomeomorph :=
  LocalHomeomorph.eq_of_local_equiv_eq <| Equiv.trans_toLocalEquiv _ _
#align homeomorph.trans_to_local_homeomorph Homeomorph.trans_to_local_homeomorph

end Homeomorph

namespace OpenEmbedding

variable (f : α → β) (h : OpenEmbedding f)

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `local_homeomorph.to_open_embedding`. -/
@[simps (config := mfld_cfg) apply source target]
noncomputable def toLocalHomeomorph [Nonempty α] : LocalHomeomorph α β :=
  LocalHomeomorph.ofContinuousOpen ((h.toEmbedding.inj.InjOn univ).toLocalEquiv _ _)
    h.Continuous.ContinuousOn h.IsOpenMap is_open_univ
#align open_embedding.to_local_homeomorph OpenEmbedding.toLocalHomeomorph

theorem continuous_at_iff {f : α → β} {g : β → γ} (hf : OpenEmbedding f) {x : α} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  by
  haveI : Nonempty α := ⟨x⟩
  convert ((hf.to_local_homeomorph f).continuous_at_iff_continuous_at_comp_right _).symm
  · apply (LocalHomeomorph.left_inv _ _).symm
    simp
  · simp
#align open_embedding.continuous_at_iff OpenEmbedding.continuous_at_iff

end OpenEmbedding

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (s : Opens α) [Nonempty s]

/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
noncomputable def localHomeomorphSubtypeCoe : LocalHomeomorph s α :=
  OpenEmbedding.toLocalHomeomorph _ s.2.open_embedding_subtype_coe
#align
  topological_space.opens.local_homeomorph_subtype_coe TopologicalSpace.Opens.localHomeomorphSubtypeCoe

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_coe : (s.localHomeomorphSubtypeCoe : s → α) = coe :=
  rfl
#align
  topological_space.opens.local_homeomorph_subtype_coe_coe TopologicalSpace.Opens.local_homeomorph_subtype_coe_coe

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_source : s.localHomeomorphSubtypeCoe.source = Set.univ :=
  rfl
#align
  topological_space.opens.local_homeomorph_subtype_coe_source TopologicalSpace.Opens.local_homeomorph_subtype_coe_source

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_target : s.localHomeomorphSubtypeCoe.target = s :=
  by
  simp only [local_homeomorph_subtype_coe, Subtype.range_coe_subtype, mfld_simps]
  rfl
#align
  topological_space.opens.local_homeomorph_subtype_coe_target TopologicalSpace.Opens.local_homeomorph_subtype_coe_target

end TopologicalSpace.Opens

namespace LocalHomeomorph

open TopologicalSpace

variable (e : LocalHomeomorph α β)

variable (s : Opens α) [Nonempty s]

/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
noncomputable def subtypeRestr : LocalHomeomorph s β :=
  s.localHomeomorphSubtypeCoe.trans e
#align local_homeomorph.subtype_restr LocalHomeomorph.subtypeRestr

theorem subtype_restr_def : e.subtypeRestr s = s.localHomeomorphSubtypeCoe.trans e :=
  rfl
#align local_homeomorph.subtype_restr_def LocalHomeomorph.subtype_restr_def

@[simp, mfld_simps]
theorem subtype_restr_coe :
    ((e.subtypeRestr s : LocalHomeomorph s β) : s → β) = Set.restrict ↑s (e : α → β) :=
  rfl
#align local_homeomorph.subtype_restr_coe LocalHomeomorph.subtype_restr_coe

@[simp, mfld_simps]
theorem subtype_restr_source : (e.subtypeRestr s).source = coe ⁻¹' e.source := by
  simp only [subtype_restr_def, mfld_simps]
#align local_homeomorph.subtype_restr_source LocalHomeomorph.subtype_restr_source

/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
theorem subtype_restr_symm_trans_subtype_restr (f f' : LocalHomeomorph α β) :
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
#align
  local_homeomorph.subtype_restr_symm_trans_subtype_restr LocalHomeomorph.subtype_restr_symm_trans_subtype_restr

end LocalHomeomorph

