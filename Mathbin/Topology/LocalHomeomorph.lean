import Mathbin.Data.Equiv.LocalEquiv
import Mathbin.Topology.Opens

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

open topological_space (SecondCountableTopology)

open_locale TopologicalSpace

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} [TopologicalSpace α] [TopologicalSpace β]
  [TopologicalSpace γ] [TopologicalSpace δ]

/-- local homeomorphisms, defined on open subsets of the space -/
@[nolint has_inhabited_instance]
structure LocalHomeomorph (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] extends
  LocalEquiv α β where
  open_source : IsOpen source
  open_target : IsOpen target
  continuous_to_fun : ContinuousOn to_fun source
  continuous_inv_fun : ContinuousOn inv_fun target

/-- A homeomorphism induces a local homeomorphism on the whole space -/
def Homeomorph.toLocalHomeomorph (e : α ≃ₜ β) : LocalHomeomorph α β :=
  { e.to_equiv.to_local_equiv with open_source := is_open_univ, open_target := is_open_univ,
    continuous_to_fun := by
      erw [← continuous_iff_continuous_on_univ]
      exact e.continuous_to_fun,
    continuous_inv_fun := by
      erw [← continuous_iff_continuous_on_univ]
      exact e.continuous_inv_fun }

namespace LocalHomeomorph

variable (e : LocalHomeomorph α β) (e' : LocalHomeomorph β γ)

instance : CoeFun (LocalHomeomorph α β) fun _ => α → β :=
  ⟨fun e => e.to_fun⟩

/-- The inverse of a local homeomorphism -/
protected def symm : LocalHomeomorph β α :=
  { e.to_local_equiv.symm with open_source := e.open_target, open_target := e.open_source,
    continuous_to_fun := e.continuous_inv_fun, continuous_inv_fun := e.continuous_to_fun }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (e : LocalHomeomorph α β) : α → β :=
  e

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : LocalHomeomorph α β) : β → α :=
  e.symm

initialize_simps_projections LocalHomeomorph (to_local_equiv_to_fun → apply, to_local_equiv_inv_fun → symmApply,
  to_local_equiv_source → Source, to_local_equiv_target → Target, -toLocalEquiv)

protected theorem ContinuousOn : ContinuousOn e e.source :=
  e.continuous_to_fun

theorem continuous_on_symm : ContinuousOn e.symm e.target :=
  e.continuous_inv_fun

@[simp, mfld_simps]
theorem mk_coe (e : LocalEquiv α β) a b c d : (LocalHomeomorph.mk e a b c d : α → β) = e :=
  rfl

@[simp, mfld_simps]
theorem mk_coe_symm (e : LocalEquiv α β) a b c d : ((LocalHomeomorph.mk e a b c d).symm : β → α) = e.symm :=
  rfl

@[simp, mfld_simps]
theorem to_fun_eq_coe (e : LocalHomeomorph α β) : e.to_fun = e :=
  rfl

@[simp, mfld_simps]
theorem inv_fun_eq_coe (e : LocalHomeomorph α β) : e.inv_fun = e.symm :=
  rfl

@[simp, mfld_simps]
theorem coe_coe : (e.to_local_equiv : α → β) = e :=
  rfl

@[simp, mfld_simps]
theorem coe_coe_symm : (e.to_local_equiv.symm : β → α) = e.symm :=
  rfl

@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h

@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h

@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h

protected theorem maps_to : maps_to e e.source e.target := fun x => e.map_source

protected theorem symm_maps_to : maps_to e.symm e.target e.source :=
  e.symm.maps_to

protected theorem left_inv_on : left_inv_on e.symm e e.source := fun x => e.left_inv

protected theorem right_inv_on : right_inv_on e.symm e e.target := fun x => e.right_inv

protected theorem inv_on : inv_on e.symm e e.source e.target :=
  ⟨e.left_inv_on, e.right_inv_on⟩

protected theorem inj_on : inj_on e e.source :=
  e.left_inv_on.inj_on

protected theorem bij_on : bij_on e e.source e.target :=
  e.inv_on.bij_on e.maps_to e.symm_maps_to

protected theorem surj_on : surj_on e e.source e.target :=
  e.bij_on.surj_on

/-- Replace `to_local_equiv` field to provide better definitional equalities. -/
def replace_equiv (e : LocalHomeomorph α β) (e' : LocalEquiv α β) (h : e.to_local_equiv = e') :
    LocalHomeomorph α β where
  toLocalEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuous_to_fun := h ▸ e.continuous_to_fun
  continuous_inv_fun := h ▸ e.continuous_inv_fun

theorem replace_equiv_eq_self (e : LocalHomeomorph α β) (e' : LocalEquiv α β) (h : e.to_local_equiv = e') :
    e.replace_equiv e' h = e := by
  cases e
  subst e'
  rfl

theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.maps_to

theorem eq_of_local_equiv_eq {e e' : LocalHomeomorph α β} (h : e.to_local_equiv = e'.to_local_equiv) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

theorem eventually_left_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) : ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'

theorem eventually_left_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)

theorem eventually_right_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.target) : ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'

theorem eventually_right_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)

theorem eventually_ne_nhds_within (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) : ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhds_within_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by
        rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']

theorem nhds_within_source_inter {x} (hx : x ∈ e.source) (s : Set α) : 𝓝[e.source ∩ s] x = 𝓝[s] x :=
  nhds_within_inter_of_mem (mem_nhds_within_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)

theorem nhds_within_target_inter {x} (hx : x ∈ e.target) (s : Set β) : 𝓝[e.target ∩ s] x = 𝓝[s] x :=
  e.symm.nhds_within_source_inter hx s

theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) : e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.to_local_equiv.image_eq_target_inter_inv_preimage h

theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.to_local_equiv.image_source_inter_eq' s

theorem image_source_inter_eq (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.to_local_equiv.image_source_inter_eq s

theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) : e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

theorem symm_image_target_inter_eq (s : Set β) : e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _

theorem source_inter_preimage_inv_preimage (s : Set α) : e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.to_local_equiv.source_inter_preimage_inv_preimage s

theorem target_inter_inv_preimage_preimage (s : Set β) : e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _

theorem source_inter_preimage_target_inter (s : Set β) : e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.to_local_equiv.source_inter_preimage_target_inter s

/-- Two local homeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected theorem ext (e' : LocalHomeomorph α β) (h : ∀ x, e x = e' x) (hinv : ∀ x, e.symm x = e'.symm x)
    (hs : e.source = e'.source) : e = e' :=
  eq_of_local_equiv_eq (LocalEquiv.ext h hinv hs)

@[simp, mfld_simps]
theorem symm_to_local_equiv : e.symm.to_local_equiv = e.to_local_equiv.symm :=
  rfl

theorem symm_source : e.symm.source = e.target :=
  rfl

theorem symm_target : e.symm.target = e.source :=
  rfl

@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e :=
  eq_of_local_equiv_eq <| by
    simp

/-- A local homeomorphism is continuous at any point of its source -/
protected theorem ContinuousAt {x : α} (h : x ∈ e.source) : ContinuousAt e x :=
  (e.continuous_on x h).ContinuousAt (IsOpen.mem_nhds e.open_source h)

/-- A local homeomorphism inverse is continuous at any point of its target -/
theorem continuous_at_symm {x : β} (h : x ∈ e.target) : ContinuousAt e.symm x :=
  e.symm.continuous_at h

theorem tendsto_symm {x} (hx : x ∈ e.source) : tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [ContinuousAt, e.left_inv hx] using e.continuous_at_symm (e.map_source hx)

theorem map_nhds_eq {x} (hx : x ∈ e.source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymmₓ (e.continuous_at hx) <| le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)

theorem symm_map_nhds_eq {x} (hx : x ∈ e.source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by
    rw [e.left_inv hx]

theorem image_mem_nhds {x} (hx : x ∈ e.source) {s : Set α} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs

theorem map_nhds_within_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set α) :
    map e (𝓝[s] x) = 𝓝[e '' (e.source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.source ∩ s] x) := congr_argₓ (map e) (e.nhds_within_source_inter hx _).symm
    _ = 𝓝[e '' (e.source ∩ s)] e x :=
      (e.left_inv_on.mono <| inter_subset_left _ _).map_nhds_within_eq (e.left_inv hx)
        (e.continuous_at_symm (e.map_source hx)).ContinuousWithinAt (e.continuous_at hx).ContinuousWithinAt
    

theorem map_nhds_within_preimage_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.source) (s : Set β) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhds_within_target_inter (e.map_source hx)]

theorem preimage_open_of_open {s : Set β} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.continuous_on.preimage_open_of_open e.open_source hs

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
def is_image (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

theorem to_local_equiv (h : e.is_image s t) : e.to_local_equiv.is_image s t :=
  h

theorem apply_mem_iff (h : e.is_image s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx

protected theorem symm (h : e.is_image s t) : e.symm.is_image t s :=
  h.to_local_equiv.symm

theorem symm_apply_mem_iff (h : e.is_image s t) (hy : y ∈ e.target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy

@[simp]
theorem symm_iff : e.symm.is_image t s ↔ e.is_image s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

protected theorem maps_to (h : e.is_image s t) : maps_to e (e.source ∩ s) (e.target ∩ t) :=
  h.to_local_equiv.maps_to

theorem symm_maps_to (h : e.is_image s t) : maps_to e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.maps_to

theorem image_eq (h : e.is_image s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.to_local_equiv.image_eq

theorem symm_image_eq (h : e.is_image s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq

theorem iff_preimage_eq : e.is_image s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s :=
  LocalEquiv.IsImage.iff_preimage_eq

alias iff_preimage_eq ↔ LocalHomeomorph.IsImage.preimage_eq LocalHomeomorph.IsImage.of_preimage_eq

theorem iff_symm_preimage_eq : e.is_image s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias iff_symm_preimage_eq ↔ LocalHomeomorph.IsImage.symm_preimage_eq LocalHomeomorph.IsImage.of_symm_preimage_eq

theorem iff_symm_preimage_eq' : e.is_image s t ↔ e.target ∩ e.symm ⁻¹' (e.source ∩ s) = e.target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']

alias iff_symm_preimage_eq' ↔ LocalHomeomorph.IsImage.symm_preimage_eq' LocalHomeomorph.IsImage.of_symm_preimage_eq'

theorem iff_preimage_eq' : e.is_image s t ↔ e.source ∩ e ⁻¹' (e.target ∩ t) = e.source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'

alias iff_preimage_eq' ↔ LocalHomeomorph.IsImage.preimage_eq' LocalHomeomorph.IsImage.of_preimage_eq'

theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.is_image s t :=
  LocalEquiv.IsImage.of_image_eq h

theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.is_image s t :=
  LocalEquiv.IsImage.of_symm_image_eq h

protected theorem compl (h : e.is_image s t) : e.is_image (sᶜ) (tᶜ) := fun x hx => not_congr (h hx)

protected theorem inter {s' t'} (h : e.is_image s t) (h' : e.is_image s' t') : e.is_image (s ∩ s') (t ∩ t') :=
  fun x hx => and_congr (h hx) (h' hx)

protected theorem union {s' t'} (h : e.is_image s t) (h' : e.is_image s' t') : e.is_image (s ∪ s') (t ∪ t') :=
  fun x hx => or_congr (h hx) (h' hx)

protected theorem diff {s' t'} (h : e.is_image s t) (h' : e.is_image s' t') : e.is_image (s \ s') (t \ t') :=
  h.inter h'.compl

theorem left_inv_on_piecewise {e' : LocalHomeomorph α β} [∀ i, Decidable (i ∈ s)] [∀ i, Decidable (i ∈ t)]
    (h : e.is_image s t) (h' : e'.is_image s t) :
    left_inv_on (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) :=
  h.to_local_equiv.left_inv_on_piecewise h'

theorem inter_eq_of_inter_eq_of_eq_on {e' : LocalHomeomorph α β} (h : e.is_image s t) (h' : e'.is_image s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : eq_on e e' (e.source ∩ s)) : e.target ∩ t = e'.target ∩ t :=
  h.to_local_equiv.inter_eq_of_inter_eq_of_eq_on h' hs Heq

theorem symm_eq_on_of_inter_eq_of_eq_on {e' : LocalHomeomorph α β} (h : e.is_image s t)
    (hs : e.source ∩ s = e'.source ∩ s) (Heq : eq_on e e' (e.source ∩ s)) : eq_on e.symm e'.symm (e.target ∩ t) :=
  h.to_local_equiv.symm_eq_on_of_inter_eq_of_eq_on hs Heq

theorem map_nhds_within_eq (h : e.is_image s t) (hx : x ∈ e.source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhds_within_eq hx, h.image_eq, e.nhds_within_target_inter (e.map_source hx)]

protected theorem Closure (h : e.is_image s t) : e.is_image (Closure s) (Closure t) := fun x hx => by
  simp only [mem_closure_iff_nhds_within_ne_bot, ← h.map_nhds_within_eq hx, map_ne_bot_iff]

protected theorem Interior (h : e.is_image s t) : e.is_image (Interior s) (Interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl

protected theorem Frontier (h : e.is_image s t) : e.is_image (Frontier s) (Frontier t) :=
  h.closure.diff h.interior

theorem is_open_iff (h : e.is_image s t) : IsOpen (e.source ∩ s) ↔ IsOpen (e.target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.preimage_open_of_open hs, fun hs =>
    h.preimage_eq' ▸ e.preimage_open_of_open hs⟩

/-- Restrict a `local_homeomorph` to a pair of corresponding open sets. -/
@[simps toLocalEquiv]
def restr (h : e.is_image s t) (hs : IsOpen (e.source ∩ s)) : LocalHomeomorph α β where
  toLocalEquiv := h.to_local_equiv.restr
  open_source := hs
  open_target := h.is_open_iff.1 hs
  continuous_to_fun := e.continuous_on.mono (inter_subset_left _ _)
  continuous_inv_fun := e.symm.continuous_on.mono (inter_subset_left _ _)

end IsImage

theorem is_image_source_target : e.is_image e.source e.target :=
  e.to_local_equiv.is_image_source_target

theorem is_image_source_target_of_disjoint (e' : LocalHomeomorph α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) : e.is_image e'.source e'.target :=
  e.to_local_equiv.is_image_source_target_of_disjoint e'.to_local_equiv hs ht

/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
theorem preimage_interior (s : Set β) : e.source ∩ e ⁻¹' Interior s = e.source ∩ Interior (e ⁻¹' s) :=
  (is_image.of_preimage_eq rfl).Interior.preimage_eq

theorem preimage_closure (s : Set β) : e.source ∩ e ⁻¹' Closure s = e.source ∩ Closure (e ⁻¹' s) :=
  (is_image.of_preimage_eq rfl).closure.preimage_eq

theorem preimage_frontier (s : Set β) : e.source ∩ e ⁻¹' Frontier s = e.source ∩ Frontier (e ⁻¹' s) :=
  (is_image.of_preimage_eq rfl).Frontier.preimage_eq

theorem preimage_open_of_open_symm {s : Set α} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.continuous_on.preimage_open_of_open e.open_target hs

/-- The image of an open set in the source is open. -/
theorem image_open_of_open {s : Set α} (hs : IsOpen s) (h : s ⊆ e.source) : IsOpen (e '' s) := by
  have : e '' s = e.target ∩ e.symm ⁻¹' s := e.to_local_equiv.image_eq_target_inter_inv_preimage h
  rw [this]
  exact e.continuous_on_symm.preimage_open_of_open e.open_target hs

/-- The image of the restriction of an open set to the source is open. -/
theorem image_open_of_open' {s : Set α} (hs : IsOpen s) : IsOpen (e '' (e.source ∩ s)) :=
  image_open_of_open _ (IsOpen.inter e.open_source hs) (inter_subset_left _ _)

/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def of_continuous_open_restrict (e : LocalEquiv α β) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : LocalHomeomorph α β where
  toLocalEquiv := e
  open_source := hs
  open_target := by
    simpa only [range_restrict, e.image_source_eq_target] using ho.is_open_range
  continuous_to_fun := hc
  continuous_inv_fun := e.image_source_eq_target ▸ ho.continuous_on_image_of_left_inv_on e.left_inv_on

/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def of_continuous_open (e : LocalEquiv α β) (hc : ContinuousOn e e.source) (ho : IsOpenMap e) (hs : IsOpen e.source) :
    LocalHomeomorph α β :=
  of_continuous_open_restrict e hc (ho.restrict hs) hs

/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restr_open (s : Set α) (hs : IsOpen s) : LocalHomeomorph α β :=
  (@is_image.of_symm_preimage_eq α β _ _ e s (e.symm ⁻¹' s) rfl).restr (IsOpen.inter e.open_source hs)

@[simp, mfld_simps]
theorem restr_open_to_local_equiv (s : Set α) (hs : IsOpen s) :
    (e.restr_open s hs).toLocalEquiv = e.to_local_equiv.restr s :=
  rfl

theorem restr_open_source (s : Set α) (hs : IsOpen s) : (e.restr_open s hs).Source = e.source ∩ s :=
  rfl

/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
@[simps (config := mfldCfg) apply symmApply, simps (config := { attrs := [] }) Source Target]
protected def restr (s : Set α) : LocalHomeomorph α β :=
  e.restr_open (Interior s) is_open_interior

@[simp, mfld_simps]
theorem restr_to_local_equiv (s : Set α) : (e.restr s).toLocalEquiv = e.to_local_equiv.restr (Interior s) :=
  rfl

theorem restr_source' (s : Set α) (hs : IsOpen s) : (e.restr s).Source = e.source ∩ s := by
  rw [e.restr_source, hs.interior_eq]

theorem restr_to_local_equiv' (s : Set α) (hs : IsOpen s) : (e.restr s).toLocalEquiv = e.to_local_equiv.restr s := by
  rw [e.restr_to_local_equiv, hs.interior_eq]

theorem restr_eq_of_source_subset {e : LocalHomeomorph α β} {s : Set α} (h : e.source ⊆ s) : e.restr s = e := by
  apply eq_of_local_equiv_eq
  rw [restr_to_local_equiv]
  apply LocalEquiv.restr_eq_of_source_subset
  exact interior_maximal h e.open_source

@[simp, mfld_simps]
theorem restr_univ {e : LocalHomeomorph α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)

theorem restr_source_inter (s : Set α) : e.restr (e.source ∩ s) = e.restr s := by
  refine' LocalHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) _
  simp [e.open_source.interior_eq, ← inter_assoc]

/-- The identity on the whole space as a local homeomorphism. -/
@[simps (config := mfldCfg) apply, simps (config := { attrs := [] }) Source Target]
protected def refl (α : Type _) [TopologicalSpace α] : LocalHomeomorph α α :=
  (Homeomorph.refl α).toLocalHomeomorph

@[simp, mfld_simps]
theorem refl_local_equiv : (LocalHomeomorph.refl α).toLocalEquiv = LocalEquiv.refl α :=
  rfl

@[simp, mfld_simps]
theorem refl_symm : (LocalHomeomorph.refl α).symm = LocalHomeomorph.refl α :=
  rfl

section

variable {s : Set α} (hs : IsOpen s)

/-- The identity local equiv on a set `s` -/
@[simps (config := mfldCfg) apply, simps (config := { attrs := [] }) Source Target]
def of_set (s : Set α) (hs : IsOpen s) : LocalHomeomorph α α :=
  { LocalEquiv.ofSet s with open_source := hs, open_target := hs, continuous_to_fun := continuous_id.ContinuousOn,
    continuous_inv_fun := continuous_id.ContinuousOn }

@[simp, mfld_simps]
theorem of_set_to_local_equiv : (of_set s hs).toLocalEquiv = LocalEquiv.ofSet s :=
  rfl

@[simp, mfld_simps]
theorem of_set_symm : (of_set s hs).symm = of_set s hs :=
  rfl

@[simp, mfld_simps]
theorem of_set_univ_eq_refl : of_set univ is_open_univ = LocalHomeomorph.refl α := by
  ext <;> simp

end

/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.target = e'.source) : LocalHomeomorph α γ :=
  { LocalEquiv.trans' e.to_local_equiv e'.to_local_equiv h with open_source := e.open_source,
    open_target := e'.open_target,
    continuous_to_fun := by
      apply ContinuousOn.comp e'.continuous_to_fun e.continuous_to_fun
      rw [← h]
      exact e.to_local_equiv.source_subset_preimage_target,
    continuous_inv_fun := by
      apply ContinuousOn.comp e.continuous_inv_fun e'.continuous_inv_fun
      rw [h]
      exact e'.to_local_equiv.target_subset_preimage_source }

/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : LocalHomeomorph α γ :=
  LocalHomeomorph.trans' (e.symm.restr_open e'.source e'.open_source).symm (e'.restr_open e.target e.open_target)
    (by
      simp [inter_comm])

@[simp, mfld_simps]
theorem trans_to_local_equiv : (e.trans e').toLocalEquiv = e.to_local_equiv.trans e'.to_local_equiv :=
  rfl

@[simp, mfld_simps]
theorem coeTransₓ : (e.trans e' : α → γ) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := by
  cases e <;> cases e' <;> rfl

theorem trans_source : (e.trans e').Source = e.source ∩ e ⁻¹' e'.source :=
  LocalEquiv.trans_source e.to_local_equiv e'.to_local_equiv

theorem trans_source' : (e.trans e').Source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) :=
  LocalEquiv.trans_source' e.to_local_equiv e'.to_local_equiv

theorem trans_source'' : (e.trans e').Source = e.symm '' (e.target ∩ e'.source) :=
  LocalEquiv.trans_source'' e.to_local_equiv e'.to_local_equiv

theorem image_trans_source : e '' (e.trans e').Source = e.target ∩ e'.source :=
  LocalEquiv.image_trans_source e.to_local_equiv e'.to_local_equiv

theorem trans_target : (e.trans e').Target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl

theorem trans_target' : (e.trans e').Target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm

theorem trans_target'' : (e.trans e').Target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm

theorem inv_image_trans_target : e'.symm '' (e.trans e').Target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm

theorem trans_assoc (e'' : LocalHomeomorph γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  eq_of_local_equiv_eq <| LocalEquiv.trans_assoc e.to_local_equiv e'.to_local_equiv e''.to_local_equiv

@[simp, mfld_simps]
theorem trans_refl : e.trans (LocalHomeomorph.refl β) = e :=
  eq_of_local_equiv_eq <| LocalEquiv.trans_refl e.to_local_equiv

@[simp, mfld_simps]
theorem refl_trans : (LocalHomeomorph.refl α).trans e = e :=
  eq_of_local_equiv_eq <| LocalEquiv.refl_trans e.to_local_equiv

theorem trans_of_set {s : Set β} (hs : IsOpen s) : e.trans (of_set s hs) = e.restr (e ⁻¹' s) :=
  (LocalHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [LocalEquiv.trans_source, (e.preimage_interior _).symm, hs.interior_eq]

theorem trans_of_set' {s : Set β} (hs : IsOpen s) : e.trans (of_set s hs) = e.restr (e.source ∩ e ⁻¹' s) := by
  rw [trans_of_set, restr_source_inter]

theorem of_set_trans {s : Set α} (hs : IsOpen s) : (of_set s hs).trans e = e.restr s :=
  (LocalHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [LocalEquiv.trans_source, hs.interior_eq, inter_comm]

theorem of_set_trans' {s : Set α} (hs : IsOpen s) : (of_set s hs).trans e = e.restr (e.source ∩ s) := by
  rw [of_set_trans, restr_source_inter]

@[simp, mfld_simps]
theorem of_set_trans_of_set {s : Set α} (hs : IsOpen s) {s' : Set α} (hs' : IsOpen s') :
    (of_set s hs).trans (of_set s' hs') = of_set (s ∩ s') (IsOpen.inter hs hs') := by
  rw [(of_set s hs).trans_of_set hs']
  ext <;> simp [hs'.interior_eq]

theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  eq_of_local_equiv_eq <| LocalEquiv.restr_trans e.to_local_equiv e'.to_local_equiv (Interior s)

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def eq_on_source (e e' : LocalHomeomorph α β) : Prop :=
  e.source = e'.source ∧ eq_on e e' e.source

theorem eq_on_source_iff (e e' : LocalHomeomorph α β) :
    eq_on_source e e' ↔ LocalEquiv.EqOnSource e.to_local_equiv e'.to_local_equiv :=
  Iff.rfl

/-- `eq_on_source` is an equivalence relation -/
instance : Setoidₓ (LocalHomeomorph α β) where
  R := eq_on_source
  iseqv :=
    ⟨fun e => (@LocalEquiv.eqOnSourceSetoid α β).iseqv.1 e.to_local_equiv, fun e e' h =>
      (@LocalEquiv.eqOnSourceSetoid α β).iseqv.2.1 ((eq_on_source_iff e e').1 h), fun e e' e'' h h' =>
      (@LocalEquiv.eqOnSourceSetoid α β).iseqv.2.2 ((eq_on_source_iff e e').1 h) ((eq_on_source_iff e' e'').1 h')⟩

theorem eq_on_source_refl : e ≈ e :=
  Setoidₓ.refl _

/-- If two local homeomorphisms are equivalent, so are their inverses -/
theorem eq_on_source.symm' {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
  LocalEquiv.EqOnSource.symm' h

/-- Two equivalent local homeomorphisms have the same source -/
theorem eq_on_source.source_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.source = e'.source :=
  h.1

/-- Two equivalent local homeomorphisms have the same target -/
theorem eq_on_source.target_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.target = e'.target :=
  h.symm'.1

/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
theorem eq_on_source.eq_on {e e' : LocalHomeomorph α β} (h : e ≈ e') : eq_on e e' e.source :=
  h.2

/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
theorem eq_on_source.symm_eq_on_target {e e' : LocalHomeomorph α β} (h : e ≈ e') : eq_on e.symm e'.symm e.target :=
  h.symm'.2

/-- Composition of local homeomorphisms respects equivalence -/
theorem eq_on_source.trans' {e e' : LocalHomeomorph α β} {f f' : LocalHomeomorph β γ} (he : e ≈ e') (hf : f ≈ f') :
    e.trans f ≈ e'.trans f' :=
  LocalEquiv.EqOnSource.trans' he hf

/-- Restriction of local homeomorphisms respects equivalence -/
theorem eq_on_source.restr {e e' : LocalHomeomorph α β} (he : e ≈ e') (s : Set α) : e.restr s ≈ e'.restr s :=
  LocalEquiv.EqOnSource.restr he _

/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem trans_self_symm : e.trans e.symm ≈ LocalHomeomorph.ofSet e.source e.open_source :=
  LocalEquiv.trans_self_symm _

theorem trans_symm_self : e.symm.trans e ≈ LocalHomeomorph.ofSet e.target e.open_target :=
  e.symm.trans_self_symm

theorem eq_of_eq_on_source_univ {e e' : LocalHomeomorph α β} (h : e ≈ e') (s : e.source = univ) (t : e.target = univ) :
    e = e' :=
  eq_of_local_equiv_eq <| LocalEquiv.eq_of_eq_on_source_univ _ _ h s t

section Prod

/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
@[simps (config := mfldCfg) toLocalEquiv apply, simps (config := { attrs := [] }) Source Target symmApply]
def Prod (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) : LocalHomeomorph (α × γ) (β × δ) where
  open_source := e.open_source.prod e'.open_source
  open_target := e.open_target.prod e'.open_target
  continuous_to_fun := e.continuous_on.prod_map e'.continuous_on
  continuous_inv_fun := e.continuous_on_symm.prod_map e'.continuous_on_symm
  toLocalEquiv := e.to_local_equiv.prod e'.to_local_equiv

@[simp, mfld_simps]
theorem prod_symm (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) : (e.prod e').symm = e.symm.prod e'.symm :=
  rfl

@[simp, mfld_simps]
theorem prod_trans {η : Type _} {ε : Type _} [TopologicalSpace η] [TopologicalSpace ε] (e : LocalHomeomorph α β)
    (f : LocalHomeomorph β γ) (e' : LocalHomeomorph δ η) (f' : LocalHomeomorph η ε) :
    (e.prod e').trans (f.prod f') = (e.trans f).Prod (e'.trans f') :=
  LocalHomeomorph.eq_of_local_equiv_eq <| by
    dsimp only [trans_to_local_equiv, prod_to_local_equiv] <;> apply LocalEquiv.prod_trans

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
@[simps (config := { fullyApplied := ff }) toLocalEquiv apply]
def piecewise (e e' : LocalHomeomorph α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)]
    (H : e.is_image s t) (H' : e'.is_image s t) (Hs : e.source ∩ Frontier s = e'.source ∩ Frontier s)
    (Heq : eq_on e e' (e.source ∩ Frontier s)) : LocalHomeomorph α β where
  toLocalEquiv := e.to_local_equiv.piecewise e'.to_local_equiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target := e.open_target.ite e'.open_target <| H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq
  continuous_to_fun := continuous_on_piecewise_ite e.continuous_on e'.continuous_on Hs Heq
  continuous_inv_fun :=
    continuous_on_piecewise_ite e.continuous_on_symm e'.continuous_on_symm
      (H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq) (H.frontier.symm_eq_on_of_inter_eq_of_eq_on Hs Heq)

@[simp]
theorem symm_piecewise (e e' : LocalHomeomorph α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.is_image s t) (H' : e'.is_image s t)
    (Hs : e.source ∩ Frontier s = e'.source ∩ Frontier s) (Heq : eq_on e e' (e.source ∩ Frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm (H.frontier.inter_eq_of_inter_eq_of_eq_on H'.frontier Hs Heq)
        (H.frontier.symm_eq_on_of_inter_eq_of_eq_on Hs Heq) :=
  rfl

/-- Combine two `local_homeomorph`s with disjoint sources and disjoint targets. We reuse
`local_homeomorph.piecewise` then override `to_local_equiv` to `local_equiv.disjoint_union`.
This way we have better definitional equalities for `source` and `target`. -/
def disjoint_union (e e' : LocalHomeomorph α β) [∀ x, Decidable (x ∈ e.source)] [∀ y, Decidable (y ∈ e.target)]
    (Hs : Disjoint e.source e'.source) (Ht : Disjoint e.target e'.target) : LocalHomeomorph α β :=
  (e.piecewise e' e.source e.target e.is_image_source_target (e'.is_image_source_target_of_disjoint e Hs.symm Ht.symm)
        (by
          rw [e.open_source.inter_frontier_eq, e'.open_source.inter_frontier_eq_empty_of_disjoint Hs])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eq_on_empty _ _)).replaceEquiv
    (e.to_local_equiv.disjoint_union e'.to_local_equiv Hs Ht) (LocalEquiv.disjoint_union_eq_piecewise _ _ _ _).symm

end Piecewise

section Pi

variable {ι : Type _} [Fintype ι] {Xi Yi : ι → Type _} [∀ i, TopologicalSpace (Xi i)] [∀ i, TopologicalSpace (Yi i)]
  (ei : ∀ i, LocalHomeomorph (Xi i) (Yi i))

/-- The product of a finite family of `local_homeomorph`s. -/
@[simps toLocalEquiv]
def pi : LocalHomeomorph (∀ i, Xi i) (∀ i, Yi i) where
  toLocalEquiv := LocalEquiv.pi fun i => (ei i).toLocalEquiv
  open_source := (is_open_set_pi finite_univ) fun i hi => (ei i).open_source
  open_target := (is_open_set_pi finite_univ) fun i hi => (ei i).open_target
  continuous_to_fun :=
    continuous_on_pi.2 fun i => (ei i).ContinuousOn.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivialₓ
  continuous_inv_fun :=
    continuous_on_pi.2 fun i =>
      (ei i).continuous_on_symm.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivialₓ

end Pi

section Continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuous_within_at_iff_continuous_within_at_comp_right {f : β → γ} {s : Set β} {x : β} (h : x ∈ e.target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e, e.map_nhds_within_preimage_eq (e.map_target h), · ∘ ·,
    e.right_inv h]

/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
theorem continuous_at_iff_continuous_at_comp_right {f : β → γ} {x : β} (h : x ∈ e.target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuous_within_at_univ, e.continuous_within_at_iff_continuous_within_at_comp_right h, preimage_univ,
    continuous_within_at_univ]

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuous_on_iff_continuous_on_comp_right {f : β → γ} {s : Set β} (h : s ⊆ e.target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.source ∩ e ⁻¹' s) := by
  simp only [← e.symm_image_eq_source_inter_preimage h, ContinuousOn, ball_image_iff]
  refine' forall₂_congrₓ fun x hx => _
  rw [e.continuous_within_at_iff_continuous_within_at_comp_right (h hx), e.symm_image_eq_source_inter_preimage h,
    inter_comm, continuous_within_at_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
theorem continuous_within_at_iff_continuous_within_at_comp_left {f : γ → α} {s : Set γ} {x : γ} (hx : f x ∈ e.source)
    (h : f ⁻¹' e.source ∈ 𝓝[s] x) : ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x := by
  refine' ⟨(e.continuous_at hx).Tendsto.comp, fun fe_cont => _⟩
  rw [← continuous_within_at_inter' h] at fe_cont⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x :=
    have : ContinuousWithinAt e.symm univ (e (f x)) := (e.continuous_at_symm (e.map_source hx)).ContinuousWithinAt
    ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact
    this.congr
      (fun y hy => by
        simp [e.left_inv hy.2])
      (by
        simp [e.left_inv hx])

/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
theorem continuous_at_iff_continuous_at_comp_left {f : γ → α} {x : γ} (h : f ⁻¹' e.source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x := by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by
    rwa [nhds_within_univ]
  rw [← continuous_within_at_univ, ← continuous_within_at_univ,
    e.continuous_within_at_iff_continuous_within_at_comp_left hx h']

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuous_on_iff_continuous_on_comp_left {f : γ → α} {s : Set γ} (h : s ⊆ f ⁻¹' e.source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congrₓ fun x hx =>
    e.continuous_within_at_iff_continuous_within_at_comp_left (h hx) (mem_of_superset self_mem_nhds_within h)

end Continuity

/-- A local homeomrphism defines a homeomorphism between its source and target. -/
def to_homeomorph_source_target : e.source ≃ₜ e.target where
  toFun := e.maps_to.restrict _ _ _
  invFun := e.symm_maps_to.restrict _ _ _
  left_inv := fun x => Subtype.eq <| e.left_inv x.2
  right_inv := fun x => Subtype.eq <| e.right_inv x.2
  continuous_to_fun := continuous_subtype_mk _ <| continuous_on_iff_continuous_restrict.1 e.continuous_on
  continuous_inv_fun := continuous_subtype_mk _ <| continuous_on_iff_continuous_restrict.1 e.symm.continuous_on

theorem second_countable_topology_source [second_countable_topology β] (e : LocalHomeomorph α β) :
    second_countable_topology e.source :=
  e.to_homeomorph_source_target.second_countable_topology

/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps (config := mfldCfg) apply symmApply]
def to_homeomorph_of_source_eq_univ_target_eq_univ (h : e.source = (univ : Set α)) (h' : e.target = univ) : α ≃ₜ β where
  toFun := e
  invFun := e.symm
  left_inv := fun x =>
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv := fun x =>
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

/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `open_embedding.to_local_homeomorph`. -/
theorem to_open_embedding (h : e.source = Set.Univ) : OpenEmbedding e := by
  apply open_embedding_of_continuous_injective_open
  · apply continuous_iff_continuous_on_univ.mpr
    rw [← h]
    exact e.continuous_to_fun
    
  · apply set.injective_iff_inj_on_univ.mpr
    rw [← h]
    exact e.inj_on
    
  · intro U hU
    simpa only [h, subset_univ] with mfld_simps using e.image_open_of_open hU
    

end LocalHomeomorph

namespace Homeomorph

variable (e : α ≃ₜ β) (e' : β ≃ₜ γ)

attribute [simps (config := { mfldCfg with simpRhs := tt }) apply Source Target] to_local_homeomorph

@[simp, mfld_simps]
theorem to_local_homeomorph_coe_symm : (e.to_local_homeomorph.symm : β → α) = e.symm :=
  rfl

@[simp, mfld_simps]
theorem refl_to_local_homeomorph : (Homeomorph.refl α).toLocalHomeomorph = LocalHomeomorph.refl α :=
  rfl

@[simp, mfld_simps]
theorem symm_to_local_homeomorph : e.symm.to_local_homeomorph = e.to_local_homeomorph.symm :=
  rfl

@[simp, mfld_simps]
theorem trans_to_local_homeomorph :
    (e.trans e').toLocalHomeomorph = e.to_local_homeomorph.trans e'.to_local_homeomorph :=
  LocalHomeomorph.eq_of_local_equiv_eq <| Equivₓ.trans_to_local_equiv _ _

end Homeomorph

namespace OpenEmbedding

variable (f : α → β) (h : OpenEmbedding f)

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `local_homeomorph.to_open_embedding`. -/
@[simps (config := mfldCfg) apply Source Target]
noncomputable def to_local_homeomorph [Nonempty α] : LocalHomeomorph α β :=
  LocalHomeomorph.ofContinuousOpen ((h.to_embedding.inj.inj_on univ).toLocalEquiv _ _) h.continuous.continuous_on
    h.is_open_map is_open_univ

theorem continuous_at_iff {f : α → β} {g : β → γ} (hf : OpenEmbedding f) {x : α} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  have : Nonempty α := ⟨x⟩
  convert ((hf.to_local_homeomorph f).continuous_at_iff_continuous_at_comp_right _).symm
  · apply (LocalHomeomorph.left_inv _ _).symm
    simp
    
  · simp
    

end OpenEmbedding

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (s : opens α) [Nonempty s]

/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
noncomputable def local_homeomorph_subtype_coe : LocalHomeomorph s α :=
  OpenEmbedding.toLocalHomeomorph _ s.2.open_embedding_subtype_coe

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_coe : (s.local_homeomorph_subtype_coe : s → α) = coe :=
  rfl

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_source : s.local_homeomorph_subtype_coe.source = Set.Univ :=
  rfl

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_target : s.local_homeomorph_subtype_coe.target = s := by
  simp' only [local_homeomorph_subtype_coe, Subtype.range_coe_subtype] with mfld_simps
  rfl

end TopologicalSpace.Opens

namespace LocalHomeomorph

open TopologicalSpace

variable (e : LocalHomeomorph α β)

variable (s : opens α) [Nonempty s]

/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
noncomputable def subtype_restr : LocalHomeomorph s β :=
  s.local_homeomorph_subtype_coe.trans e

theorem subtype_restr_def : e.subtype_restr s = s.local_homeomorph_subtype_coe.trans e :=
  rfl

@[simp, mfld_simps]
theorem subtype_restr_coe : ((e.subtype_restr s : LocalHomeomorph s β) : s → β) = Set.restrict (e : α → β) s :=
  rfl

@[simp, mfld_simps]
theorem subtype_restr_source : (e.subtype_restr s).Source = coe ⁻¹' e.source := by
  simp' only [subtype_restr_def] with mfld_simps

theorem subtype_restr_symm_trans_subtype_restr (f f' : LocalHomeomorph α β) :
    (f.subtype_restr s).symm.trans (f'.subtype_restr s) ≈ (f.symm.trans f').restr (f.target ∩ f.symm ⁻¹' s) := by
  simp only [subtype_restr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.preimage_open_of_open_symm s.2
  rw [← of_set_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine' eq_on_source.trans' _ (eq_on_source_refl _)
  have sets_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s := by
    mfld_set_tac
  have openness₂ : IsOpen (s : Set α) := s.2
  rw [of_set_trans', sets_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine' eq_on_source.trans' (eq_on_source_refl _) _
  refine' Setoidₓ.trans (trans_symm_self s.local_homeomorph_subtype_coe) _
  simp' only with mfld_simps

end LocalHomeomorph

