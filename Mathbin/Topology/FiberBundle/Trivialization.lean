/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.fiber_bundle.trivialization
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Bundle
import Mathbin.Topology.Algebra.Order.Field
import Mathbin.Topology.LocalHomeomorph

/-!
# Trivializations

## Main definitions

### Basic definitions

* `trivialization F p` : structure extending local homeomorphisms, defining a local
                  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `pretrivialization F proj` : trivialization as a local equivalence, mainly used when the
                                      topology on the total space has not yet been defined.

### Operations on bundles

We provide the following operations on `trivialization`s.

* `trivialization.comp_homeomorph`: given a local trivialization `e` of a fiber bundle
  `p : Z → B` and a homeomorphism `h : Z' ≃ₜ Z`, returns a local trivialization of the fiber bundle
  `p ∘ h`.

## Implementation notes

Previously, in mathlib, there was a structure `topological_vector_bundle.trivialization` which
extended another structure `topological_fibre_bundle.trivialization` by a linearity hypothesis. As
of PR #17359, we have changed this to a single structure `trivialization` (no namespace), together
with a mixin class `trivialization.is_linear`.

This permits all the *data* of a vector bundle to be held at the level of fibre bundles, so that the
same trivializations can underlie an object's structure as (say) a vector bundle over `ℂ` and as a
vector bundle over `ℝ`, as well as its structure simply as a fibre bundle.

This might be a little surprising, given the general trend of the library to ever-increased
bundling.  But in this case the typical motivation for more bundling does not apply: there is no
algebraic or order structure on the whole type of linear (say) trivializations of a bundle.
Indeed, since trivializations only have meaning on their base sets (taking junk values outside), the
type of linear trivializations is not even particularly well-behaved.

-/


open TopologicalSpace Filter Set Bundle

open TopologicalSpace Classical Bundle

variable {ι : Type _} {B : Type _} {F : Type _} {E : B → Type _}

variable (F) {Z : Type _} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- This structure contains the information left for a local trivialization (which is implemented
below as `trivialization F proj`) if the total space has not been given a topology, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`pretrivialization F proj` to a `trivialization F proj`. -/
@[ext, nolint has_nonempty_instance]
structure Pretrivialization (proj : Z → B) extends LocalEquiv Z (B × F) where
  open_target : IsOpen target
  baseSet : Set B
  open_base_set : IsOpen base_set
  source_eq : source = proj ⁻¹' base_set
  target_eq : target = base_set ×ˢ univ
  proj_to_fun : ∀ p ∈ source, (to_fun p).1 = proj p
#align pretrivialization Pretrivialization

namespace Pretrivialization

instance : CoeFun (Pretrivialization F proj) fun _ => Z → B × F :=
  ⟨fun e => e.toFun⟩

variable {F} (e : Pretrivialization F proj) {x : Z}

@[simp, mfld_simps]
theorem coe_coe : ⇑e.toLocalEquiv = e :=
  rfl
#align pretrivialization.coe_coe Pretrivialization.coe_coe

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_to_fun x ex
#align pretrivialization.coe_fst Pretrivialization.coe_fst

theorem mem_source : x ∈ e.source ↔ proj x ∈ e.baseSet := by rw [e.source_eq, mem_preimage]
#align pretrivialization.mem_source Pretrivialization.mem_source

theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)
#align pretrivialization.coe_fst' Pretrivialization.coe_fst'

protected theorem eq_on : EqOn (Prod.fst ∘ e) proj e.source := fun x hx => e.coe_fst hx
#align pretrivialization.eq_on Pretrivialization.eq_on

theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl
#align pretrivialization.mk_proj_snd Pretrivialization.mk_proj_snd

theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl
#align pretrivialization.mk_proj_snd' Pretrivialization.mk_proj_snd'

/-- Composition of inverse and coercion from the subtype of the target. -/
def setSymm : e.target → Z :=
  e.target.restrict e.toLocalEquiv.symm
#align pretrivialization.set_symm Pretrivialization.setSymm

theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.baseSet := by
  rw [e.target_eq, prod_univ, mem_preimage]
#align pretrivialization.mem_target Pretrivialization.mem_target

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.toLocalEquiv.symm x) = x.1 :=
  by
  have := (e.coe_fst (e.to_local_equiv.map_target hx)).symm
  rwa [← e.coe_coe, e.to_local_equiv.right_inv hx] at this
#align pretrivialization.proj_symm_apply Pretrivialization.proj_symm_apply

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    proj (e.toLocalEquiv.symm (b, x)) = b :=
  e.proj_symm_apply (e.mem_target.2 hx)
#align pretrivialization.proj_symm_apply' Pretrivialization.proj_symm_apply'

theorem proj_surj_on_base_set [Nonempty F] : Set.SurjOn proj e.source e.baseSet := fun b hb =>
  let ⟨y⟩ := ‹Nonempty F›
  ⟨e.toLocalEquiv.symm (b, y), e.toLocalEquiv.map_target <| e.mem_target.2 hb,
    e.proj_symm_apply' hb⟩
#align pretrivialization.proj_surj_on_base_set Pretrivialization.proj_surj_on_base_set

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.toLocalEquiv.symm x) = x :=
  e.toLocalEquiv.right_inv hx
#align pretrivialization.apply_symm_apply Pretrivialization.apply_symm_apply

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    e (e.toLocalEquiv.symm (b, x)) = (b, x) :=
  e.apply_symm_apply (e.mem_target.2 hx)
#align pretrivialization.apply_symm_apply' Pretrivialization.apply_symm_apply'

theorem symm_apply_apply {x : Z} (hx : x ∈ e.source) : e.toLocalEquiv.symm (e x) = x :=
  e.toLocalEquiv.left_inv hx
#align pretrivialization.symm_apply_apply Pretrivialization.symm_apply_apply

@[simp, mfld_simps]
theorem symm_apply_mk_proj {x : Z} (ex : x ∈ e.source) :
    e.toLocalEquiv.symm (proj x, (e x).2) = x := by
  rw [← e.coe_fst ex, Prod.mk.eta, ← e.coe_coe, e.to_local_equiv.left_inv ex]
#align pretrivialization.symm_apply_mk_proj Pretrivialization.symm_apply_mk_proj

@[simp, mfld_simps]
theorem preimage_symm_proj_base_set :
    e.toLocalEquiv.symm ⁻¹' (proj ⁻¹' e.baseSet) ∩ e.target = e.target :=
  by
  refine' inter_eq_right_iff_subset.mpr fun x hx => _
  simp only [mem_preimage, LocalEquiv.invFun_as_coe, e.proj_symm_apply hx]
  exact e.mem_target.mp hx
#align pretrivialization.preimage_symm_proj_base_set Pretrivialization.preimage_symm_proj_base_set

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, mfld_simps]
theorem preimage_symm_proj_inter (s : Set B) :
    e.toLocalEquiv.symm ⁻¹' (proj ⁻¹' s) ∩ e.baseSet ×ˢ univ = (s ∩ e.baseSet) ×ˢ univ :=
  by
  ext ⟨x, y⟩
  suffices x ∈ e.base_set → (proj (e.to_local_equiv.symm (x, y)) ∈ s ↔ x ∈ s) by
    simpa only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true_iff, mem_univ, and_congr_left_iff]
  intro h
  rw [e.proj_symm_apply' h]
#align pretrivialization.preimage_symm_proj_inter Pretrivialization.preimage_symm_proj_inter

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem target_inter_preimage_symm_source_eq (e f : Pretrivialization F proj) :
    f.target ∩ f.toLocalEquiv.symm ⁻¹' e.source = (e.baseSet ∩ f.baseSet) ×ˢ univ := by
  rw [inter_comm, f.target_eq, e.source_eq, f.preimage_symm_proj_inter]
#align pretrivialization.target_inter_preimage_symm_source_eq Pretrivialization.target_inter_preimage_symm_source_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem trans_source (e f : Pretrivialization F proj) :
    (f.toLocalEquiv.symm.trans e.toLocalEquiv).source = (e.baseSet ∩ f.baseSet) ×ˢ univ := by
  rw [LocalEquiv.trans_source, LocalEquiv.symm_source, e.target_inter_preimage_symm_source_eq]
#align pretrivialization.trans_source Pretrivialization.trans_source

theorem symm_trans_symm (e e' : Pretrivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).symm = e'.toLocalEquiv.symm.trans e.toLocalEquiv :=
  by rw [LocalEquiv.trans_symm_eq_symm_trans_symm, LocalEquiv.symm_symm]
#align pretrivialization.symm_trans_symm Pretrivialization.symm_trans_symm

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem symm_trans_source_eq (e e' : Pretrivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).source = (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
  rw [LocalEquiv.trans_source, e'.source_eq, LocalEquiv.symm_source, e.target_eq, inter_comm,
    e.preimage_symm_proj_inter, inter_comm]
#align pretrivialization.symm_trans_source_eq Pretrivialization.symm_trans_source_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem symm_trans_target_eq (e e' : Pretrivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).target = (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
  rw [← LocalEquiv.symm_source, symm_trans_symm, symm_trans_source_eq, inter_comm]
#align pretrivialization.symm_trans_target_eq Pretrivialization.symm_trans_target_eq

variable {B F} (e' : Pretrivialization F (π E)) {x' : TotalSpace E} {b : B} {y : E b}

theorem coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.baseSet :=
  e'.mem_source
#align pretrivialization.coe_mem_source Pretrivialization.coe_mem_source

@[simp, mfld_simps]
theorem coe_coe_fst (hb : b ∈ e'.baseSet) : (e' y).1 = b :=
  e'.coe_fst (e'.mem_source.2 hb)
#align pretrivialization.coe_coe_fst Pretrivialization.coe_coe_fst

theorem mk_mem_target {x : B} {y : F} : (x, y) ∈ e'.target ↔ x ∈ e'.baseSet :=
  e'.mem_target
#align pretrivialization.mk_mem_target Pretrivialization.mk_mem_target

theorem symm_coe_proj {x : B} {y : F} (e' : Pretrivialization F (π E)) (h : x ∈ e'.baseSet) :
    (e'.toLocalEquiv.symm (x, y)).1 = x :=
  e'.proj_symm_apply' h
#align pretrivialization.symm_coe_proj Pretrivialization.symm_coe_proj

section Zero

variable [∀ x, Zero (E x)]

/-- A fiberwise inverse to `e`. This is the function `F → E b` that induces a local inverse
`B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected noncomputable def symm (e : Pretrivialization F (π E)) (b : B) (y : F) : E b :=
  if hb : b ∈ e.baseSet then
    cast (congr_arg E (e.proj_symm_apply' hb)) (e.toLocalEquiv.symm (b, y)).2
  else 0
#align pretrivialization.symm Pretrivialization.symm

theorem symm_apply (e : Pretrivialization F (π E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toLocalEquiv.symm (b, y)).2 :=
  dif_pos hb
#align pretrivialization.symm_apply Pretrivialization.symm_apply

theorem symm_apply_of_not_mem (e : Pretrivialization F (π E)) {b : B} (hb : b ∉ e.baseSet) (y : F) :
    e.symm b y = 0 :=
  dif_neg hb
#align pretrivialization.symm_apply_of_not_mem Pretrivialization.symm_apply_of_not_mem

theorem coe_symm_of_not_mem (e : Pretrivialization F (π E)) {b : B} (hb : b ∉ e.baseSet) :
    (e.symm b : F → E b) = 0 :=
  funext fun y => dif_neg hb
#align pretrivialization.coe_symm_of_not_mem Pretrivialization.coe_symm_of_not_mem

theorem mk_symm (e : Pretrivialization F (π E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    totalSpaceMk b (e.symm b y) = e.toLocalEquiv.symm (b, y) := by
  rw [e.symm_apply hb, total_space.mk_cast, total_space.eta]
#align pretrivialization.mk_symm Pretrivialization.mk_symm

theorem symm_proj_apply (e : Pretrivialization F (π E)) (z : TotalSpace E)
    (hz : z.proj ∈ e.baseSet) : e.symm z.proj (e z).2 = z.2 := by
  rw [e.symm_apply hz, cast_eq_iff_heq, e.mk_proj_snd' hz, e.symm_apply_apply (e.mem_source.mpr hz)]
#align pretrivialization.symm_proj_apply Pretrivialization.symm_proj_apply

theorem symm_apply_apply_mk (e : Pretrivialization F (π E)) {b : B} (hb : b ∈ e.baseSet) (y : E b) :
    e.symm b (e (totalSpaceMk b y)).2 = y :=
  e.symm_proj_apply (totalSpaceMk b y) hb
#align pretrivialization.symm_apply_apply_mk Pretrivialization.symm_apply_apply_mk

theorem apply_mk_symm (e : Pretrivialization F (π E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e (totalSpaceMk b (e.symm b y)) = (b, y) := by
  rw [e.mk_symm hb, e.apply_symm_apply (e.mk_mem_target.mpr hb)]
#align pretrivialization.apply_mk_symm Pretrivialization.apply_mk_symm

end Zero

end Pretrivialization

variable [TopologicalSpace Z] [TopologicalSpace (TotalSpace E)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
@[ext, nolint has_nonempty_instance]
structure Trivialization (proj : Z → B) extends LocalHomeomorph Z (B × F) where
  baseSet : Set B
  open_base_set : IsOpen base_set
  source_eq : source = proj ⁻¹' base_set
  target_eq : target = base_set ×ˢ univ
  proj_to_fun : ∀ p ∈ source, (to_local_homeomorph p).1 = proj p
#align trivialization Trivialization

namespace Trivialization

variable {F} (e : Trivialization F proj) {x : Z}

/-- Natural identification as a `pretrivialization`. -/
def toPretrivialization : Pretrivialization F proj :=
  { e with }
#align trivialization.to_pretrivialization Trivialization.toPretrivialization

instance : CoeFun (Trivialization F proj) fun _ => Z → B × F :=
  ⟨fun e => e.toFun⟩

instance : Coe (Trivialization F proj) (Pretrivialization F proj) :=
  ⟨toPretrivialization⟩

theorem to_pretrivialization_injective :
    Function.Injective fun e : Trivialization F proj => e.toPretrivialization :=
  by
  intro e e'
  rw [Pretrivialization.ext_iff, Trivialization.ext_iff, ←
    local_homeomorph.to_local_equiv_injective.eq_iff]
  exact id
#align trivialization.to_pretrivialization_injective Trivialization.to_pretrivialization_injective

@[simp, mfld_simps]
theorem coe_coe : ⇑e.toLocalHomeomorph = e :=
  rfl
#align trivialization.coe_coe Trivialization.coe_coe

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_to_fun x ex
#align trivialization.coe_fst Trivialization.coe_fst

protected theorem eq_on : EqOn (Prod.fst ∘ e) proj e.source := fun x hx => e.coe_fst hx
#align trivialization.eq_on Trivialization.eq_on

theorem mem_source : x ∈ e.source ↔ proj x ∈ e.baseSet := by rw [e.source_eq, mem_preimage]
#align trivialization.mem_source Trivialization.mem_source

theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)
#align trivialization.coe_fst' Trivialization.coe_fst'

theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl
#align trivialization.mk_proj_snd Trivialization.mk_proj_snd

theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl
#align trivialization.mk_proj_snd' Trivialization.mk_proj_snd'

theorem source_inter_preimage_target_inter (s : Set (B × F)) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toLocalHomeomorph.source_inter_preimage_target_inter s
#align trivialization.source_inter_preimage_target_inter Trivialization.source_inter_preimage_target_inter

@[simp, mfld_simps]
theorem coe_mk (e : LocalHomeomorph Z (B × F)) (i j k l m) (x : Z) :
    (Trivialization.mk e i j k l m : Trivialization F proj) x = e x :=
  rfl
#align trivialization.coe_mk Trivialization.coe_mk

theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.baseSet :=
  e.toPretrivialization.mem_target
#align trivialization.mem_target Trivialization.mem_target

theorem map_target {x : B × F} (hx : x ∈ e.target) : e.toLocalHomeomorph.symm x ∈ e.source :=
  e.toLocalHomeomorph.map_target hx
#align trivialization.map_target Trivialization.map_target

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.toLocalHomeomorph.symm x) = x.1 :=
  e.toPretrivialization.proj_symm_apply hx
#align trivialization.proj_symm_apply Trivialization.proj_symm_apply

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    proj (e.toLocalHomeomorph.symm (b, x)) = b :=
  e.toPretrivialization.proj_symm_apply' hx
#align trivialization.proj_symm_apply' Trivialization.proj_symm_apply'

theorem proj_surj_on_base_set [Nonempty F] : Set.SurjOn proj e.source e.baseSet :=
  e.toPretrivialization.proj_surj_on_base_set
#align trivialization.proj_surj_on_base_set Trivialization.proj_surj_on_base_set

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.toLocalHomeomorph.symm x) = x :=
  e.toLocalHomeomorph.right_inv hx
#align trivialization.apply_symm_apply Trivialization.apply_symm_apply

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.baseSet) :
    e (e.toLocalHomeomorph.symm (b, x)) = (b, x) :=
  e.toPretrivialization.apply_symm_apply' hx
#align trivialization.apply_symm_apply' Trivialization.apply_symm_apply'

@[simp, mfld_simps]
theorem symm_apply_mk_proj (ex : x ∈ e.source) : e.toLocalHomeomorph.symm (proj x, (e x).2) = x :=
  e.toPretrivialization.symm_apply_mk_proj ex
#align trivialization.symm_apply_mk_proj Trivialization.symm_apply_mk_proj

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem symm_trans_source_eq (e e' : Trivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).source = (e.baseSet ∩ e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_source_eq e.toPretrivialization e'
#align trivialization.symm_trans_source_eq Trivialization.symm_trans_source_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem symm_trans_target_eq (e e' : Trivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).target = (e.baseSet ∩ e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_target_eq e.toPretrivialization e'
#align trivialization.symm_trans_target_eq Trivialization.symm_trans_target_eq

theorem coe_fst_eventually_eq_proj (ex : x ∈ e.source) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  mem_nhds_iff.2 ⟨e.source, fun y hy => e.coe_fst hy, e.open_source, ex⟩
#align trivialization.coe_fst_eventually_eq_proj Trivialization.coe_fst_eventually_eq_proj

theorem coe_fst_eventually_eq_proj' (ex : proj x ∈ e.baseSet) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  e.coe_fst_eventually_eq_proj (e.mem_source.2 ex)
#align trivialization.coe_fst_eventually_eq_proj' Trivialization.coe_fst_eventually_eq_proj'

theorem map_proj_nhds (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) := by
  rw [← e.coe_fst ex, ← map_congr (e.coe_fst_eventually_eq_proj ex), ← map_map, ← e.coe_coe,
    e.to_local_homeomorph.map_nhds_eq ex, map_fst_nhds]
#align trivialization.map_proj_nhds Trivialization.map_proj_nhds

theorem preimage_subset_source {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ⊆ e.source :=
  fun p hp => e.mem_source.mpr (hb hp)
#align trivialization.preimage_subset_source Trivialization.preimage_subset_source

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem image_preimage_eq_prod_univ {s : Set B} (hb : s ⊆ e.baseSet) :
    e '' (proj ⁻¹' s) = s ×ˢ univ :=
  Subset.antisymm
    (image_subset_iff.mpr fun p hp =>
      ⟨(e.proj_to_fun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)
    fun p hp =>
    let hp' : p ∈ e.target := e.mem_target.mpr (hb hp.1)
    ⟨e.invFun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp'⟩
#align trivialization.image_preimage_eq_prod_univ Trivialization.image_preimage_eq_prod_univ

/-- The preimage of a subset of the base set is homeomorphic to the product with the fiber. -/
def preimageHomeomorph {s : Set B} (hb : s ⊆ e.baseSet) : proj ⁻¹' s ≃ₜ s × F :=
  (e.toLocalHomeomorph.homeomorphOfImageSubsetSource (e.preimage_subset_source hb)
        (e.image_preimage_eq_prod_univ hb)).trans
    ((Homeomorph.Set.prod s univ).trans ((Homeomorph.refl s).prodCongr (Homeomorph.Set.univ F)))
#align trivialization.preimage_homeomorph Trivialization.preimageHomeomorph

@[simp]
theorem preimage_homeomorph_apply {s : Set B} (hb : s ⊆ e.baseSet) (p : proj ⁻¹' s) :
    e.preimageHomeomorph hb p = (⟨proj p, p.2⟩, (e p).2) :=
  Prod.ext (Subtype.ext (e.proj_to_fun p (e.mem_source.mpr (hb p.2)))) rfl
#align trivialization.preimage_homeomorph_apply Trivialization.preimage_homeomorph_apply

@[simp]
theorem preimage_homeomorph_symm_apply {s : Set B} (hb : s ⊆ e.baseSet) (p : s × F) :
    (e.preimageHomeomorph hb).symm p = ⟨e.symm (p.1, p.2), ((e.preimageHomeomorph hb).symm p).2⟩ :=
  rfl
#align trivialization.preimage_homeomorph_symm_apply Trivialization.preimage_homeomorph_symm_apply

/-- The source is homeomorphic to the product of the base set with the fiber. -/
def sourceHomeomorphBaseSetProd : e.source ≃ₜ e.baseSet × F :=
  (Homeomorph.setCongr e.source_eq).trans (e.preimageHomeomorph subset_rfl)
#align trivialization.source_homeomorph_base_set_prod Trivialization.sourceHomeomorphBaseSetProd

@[simp]
theorem source_homeomorph_base_set_prod_apply (p : e.source) :
    e.sourceHomeomorphBaseSetProd p = (⟨proj p, e.mem_source.mp p.2⟩, (e p).2) :=
  e.preimage_homeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩
#align trivialization.source_homeomorph_base_set_prod_apply Trivialization.source_homeomorph_base_set_prod_apply

@[simp]
theorem source_homeomorph_base_set_prod_symm_apply (p : e.baseSet × F) :
    e.sourceHomeomorphBaseSetProd.symm p =
      ⟨e.symm (p.1, p.2), (e.sourceHomeomorphBaseSetProd.symm p).2⟩ :=
  rfl
#align trivialization.source_homeomorph_base_set_prod_symm_apply Trivialization.source_homeomorph_base_set_prod_symm_apply

/-- Each fiber of a trivialization is homeomorphic to the specified fiber. -/
def preimageSingletonHomeomorph {b : B} (hb : b ∈ e.baseSet) : proj ⁻¹' {b} ≃ₜ F :=
  (e.preimageHomeomorph (Set.singleton_subset_iff.mpr hb)).trans
    (((Homeomorph.homeomorphOfUnique ({b} : Set B) PUnit).prodCongr (Homeomorph.refl F)).trans
      (Homeomorph.punitProd F))
#align trivialization.preimage_singleton_homeomorph Trivialization.preimageSingletonHomeomorph

@[simp]
theorem preimage_singleton_homeomorph_apply {b : B} (hb : b ∈ e.baseSet) (p : proj ⁻¹' {b}) :
    e.preimageSingletonHomeomorph hb p = (e p).2 :=
  rfl
#align trivialization.preimage_singleton_homeomorph_apply Trivialization.preimage_singleton_homeomorph_apply

@[simp]
theorem preimage_singleton_homeomorph_symm_apply {b : B} (hb : b ∈ e.baseSet) (p : F) :
    (e.preimageSingletonHomeomorph hb).symm p =
      ⟨e.symm (b, p), by rw [mem_preimage, e.proj_symm_apply' hb, mem_singleton_iff]⟩ :=
  rfl
#align trivialization.preimage_singleton_homeomorph_symm_apply Trivialization.preimage_singleton_homeomorph_symm_apply

/-- In the domain of a bundle trivialization, the projection is continuous-/
theorem continuous_at_proj (ex : x ∈ e.source) : ContinuousAt proj x :=
  (e.map_proj_nhds ex).le
#align trivialization.continuous_at_proj Trivialization.continuous_at_proj

/-- Composition of a `trivialization` and a `homeomorph`. -/
protected def compHomeomorph {Z' : Type _} [TopologicalSpace Z'] (h : Z' ≃ₜ Z) :
    Trivialization F (proj ∘ h)
    where
  toLocalHomeomorph := h.toLocalHomeomorph.trans e.toLocalHomeomorph
  baseSet := e.baseSet
  open_base_set := e.open_base_set
  source_eq := by simp [e.source_eq, preimage_preimage]
  target_eq := by simp [e.target_eq]
  proj_to_fun p hp := by
    have hp : h p ∈ e.source := by simpa using hp
    simp [hp]
#align trivialization.comp_homeomorph Trivialization.compHomeomorph

/-- Read off the continuity of a function `f : Z → X` at `z : Z` by transferring via a
trivialization of `Z` containing `z`. -/
theorem continuous_at_of_comp_right {X : Type _} [TopologicalSpace X] {f : Z → X} {z : Z}
    (e : Trivialization F proj) (he : proj z ∈ e.baseSet)
    (hf : ContinuousAt (f ∘ e.toLocalEquiv.symm) (e z)) : ContinuousAt f z :=
  by
  have hez : z ∈ e.to_local_equiv.symm.target :=
    by
    rw [LocalEquiv.symm_target, e.mem_source]
    exact he
  rwa [e.to_local_homeomorph.symm.continuous_at_iff_continuous_at_comp_right hez,
    LocalHomeomorph.symm_symm]
#align trivialization.continuous_at_of_comp_right Trivialization.continuous_at_of_comp_right

/-- Read off the continuity of a function `f : X → Z` at `x : X` by transferring via a
trivialization of `Z` containing `f x`. -/
theorem continuous_at_of_comp_left {X : Type _} [TopologicalSpace X] {f : X → Z} {x : X}
    (e : Trivialization F proj) (hf_proj : ContinuousAt (proj ∘ f) x) (he : proj (f x) ∈ e.baseSet)
    (hf : ContinuousAt (e ∘ f) x) : ContinuousAt f x :=
  by
  rw [e.to_local_homeomorph.continuous_at_iff_continuous_at_comp_left]
  · exact hf
  rw [e.source_eq, ← preimage_comp]
  exact hf_proj.preimage_mem_nhds (e.open_base_set.mem_nhds he)
#align trivialization.continuous_at_of_comp_left Trivialization.continuous_at_of_comp_left

variable {E} (e' : Trivialization F (π E)) {x' : TotalSpace E} {b : B} {y : E b}

protected theorem continuous_on : ContinuousOn e' e'.source :=
  e'.continuous_to_fun
#align trivialization.continuous_on Trivialization.continuous_on

theorem coe_mem_source : ↑y ∈ e'.source ↔ b ∈ e'.baseSet :=
  e'.mem_source
#align trivialization.coe_mem_source Trivialization.coe_mem_source

theorem open_target : IsOpen e'.target :=
  by
  rw [e'.target_eq]
  exact e'.open_base_set.prod is_open_univ
#align trivialization.open_target Trivialization.open_target

@[simp, mfld_simps]
theorem coe_coe_fst (hb : b ∈ e'.baseSet) : (e' y).1 = b :=
  e'.coe_fst (e'.mem_source.2 hb)
#align trivialization.coe_coe_fst Trivialization.coe_coe_fst

theorem mk_mem_target {y : F} : (b, y) ∈ e'.target ↔ b ∈ e'.baseSet :=
  e'.toPretrivialization.mem_target
#align trivialization.mk_mem_target Trivialization.mk_mem_target

theorem symm_apply_apply {x : TotalSpace E} (hx : x ∈ e'.source) :
    e'.toLocalHomeomorph.symm (e' x) = x :=
  e'.toLocalEquiv.left_inv hx
#align trivialization.symm_apply_apply Trivialization.symm_apply_apply

@[simp, mfld_simps]
theorem symm_coe_proj {x : B} {y : F} (e : Trivialization F (π E)) (h : x ∈ e.baseSet) :
    (e.toLocalHomeomorph.symm (x, y)).1 = x :=
  e.proj_symm_apply' h
#align trivialization.symm_coe_proj Trivialization.symm_coe_proj

section Zero

variable [∀ x, Zero (E x)]

/-- A fiberwise inverse to `e'`. The function `F → E x` that induces a local inverse
`B × F → total_space E` of `e'` on `e'.base_set`. It is defined to be `0` outside `e'.base_set`. -/
protected noncomputable def symm (e : Trivialization F (π E)) (b : B) (y : F) : E b :=
  e.toPretrivialization.symm b y
#align trivialization.symm Trivialization.symm

theorem symm_apply (e : Trivialization F (π E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toLocalHomeomorph.symm (b, y)).2 :=
  dif_pos hb
#align trivialization.symm_apply Trivialization.symm_apply

theorem symm_apply_of_not_mem (e : Trivialization F (π E)) {b : B} (hb : b ∉ e.baseSet) (y : F) :
    e.symm b y = 0 :=
  dif_neg hb
#align trivialization.symm_apply_of_not_mem Trivialization.symm_apply_of_not_mem

theorem mk_symm (e : Trivialization F (π E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    totalSpaceMk b (e.symm b y) = e.toLocalHomeomorph.symm (b, y) :=
  e.toPretrivialization.mk_symm hb y
#align trivialization.mk_symm Trivialization.mk_symm

theorem symm_proj_apply (e : Trivialization F (π E)) (z : TotalSpace E) (hz : z.proj ∈ e.baseSet) :
    e.symm z.proj (e z).2 = z.2 :=
  e.toPretrivialization.symm_proj_apply z hz
#align trivialization.symm_proj_apply Trivialization.symm_proj_apply

theorem symm_apply_apply_mk (e : Trivialization F (π E)) {b : B} (hb : b ∈ e.baseSet) (y : E b) :
    e.symm b (e (totalSpaceMk b y)).2 = y :=
  e.symm_proj_apply (totalSpaceMk b y) hb
#align trivialization.symm_apply_apply_mk Trivialization.symm_apply_apply_mk

theorem apply_mk_symm (e : Trivialization F (π E)) {b : B} (hb : b ∈ e.baseSet) (y : F) :
    e (totalSpaceMk b (e.symm b y)) = (b, y) :=
  e.toPretrivialization.apply_mk_symm hb y
#align trivialization.apply_mk_symm Trivialization.apply_mk_symm

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem continuous_on_symm (e : Trivialization F (π E)) :
    ContinuousOn (fun z : B × F => totalSpaceMk z.1 (e.symm z.1 z.2)) (e.baseSet ×ˢ univ) :=
  by
  have :
    ∀ (z : B × F) (hz : z ∈ e.base_set ×ˢ (univ : Set F)),
      total_space_mk z.1 (e.symm z.1 z.2) = e.to_local_homeomorph.symm z :=
    by
    rintro x ⟨hx : x.1 ∈ e.base_set, _⟩
    simp_rw [e.mk_symm hx, Prod.mk.eta]
  refine' ContinuousOn.congr _ this
  rw [← e.target_eq]
  exact e.to_local_homeomorph.continuous_on_symm
#align trivialization.continuous_on_symm Trivialization.continuous_on_symm

end Zero

/-- If `e` is a `trivialization` of `proj : Z → B` with fiber `F` and `h` is a homeomorphism
`F ≃ₜ F'`, then `e.trans_fiber_homeomorph h` is the trivialization of `proj` with the fiber `F'`
that sends `p : Z` to `((e p).1, h (e p).2)`. -/
def transFiberHomeomorph {F' : Type _} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') : Trivialization F' proj
    where
  toLocalHomeomorph := e.toLocalHomeomorph.transHomeomorph <| (Homeomorph.refl _).prodCongr h
  baseSet := e.baseSet
  open_base_set := e.open_base_set
  source_eq := e.source_eq
  target_eq := by simp [e.target_eq, prod_univ, preimage_preimage]
  proj_to_fun := e.proj_to_fun
#align trivialization.trans_fiber_homeomorph Trivialization.transFiberHomeomorph

@[simp]
theorem trans_fiber_homeomorph_apply {F' : Type _} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') (x : Z) : e.transFiberHomeomorph h x = ((e x).1, h (e x).2) :=
  rfl
#align trivialization.trans_fiber_homeomorph_apply Trivialization.trans_fiber_homeomorph_apply

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations. See also
`trivialization.coord_change_homeomorph` for a version bundled as `F ≃ₜ F`. -/
def coordChange (e₁ e₂ : Trivialization F proj) (b : B) (x : F) : F :=
  (e₂ <| e₁.toLocalHomeomorph.symm (b, x)).2
#align trivialization.coord_change Trivialization.coordChange

theorem mk_coord_change (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (x : F) :
    (b, e₁.coordChange e₂ b x) = e₂ (e₁.toLocalHomeomorph.symm (b, x)) :=
  by
  refine' Prod.ext _ rfl
  rw [e₂.coe_fst', ← e₁.coe_fst', e₁.apply_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
#align trivialization.mk_coord_change Trivialization.mk_coord_change

theorem coord_change_apply_snd (e₁ e₂ : Trivialization F proj) {p : Z} (h : proj p ∈ e₁.baseSet) :
    e₁.coordChange e₂ (proj p) (e₁ p).snd = (e₂ p).snd := by
  rw [coord_change, e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]
#align trivialization.coord_change_apply_snd Trivialization.coord_change_apply_snd

theorem coord_change_same_apply (e : Trivialization F proj) {b : B} (h : b ∈ e.baseSet) (x : F) :
    e.coordChange e b x = x := by rw [coord_change, e.apply_symm_apply' h]
#align trivialization.coord_change_same_apply Trivialization.coord_change_same_apply

theorem coord_change_same (e : Trivialization F proj) {b : B} (h : b ∈ e.baseSet) :
    e.coordChange e b = id :=
  funext <| e.coord_change_same_apply h
#align trivialization.coord_change_same Trivialization.coord_change_same

theorem coord_change_coord_change (e₁ e₂ e₃ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (x : F) :
    e₂.coordChange e₃ b (e₁.coordChange e₂ b x) = e₁.coordChange e₃ b x :=
  by
  rw [coord_change, e₁.mk_coord_change _ h₁ h₂, ← e₂.coe_coe, e₂.to_local_homeomorph.left_inv,
    coord_change]
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]
#align trivialization.coord_change_coord_change Trivialization.coord_change_coord_change

theorem continuous_coord_change (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : Continuous (e₁.coordChange e₂ b) :=
  by
  refine'
    continuous_snd.comp
      (e₂.to_local_homeomorph.continuous_on.comp_continuous
        (e₁.to_local_homeomorph.continuous_on_symm.comp_continuous _ _) _)
  · exact continuous_const.prod_mk continuous_id
  · exact fun x => e₁.mem_target.2 h₁
  · intro x
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]
#align trivialization.continuous_coord_change Trivialization.continuous_coord_change

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations,
as a homeomorphism. -/
protected def coordChangeHomeomorph (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : F ≃ₜ F
    where
  toFun := e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv x := by simp only [*, coord_change_coord_change, coord_change_same_apply]
  right_inv x := by simp only [*, coord_change_coord_change, coord_change_same_apply]
  continuous_to_fun := e₁.continuous_coord_change e₂ h₁ h₂
  continuous_inv_fun := e₂.continuous_coord_change e₁ h₂ h₁
#align trivialization.coord_change_homeomorph Trivialization.coordChangeHomeomorph

@[simp]
theorem coord_change_homeomorph_coe (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : ⇑(e₁.coordChangeHomeomorph e₂ h₁ h₂) = e₁.coordChange e₂ b :=
  rfl
#align trivialization.coord_change_homeomorph_coe Trivialization.coord_change_homeomorph_coe

variable {F} {B' : Type _} [TopologicalSpace B']

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem is_image_preimage_prod (e : Trivialization F proj) (s : Set B) :
    e.toLocalHomeomorph.IsImage (proj ⁻¹' s) (s ×ˢ univ) := fun x hx => by simp [e.coe_fst', hx]
#align trivialization.is_image_preimage_prod Trivialization.is_image_preimage_prod

/-- Restrict a `trivialization` to an open set in the base. `-/
protected def restrOpen (e : Trivialization F proj) (s : Set B) (hs : IsOpen s) :
    Trivialization F proj
    where
  toLocalHomeomorph :=
    ((e.is_image_preimage_prod s).symm.restr
        (IsOpen.inter e.open_target (hs.Prod is_open_univ))).symm
  baseSet := e.baseSet ∩ s
  open_base_set := IsOpen.inter e.open_base_set hs
  source_eq := by simp [e.source_eq]
  target_eq := by simp [e.target_eq, prod_univ]
  proj_to_fun p hp := e.proj_to_fun p hp.1
#align trivialization.restr_open Trivialization.restrOpen

section Piecewise

theorem frontier_preimage (e : Trivialization F proj) (s : Set B) :
    e.source ∩ frontier (proj ⁻¹' s) = proj ⁻¹' (e.baseSet ∩ frontier s) := by
  rw [← (e.is_image_preimage_prod s).frontier.preimage_eq, frontier_prod_univ_eq,
    (e.is_image_preimage_prod _).preimage_eq, e.source_eq, preimage_inter]
#align trivialization.frontier_preimage Trivialization.frontier_preimage

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given two bundle trivializations `e`, `e'` of `proj : Z → B` and a set `s : set B` such that
the base sets of `e` and `e'` intersect `frontier s` on the same set and `e p = e' p` whenever
`proj p ∈ e.base_set ∩ frontier s`, `e.piecewise e' s Hs Heq` is the bundle trivialization over
`set.ite s e.base_set e'.base_set` that is equal to `e` on `proj ⁻¹ s` and is equal to `e'`
otherwise. -/
noncomputable def piecewise (e e' : Trivialization F proj) (s : Set B)
    (Hs : e.baseSet ∩ frontier s = e'.baseSet ∩ frontier s)
    (Heq : EqOn e e' <| proj ⁻¹' (e.baseSet ∩ frontier s)) : Trivialization F proj
    where
  toLocalHomeomorph :=
    e.toLocalHomeomorph.piecewise e'.toLocalHomeomorph (proj ⁻¹' s) (s ×ˢ univ)
      (e.is_image_preimage_prod s) (e'.is_image_preimage_prod s)
      (by rw [e.frontier_preimage, e'.frontier_preimage, Hs]) (by rwa [e.frontier_preimage])
  baseSet := s.ite e.baseSet e'.baseSet
  open_base_set := e.open_base_set.ite e'.open_base_set Hs
  source_eq := by simp [e.source_eq, e'.source_eq]
  target_eq := by simp [e.target_eq, e'.target_eq, prod_univ]
  proj_to_fun := by rintro p (⟨he, hs⟩ | ⟨he, hs⟩) <;> simp [*]
#align trivialization.piecewise Trivialization.piecewise

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B`
over a linearly ordered base `B` and a point `a ∈ e.base_set ∩ e'.base_set` such that
`e` equals `e'` on `proj ⁻¹' {a}`, `e.piecewise_le_of_eq e' a He He' Heq` is the bundle
trivialization over `set.ite (Iic a) e.base_set e'.base_set` that is equal to `e` on points `p`
such that `proj p ≤ a` and is equal to `e'` otherwise. -/
noncomputable def piecewiseLeOfEq [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) (Heq : ∀ p, proj p = a → e p = e' p) :
    Trivialization F proj :=
  e.piecewise e' (Iic a)
    (Set.ext fun x =>
      and_congr_left_iff.2 fun hx => by
        simp [He, He', mem_singleton_iff.1 (frontier_Iic_subset _ hx)])
    fun p hp => Heq p <| frontier_Iic_subset _ hp.2
#align trivialization.piecewise_le_of_eq Trivialization.piecewiseLeOfEq

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B` over a
linearly ordered base `B` and a point `a ∈ e.base_set ∩ e'.base_set`, `e.piecewise_le e' a He He'`
is the bundle trivialization over `set.ite (Iic a) e.base_set e'.base_set` that is equal to `e` on
points `p` such that `proj p ≤ a` and is equal to `((e' p).1, h (e' p).2)` otherwise, where
`h = `e'.coord_change_homeomorph e _ _` is the homeomorphism of the fiber such that
`h (e' p).2 = (e p).2` whenever `e p = a`. -/
noncomputable def piecewiseLe [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a ∈ e.baseSet) (He' : a ∈ e'.baseSet) : Trivialization F proj :=
  e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' <|
    by
    rintro p rfl
    ext1
    · simp [e.coe_fst', e'.coe_fst', *]
    · simp [e'.coord_change_apply_snd, *]
#align trivialization.piecewise_le Trivialization.piecewiseLe

/-- Given two bundle trivializations `e`, `e'` over disjoint sets, `e.disjoint_union e' H` is the
bundle trivialization over the union of the base sets that agrees with `e` and `e'` over their
base sets. -/
noncomputable def disjointUnion (e e' : Trivialization F proj) (H : Disjoint e.baseSet e'.baseSet) :
    Trivialization F proj
    where
  toLocalHomeomorph :=
    e.toLocalHomeomorph.disjointUnion e'.toLocalHomeomorph
      (by
        rw [e.source_eq, e'.source_eq]
        exact H.preimage _)
      (by
        rw [e.target_eq, e'.target_eq, disjoint_iff_inf_le]
        intro x hx
        exact H.le_bot ⟨hx.1.1, hx.2.1⟩)
  baseSet := e.baseSet ∪ e'.baseSet
  open_base_set := IsOpen.union e.open_base_set e'.open_base_set
  source_eq := congr_arg₂ (· ∪ ·) e.source_eq e'.source_eq
  target_eq := (congr_arg₂ (· ∪ ·) e.target_eq e'.target_eq).trans union_prod.symm
  proj_to_fun := by
    rintro p (hp | hp')
    · show (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_mem, e.coe_fst] <;> exact hp
    · show (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_not_mem, e'.coe_fst hp']
      simp only [e.source_eq, e'.source_eq] at hp'⊢
      exact fun h => H.le_bot ⟨h, hp'⟩
#align trivialization.disjoint_union Trivialization.disjointUnion

end Piecewise

end Trivialization

