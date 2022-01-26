import Mathbin.Topology.Algebra.Monoid
import Mathbin.GroupTheory.GroupAction.Prod
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.Algebra.MulAction2

/-!
# Continuous monoid action

In this file we define class `has_continuous_smul`. We say `has_continuous_smul M α` if `M` acts on
`α` and the map `(c, x) ↦ c • x` is continuous on `M × α`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `has_continuous_smul M α` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × α`;
* `homeomorph.smul_of_ne_zero`: if a group with zero `G₀` (e.g., a field) acts on `α` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `α`;
* `homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `α`
  is a homeomorphism of `α`.
* `units.has_continuous_smul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `continuous.smul`
or `filter.tendsto.smul` that provide dot-syntax access to `continuous_smul`.
-/


open_locale TopologicalSpace Pointwise

open Filter

/-- Class `has_continuous_smul M α` says that the scalar multiplication `(•) : M → α → α`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class HasContinuousSmul (M α : Type _) [HasScalar M α] [TopologicalSpace M] [TopologicalSpace α] : Prop where
  continuous_smul : Continuous fun p : M × α => p.1 • p.2

export HasContinuousSmul (continuous_smul)

/-- Class `has_continuous_vadd M α` says that the additive action `(+ᵥ) : M → α → α`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class HasContinuousVadd (M α : Type _) [HasVadd M α] [TopologicalSpace M] [TopologicalSpace α] : Prop where
  continuous_vadd : Continuous fun p : M × α => p.1 +ᵥ p.2

export HasContinuousVadd (continuous_vadd)

attribute [to_additive] HasContinuousSmul

variable {M α β : Type _} [TopologicalSpace M] [TopologicalSpace α]

section HasScalar

variable [HasScalar M α] [HasContinuousSmul M α]

@[to_additive]
instance (priority := 100) HasContinuousSmul.has_continuous_smul₂ : HasContinuousSmul₂ M α where
  continuous_smul₂ := fun _ => continuous_smul.comp (continuous_const.prod_mk continuous_id)

@[to_additive]
theorem Filter.Tendsto.smul {f : β → M} {g : β → α} {l : Filter β} {c : M} {a : α} (hf : tendsto f l (𝓝 c))
    (hg : tendsto g l (𝓝 a)) : tendsto (fun x => f x • g x) l (𝓝 <| c • a) :=
  (continuous_smul.Tendsto _).comp (hf.prod_mk_nhds hg)

@[to_additive]
theorem Filter.Tendsto.const_smul {f : β → α} {l : Filter β} {a : α} (hf : tendsto f l (𝓝 a)) (c : M) :
    tendsto (fun x => c • f x) l (𝓝 (c • a)) :=
  tendsto_const_nhds.smul hf

@[to_additive]
theorem Filter.Tendsto.smul_const {f : β → M} {l : Filter β} {c : M} (hf : tendsto f l (𝓝 c)) (a : α) :
    tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.smul tendsto_const_nhds

variable [TopologicalSpace β] {f : β → M} {g : β → α} {b : β} {s : Set β}

@[to_additive]
theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
    ContinuousWithinAt (fun x => f x • g x) s b :=
  hf.smul hg

@[to_additive]
theorem ContinuousWithinAt.const_smul (hg : ContinuousWithinAt g s b) (c : M) :
    ContinuousWithinAt (fun x => c • g x) s b :=
  hg.const_smul c

@[to_additive]
theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) : ContinuousAt (fun x => f x • g x) b :=
  hf.smul hg

@[to_additive]
theorem ContinuousAt.const_smul (hg : ContinuousAt g b) (c : M) : ContinuousAt (fun x => c • g x) b :=
  hg.const_smul c

@[to_additive]
theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => f x • g x) s :=
  fun x hx => (hf x hx).smul (hg x hx)

@[to_additive]
theorem ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) : ContinuousOn (fun x => c • g x) s := fun x hx =>
  (hg x hx).const_smul c

@[continuity, to_additive]
theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x • g x :=
  continuous_smul.comp (hf.prod_mk hg)

@[to_additive]
theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous fun x => c • g x :=
  continuous_smul.comp (continuous_const.prod_mk hg)

/-- If a scalar is central, then its right action is continuous when its left action is. -/
instance HasContinuousSmul.op [HasScalar (Mᵐᵒᵖ) α] [IsCentralScalar M α] : HasContinuousSmul (Mᵐᵒᵖ) α :=
  ⟨by
    suffices Continuous fun p : M × α => MulOpposite.op p.fst • p.snd from
      this.comp (continuous_unop.prod_map continuous_id)
    simpa only [op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × α => _)⟩

end HasScalar

section Monoidₓ

variable [Monoidₓ M] [MulAction M α] [HasContinuousSmul M α]

instance Units.has_continuous_smul : HasContinuousSmul (M)ˣ α where
  continuous_smul :=
    show Continuous ((fun p : M × α => p.fst • p.snd) ∘ fun p : (M)ˣ × α => (p.1, p.2)) from
      continuous_smul.comp ((Units.continuous_coe.comp continuous_fst).prod_mk continuous_snd)

@[to_additive]
theorem smul_closure_subset (c : M) (s : Set α) : c • Closure s ⊆ Closure (c • s) :=
  ((Set.maps_to_image _ _).closure <| continuous_id.const_smul c).image_subset

@[to_additive]
theorem smul_closure_orbit_subset (c : M) (x : α) : c • Closure (MulAction.Orbit M x) ⊆ Closure (MulAction.Orbit M x) :=
  (smul_closure_subset c _).trans <| closure_mono <| MulAction.smul_orbit_subset _ _

end Monoidₓ

section Groupₓ

variable {G : Type _} [TopologicalSpace G] [Groupₓ G] [MulAction G α] [HasContinuousSmul G α]

@[to_additive]
theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} (c : G) :
    tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ tendsto f l (𝓝 a) :=
  ⟨fun h => by
    simpa only [inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩

variable [TopologicalSpace β] {f : β → α} {b : β} {s : Set β}

@[to_additive]
theorem continuous_within_at_const_smul_iff (c : G) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff c

@[to_additive]
theorem continuous_on_const_smul_iff (c : G) : ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  forall₂_congrₓ fun b hb => continuous_within_at_const_smul_iff c

@[to_additive]
theorem continuous_at_const_smul_iff (c : G) : ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  tendsto_const_smul_iff c

@[to_additive]
theorem continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Continuous f := by
  simp only [continuous_iff_continuous_at, continuous_at_const_smul_iff]

@[to_additive]
theorem is_open_map_smul (c : G) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smul c).IsOpenMap

@[to_additive]
theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
  is_open_map_smul c s hs

@[to_additive]
theorem is_closed_map_smul (c : G) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smul c).IsClosedMap

@[to_additive]
theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
  is_closed_map_smul c s hs

end Groupₓ

section GroupWithZeroₓ

variable {G₀ : Type _} [TopologicalSpace G₀] [GroupWithZeroₓ G₀] [MulAction G₀ α] [HasContinuousSmul G₀ α]

theorem tendsto_const_smul_iff₀ {f : β → α} {l : Filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
    tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff (Units.mk0 c hc)

variable [TopologicalSpace β] {f : β → α} {b : β} {c : G₀} {s : Set β}

theorem continuous_within_at_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff (Units.mk0 c hc)

theorem continuous_on_const_smul_iff₀ (hc : c ≠ 0) : ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuous_on_const_smul_iff (Units.mk0 c hc)

theorem continuous_at_const_smul_iff₀ (hc : c ≠ 0) : ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuous_at_const_smul_iff (Units.mk0 c hc)

theorem continuous_const_smul_iff₀ (hc : c ≠ 0) : (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff (Units.mk0 c hc)

/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
protected def Homeomorph.smulOfNeZero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
  Homeomorph.smul (Units.mk0 c hc)

theorem is_open_map_smul₀ {c : G₀} (hc : c ≠ 0) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).IsOpenMap

theorem IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c ≠ 0) : IsOpen (c • s) :=
  is_open_map_smul₀ hc s hs

theorem interior_smul₀ {c : G₀} (hc : c ≠ 0) (s : Set α) : Interior (c • s) = c • Interior s :=
  ((Homeomorph.smulOfNeZero c hc).image_interior s).symm

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem is_closed_map_smul_of_ne_zero {c : G₀} (hc : c ≠ 0) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).IsClosedMap

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem is_closed_map_smul₀ {𝕜 M : Type _} [DivisionRing 𝕜] [AddCommMonoidₓ M] [TopologicalSpace M] [T1Space M]
    [Module 𝕜 M] [TopologicalSpace 𝕜] [HasContinuousSmul 𝕜 M] (c : 𝕜) : IsClosedMap fun x : M => c • x := by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [zero_smul]
    exact is_closed_map_const
    
  · exact (Homeomorph.smulOfNeZero c hne).IsClosedMap
    

end GroupWithZeroₓ

namespace IsUnit

variable [Monoidₓ M] [MulAction M α] [HasContinuousSmul M α]

theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} {c : M} (hc : IsUnit c) :
    tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ tendsto f l (𝓝 a) :=
  let ⟨u, hu⟩ := hc
  hu ▸ tendsto_const_smul_iff u

variable [TopologicalSpace β] {f : β → α} {b : β} {c : M} {s : Set β}

theorem continuous_within_at_const_smul_iff (hc : IsUnit c) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_within_at_const_smul_iff u

theorem continuous_on_const_smul_iff (hc : IsUnit c) : ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_on_const_smul_iff u

theorem continuous_at_const_smul_iff (hc : IsUnit c) : ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_at_const_smul_iff u

theorem continuous_const_smul_iff (hc : IsUnit c) : (Continuous fun x => c • f x) ↔ Continuous f :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_const_smul_iff u

theorem is_open_map_smul (hc : IsUnit c) : IsOpenMap fun x : α => c • x :=
  let ⟨u, hu⟩ := hc
  hu ▸ is_open_map_smul u

theorem is_closed_map_smul (hc : IsUnit c) : IsClosedMap fun x : α => c • x :=
  let ⟨u, hu⟩ := hc
  hu ▸ is_closed_map_smul u

end IsUnit

@[to_additive]
instance HasContinuousMul.has_continuous_smul {M : Type _} [Monoidₓ M] [TopologicalSpace M] [HasContinuousMul M] :
    HasContinuousSmul M M :=
  ⟨continuous_mul⟩

@[to_additive]
instance [TopologicalSpace β] [HasScalar M α] [HasScalar M β] [HasContinuousSmul M α] [HasContinuousSmul M β] :
    HasContinuousSmul M (α × β) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type _} {γ : ι → Type _} [∀ i, TopologicalSpace (γ i)] [∀ i, HasScalar M (γ i)]
    [∀ i, HasContinuousSmul M (γ i)] : HasContinuousSmul M (∀ i, γ i) :=
  ⟨continuous_pi fun i =>
      (continuous_fst.smul continuous_snd).comp <| continuous_fst.prod_mk ((continuous_apply i).comp continuous_snd)⟩

