import Mathbin.Topology.Algebra.Monoid 
import Mathbin.GroupTheory.GroupAction.Prod 
import Mathbin.GroupTheory.GroupAction.Basic 
import Mathbin.Topology.Homeomorph

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
* `units.has_continuous_smul`: scalar multiplication by `units M` is continuous when scalar
  multiplication by `M` is continuous. This allows `homeomorph.smul` to be used with on monoids
  with `G = units M`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `continuous.smul`
or `filter.tendsto.smul` that provide dot-syntax access to `continuous_smul`.
-/


open_locale TopologicalSpace Pointwise

open Filter

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Class `has_continuous_smul M α` says that the scalar multiplication `(•) : M → α → α`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class has_continuous_smul
(M α : Type*)
[has_scalar M α]
[topological_space M]
[topological_space α] : exprProp() := (continuous_smul : continuous (λ p : «expr × »(M, α), «expr • »(p.1, p.2)))

export HasContinuousSmul(continuous_smul)

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Class `has_continuous_vadd M α` says that the additive action `(+ᵥ) : M → α → α`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class has_continuous_vadd
(M α : Type*)
[has_vadd M α]
[topological_space M]
[topological_space α] : exprProp() := (continuous_vadd : continuous (λ p : «expr × »(M, α), «expr +ᵥ »(p.1, p.2)))

export HasContinuousVadd(continuous_vadd)

attribute [toAdditive] HasContinuousSmul

variable{M α β : Type _}[TopologicalSpace M][TopologicalSpace α]

section HasScalar

variable[HasScalar M α][HasContinuousSmul M α]

@[toAdditive]
theorem Filter.Tendsto.smul {f : β → M} {g : β → α} {l : Filter β} {c : M} {a : α} (hf : tendsto f l (𝓝 c))
  (hg : tendsto g l (𝓝 a)) : tendsto (fun x => f x • g x) l (𝓝$ c • a) :=
  (continuous_smul.Tendsto _).comp (hf.prod_mk_nhds hg)

@[toAdditive]
theorem Filter.Tendsto.const_smul {f : β → α} {l : Filter β} {a : α} (hf : tendsto f l (𝓝 a)) (c : M) :
  tendsto (fun x => c • f x) l (𝓝 (c • a)) :=
  tendsto_const_nhds.smul hf

@[toAdditive]
theorem Filter.Tendsto.smul_const {f : β → M} {l : Filter β} {c : M} (hf : tendsto f l (𝓝 c)) (a : α) :
  tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.smul tendsto_const_nhds

variable[TopologicalSpace β]{f : β → M}{g : β → α}{b : β}{s : Set β}

@[toAdditive]
theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
  ContinuousWithinAt (fun x => f x • g x) s b :=
  hf.smul hg

@[toAdditive]
theorem ContinuousWithinAt.const_smul (hg : ContinuousWithinAt g s b) (c : M) :
  ContinuousWithinAt (fun x => c • g x) s b :=
  hg.const_smul c

@[toAdditive]
theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) : ContinuousAt (fun x => f x • g x) b :=
  hf.smul hg

@[toAdditive]
theorem ContinuousAt.const_smul (hg : ContinuousAt g b) (c : M) : ContinuousAt (fun x => c • g x) b :=
  hg.const_smul c

@[toAdditive]
theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => f x • g x) s :=
  fun x hx => (hf x hx).smul (hg x hx)

@[toAdditive]
theorem ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) : ContinuousOn (fun x => c • g x) s :=
  fun x hx => (hg x hx).const_smul c

@[continuity, toAdditive]
theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x • g x :=
  continuous_smul.comp (hf.prod_mk hg)

@[toAdditive]
theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous fun x => c • g x :=
  continuous_smul.comp (continuous_const.prod_mk hg)

end HasScalar

section Monoidₓ

variable[Monoidₓ M][MulAction M α][HasContinuousSmul M α]

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance units.has_continuous_smul : has_continuous_smul (units M) α :=
{ continuous_smul := show continuous «expr ∘ »(λ
   p : «expr × »(M, α), «expr • »(p.fst, p.snd), λ
   p : «expr × »(units M, α), (p.1, p.2)), from continuous_smul.comp ((units.continuous_coe.comp continuous_fst).prod_mk continuous_snd) }

@[toAdditive]
theorem smul_closure_subset (c : M) (s : Set α) : c • Closure s ⊆ Closure (c • s) :=
  ((Set.maps_to_image _ _).closure$ continuous_id.const_smul c).image_subset

@[toAdditive]
theorem smul_closure_orbit_subset (c : M) (x : α) : c • Closure (MulAction.Orbit M x) ⊆ Closure (MulAction.Orbit M x) :=
  (smul_closure_subset c _).trans$ closure_mono$ MulAction.smul_orbit_subset _ _

end Monoidₓ

section Groupₓ

variable{G : Type _}[TopologicalSpace G][Groupₓ G][MulAction G α][HasContinuousSmul G α]

@[toAdditive]
theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} (c : G) :
  tendsto (fun x => c • f x) l (𝓝$ c • a) ↔ tendsto f l (𝓝 a) :=
  ⟨fun h =>
      by 
        simpa only [inv_smul_smul] using h.const_smul (c⁻¹),
    fun h => h.const_smul _⟩

variable[TopologicalSpace β]{f : β → α}{b : β}{s : Set β}

@[toAdditive]
theorem continuous_within_at_const_smul_iff (c : G) :
  ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff c

@[toAdditive]
theorem continuous_on_const_smul_iff (c : G) : ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  forall_congrₓ$ fun b => forall_congrₓ$ fun hb => continuous_within_at_const_smul_iff c

@[toAdditive]
theorem continuous_at_const_smul_iff (c : G) : ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  tendsto_const_smul_iff c

@[toAdditive]
theorem continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Continuous f :=
  by 
    simp only [continuous_iff_continuous_at, continuous_at_const_smul_iff]

/-- Scalar multiplication by an element of a group `G` acting on `α` is a homeomorphism from `α`
to itself. -/
protected def Homeomorph.smul (c : G) : α ≃ₜ α :=
  { toEquiv := MulAction.toPermHom G α c, continuous_to_fun := continuous_id.const_smul _,
    continuous_inv_fun := continuous_id.const_smul _ }

/-- Affine-addition of an element of an additive group `G` acting on `α` is a homeomorphism
from `α` to itself. -/
protected def Homeomorph.vadd {G : Type _} [TopologicalSpace G] [AddGroupₓ G] [AddAction G α] [HasContinuousVadd G α]
  (c : G) : α ≃ₜ α :=
  { toEquiv := AddAction.toPermHom α G c, continuous_to_fun := continuous_id.const_vadd _,
    continuous_inv_fun := continuous_id.const_vadd _ }

attribute [toAdditive] Homeomorph.smul

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[to_additive #[]] theorem is_open_map_smul (c : G) : is_open_map (λ x : α, «expr • »(c, x)) :=
(homeomorph.smul c).is_open_map

@[toAdditive]
theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
  is_open_map_smul c s hs

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[to_additive #[]] theorem is_closed_map_smul (c : G) : is_closed_map (λ x : α, «expr • »(c, x)) :=
(homeomorph.smul c).is_closed_map

@[toAdditive]
theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
  is_closed_map_smul c s hs

end Groupₓ

section GroupWithZeroₓ

variable{G₀ : Type _}[TopologicalSpace G₀][GroupWithZeroₓ G₀][MulAction G₀ α][HasContinuousSmul G₀ α]

theorem tendsto_const_smul_iff₀ {f : β → α} {l : Filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
  tendsto (fun x => c • f x) l (𝓝$ c • a) ↔ tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff (Units.mk0 c hc)

variable[TopologicalSpace β]{f : β → α}{b : β}{c : G₀}{s : Set β}

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

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_open_map_smul₀ {c : G₀} (hc : «expr ≠ »(c, 0)) : is_open_map (λ x : α, «expr • »(c, x)) :=
(homeomorph.smul_of_ne_zero c hc).is_open_map

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem is_closed_map_smul_of_ne_zero {c : G₀} (hc : «expr ≠ »(c, 0)) : is_closed_map (λ x : α, «expr • »(c, x)) :=
(homeomorph.smul_of_ne_zero c hc).is_closed_map

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem is_closed_map_smul₀
{𝕜 M : Type*}
[division_ring 𝕜]
[add_comm_monoid M]
[topological_space M]
[t1_space M]
[module 𝕜 M]
[topological_space 𝕜]
[has_continuous_smul 𝕜 M]
(c : 𝕜) : is_closed_map (λ x : M, «expr • »(c, x)) :=
begin
  rcases [expr eq_or_ne c 0, "with", "(", ident rfl, "|", ident hne, ")"],
  { simp [] [] ["only"] ["[", expr zero_smul, "]"] [] [],
    exact [expr is_closed_map_const] },
  { exact [expr (homeomorph.smul_of_ne_zero c hne).is_closed_map] }
end

end GroupWithZeroₓ

namespace IsUnit

variable[Monoidₓ M][MulAction M α][HasContinuousSmul M α]

theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} {c : M} (hc : IsUnit c) :
  tendsto (fun x => c • f x) l (𝓝$ c • a) ↔ tendsto f l (𝓝 a) :=
  let ⟨u, hu⟩ := hc 
  hu ▸ tendsto_const_smul_iff u

variable[TopologicalSpace β]{f : β → α}{b : β}{c : M}{s : Set β}

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

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_open_map_smul (hc : is_unit c) : is_open_map (λ x : α, «expr • »(c, x)) :=
let ⟨u, hu⟩ := hc in
«expr ▸ »(hu, is_open_map_smul u)

-- error in Topology.Algebra.MulAction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem is_closed_map_smul (hc : is_unit c) : is_closed_map (λ x : α, «expr • »(c, x)) :=
let ⟨u, hu⟩ := hc in
«expr ▸ »(hu, is_closed_map_smul u)

end IsUnit

@[toAdditive]
instance HasContinuousMul.has_continuous_smul {M : Type _} [Monoidₓ M] [TopologicalSpace M] [HasContinuousMul M] :
  HasContinuousSmul M M :=
  ⟨continuous_mul⟩

@[toAdditive]
instance  [TopologicalSpace β] [HasScalar M α] [HasScalar M β] [HasContinuousSmul M α] [HasContinuousSmul M β] :
  HasContinuousSmul M (α × β) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[toAdditive]
instance  {ι : Type _} {γ : ι → Type} [∀ i, TopologicalSpace (γ i)] [∀ i, HasScalar M (γ i)]
  [∀ i, HasContinuousSmul M (γ i)] : HasContinuousSmul M (∀ i, γ i) :=
  ⟨continuous_pi$
      fun i =>
        (continuous_fst.smul continuous_snd).comp$ continuous_fst.prod_mk ((continuous_apply i).comp continuous_snd)⟩

