/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathbin.Geometry.Manifold.ContMdiffMap

/-!
# Smooth monoid
A smooth monoid is a monoid that is also a smooth manifold, in which multiplication is a smooth map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about smooth monoids: `has_smooth_mul` and its
additive counterpart `has_smooth_add`. These structures are general enough to also talk about smooth
semigroups.
-/


open Manifold

library_note "Design choices about smooth algebraic structures"/--
1. All smooth algebraic structures on `G` are `Prop`-valued classes that extend
`smooth_manifold_with_corners I G`. This way we save users from adding both
`[smooth_manifold_with_corners I G]` and `[has_smooth_mul I G]` to the assumptions. While many API
lemmas hold true without the `smooth_manifold_with_corners I G` assumption, we're not aware of a
mathematically interesting monoid on a topological manifold such that (a) the space is not a
`smooth_manifold_with_corners`; (b) the multiplication is smooth at `(a, b)` in the charts
`ext_chart_at I a`, `ext_chart_at I b`, `ext_chart_at I (a * b)`.

2. Because of `model_prod` we can't assume, e.g., that a `lie_group` is modelled on `𝓘(𝕜, E)`. So,
we formulate the definitions and lemmas for any model.

3. While smoothness of an operation implies its continuity, lemmas like
`has_continuous_mul_of_smooth` can't be instances becausen otherwise Lean would have to search for
`has_smooth_mul I G` with unknown `𝕜`, `E`, `H`, and `I : model_with_corners 𝕜 E H`. If users needs
`[has_continuous_mul G]` in a proof about a smooth monoid, then they need to either add
`[has_continuous_mul G]` as an assumption (worse) or use `haveI` in the proof (better). -/


-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a smooth (Lie) additive monoid or a smooth additive
semigroup. A smooth additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_smooth_add α`. -/
@[ancestor SmoothManifoldWithCorners]
class HasSmoothAdd {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type _) [Add G] [TopologicalSpace G]
  [ChartedSpace H G] extends SmoothManifoldWithCorners I G : Prop where
  smooth_add : Smooth (I.Prod I) I fun p : G × G => p.1 + p.2

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a smooth (Lie) monoid or a smooth semigroup.
A smooth monoid over `G`, for example, is obtained by requiring both the instances `monoid G`
and `has_smooth_mul I G`. -/
@[ancestor SmoothManifoldWithCorners, to_additive]
class HasSmoothMul {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type _) [Mul G] [TopologicalSpace G]
  [ChartedSpace H G] extends SmoothManifoldWithCorners I G : Prop where
  smooth_mul : Smooth (I.Prod I) I fun p : G × G => p.1 * p.2

section HasSmoothMul

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [Mul G] [TopologicalSpace G] [ChartedSpace H G]
  [HasSmoothMul I G] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type _} [TopologicalSpace M] [ChartedSpace H' M]

section

variable (I)

@[to_additive]
theorem smooth_mul : Smooth (I.Prod I) I fun p : G × G => p.1 * p.2 :=
  HasSmoothMul.smooth_mul

/-- If the multiplication is smooth, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive
      "If the addition is smooth, then it is continuous. This is not an instance for technical reasons,\nsee note [Design choices about smooth algebraic structures]."]
theorem has_continuous_mul_of_smooth : HasContinuousMul G :=
  ⟨(smooth_mul I).Continuous⟩

end

section

variable {f g : M → G} {s : Set M} {x : M} {n : ℕ∞}

@[to_additive]
theorem ContMdiffWithinAt.mul (hf : ContMdiffWithinAt I' I n f s x) (hg : ContMdiffWithinAt I' I n g s x) :
    ContMdiffWithinAt I' I n (f * g) s x :=
  ((smooth_mul I).SmoothAt.of_le le_top).comp_cont_mdiff_within_at x (hf.prod_mk hg)

@[to_additive]
theorem ContMdiffAt.mul (hf : ContMdiffAt I' I n f x) (hg : ContMdiffAt I' I n g x) : ContMdiffAt I' I n (f * g) x :=
  hf.mul hg

@[to_additive]
theorem ContMdiffOn.mul (hf : ContMdiffOn I' I n f s) (hg : ContMdiffOn I' I n g s) : ContMdiffOn I' I n (f * g) s :=
  fun x hx => (hf x hx).mul (hg x hx)

@[to_additive]
theorem ContMdiff.mul (hf : ContMdiff I' I n f) (hg : ContMdiff I' I n g) : ContMdiff I' I n (f * g) := fun x =>
  (hf x).mul (hg x)

@[to_additive]
theorem SmoothWithinAt.mul (hf : SmoothWithinAt I' I f s x) (hg : SmoothWithinAt I' I g s x) :
    SmoothWithinAt I' I (f * g) s x :=
  hf.mul hg

@[to_additive]
theorem SmoothAt.mul (hf : SmoothAt I' I f x) (hg : SmoothAt I' I g x) : SmoothAt I' I (f * g) x :=
  hf.mul hg

@[to_additive]
theorem SmoothOn.mul (hf : SmoothOn I' I f s) (hg : SmoothOn I' I g s) : SmoothOn I' I (f * g) s :=
  hf.mul hg

@[to_additive]
theorem Smooth.mul (hf : Smooth I' I f) (hg : Smooth I' I g) : Smooth I' I (f * g) :=
  hf.mul hg

@[to_additive]
theorem smooth_mul_left {a : G} : Smooth I I fun b : G => a * b :=
  smooth_const.mul smooth_id

@[to_additive]
theorem smooth_mul_right {a : G} : Smooth I I fun b : G => b * a :=
  smooth_id.mul smooth_const

end

variable (I) (g h : G)

/-- Left multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smooth_left_mul` with the notation `𝑳` usually use `L` instead of `𝑳` in the
names. -/
def smoothLeftMul : C^∞⟮I, G; I, G⟯ :=
  ⟨leftMul g, smooth_mul_left⟩

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smooth_right_mul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨rightMul g, smooth_mul_right⟩

-- mathport name: «expr𝑳»
-- Left multiplication. The abbreviation is `MIL`.
localized [LieGroup] notation "𝑳" => smoothLeftMul

-- mathport name: «expr𝑹»
-- Right multiplication. The abbreviation is `MIR`.
localized [LieGroup] notation "𝑹" => smoothRightMul

open LieGroup

@[simp]
theorem L_apply : (𝑳 I g) h = g * h :=
  rfl

@[simp]
theorem R_apply : (𝑹 I g) h = h * g :=
  rfl

@[simp]
theorem L_mul {G : Type _} [Semigroupₓ G] [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G] (g h : G) :
    𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) := by
  ext
  simp only [ContMdiffMap.comp_apply, L_apply, mul_assoc]

@[simp]
theorem R_mul {G : Type _} [Semigroupₓ G] [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G] (g h : G) :
    𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) := by
  ext
  simp only [ContMdiffMap.comp_apply, R_apply, mul_assoc]

section

variable {G' : Type _} [Monoidₓ G'] [TopologicalSpace G'] [ChartedSpace H G'] [HasSmoothMul I G'] (g' : G')

theorem smooth_left_mul_one : (𝑳 I g') 1 = g' :=
  mul_oneₓ g'

theorem smooth_right_mul_one : (𝑹 I g') 1 = g' :=
  one_mulₓ g'

end

-- Instance of product
@[to_additive]
instance HasSmoothMul.prod {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (G : Type _) [TopologicalSpace G]
    [ChartedSpace H G] [Mul G] [HasSmoothMul I G] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _}
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (G' : Type _) [TopologicalSpace G'] [ChartedSpace H' G']
    [Mul G'] [HasSmoothMul I' G'] : HasSmoothMul (I.Prod I') (G × G') :=
  { SmoothManifoldWithCorners.prod G G' with
    smooth_mul :=
      ((smooth_fst.comp smooth_fst).Smooth.mul (smooth_fst.comp smooth_snd)).prod_mk
        ((smooth_snd.comp smooth_fst).Smooth.mul (smooth_snd.comp smooth_snd)) }

end HasSmoothMul

section Monoidₓ

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [Monoidₓ G] [TopologicalSpace G] [ChartedSpace H G]
  [HasSmoothMul I G] {H' : Type _} [TopologicalSpace H'] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'} {G' : Type _} [Monoidₓ G'] [TopologicalSpace G'] [ChartedSpace H' G']
  [HasSmoothMul I' G']

theorem smooth_pow : ∀ n : ℕ, Smooth I I fun a : G => a ^ n
  | 0 => by
    simp only [pow_zeroₓ]
    exact smooth_const
  | k + 1 => by
    simpa [pow_succₓ] using smooth_id.mul (smooth_pow _)

/-- Morphism of additive smooth monoids. -/
structure SmoothAddMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') (G : Type _)
  [TopologicalSpace G] [ChartedSpace H G] [AddMonoidₓ G] [HasSmoothAdd I G] (G' : Type _) [TopologicalSpace G']
  [ChartedSpace H' G'] [AddMonoidₓ G'] [HasSmoothAdd I' G'] extends G →+ G' where
  smooth_to_fun : Smooth I I' to_fun

/-- Morphism of smooth monoids. -/
@[to_additive]
structure SmoothMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') (G : Type _)
  [TopologicalSpace G] [ChartedSpace H G] [Monoidₓ G] [HasSmoothMul I G] (G' : Type _) [TopologicalSpace G']
  [ChartedSpace H' G'] [Monoidₓ G'] [HasSmoothMul I' G'] extends G →* G' where
  smooth_to_fun : Smooth I I' to_fun

@[to_additive]
instance : One (SmoothMonoidMorphism I I' G G') :=
  ⟨{ smooth_to_fun := smooth_const, toMonoidHom := 1 }⟩

@[to_additive]
instance : Inhabited (SmoothMonoidMorphism I I' G G') :=
  ⟨1⟩

@[to_additive]
instance : CoeFun (SmoothMonoidMorphism I I' G G') fun _ => G → G' :=
  ⟨fun a => a.toFun⟩

end Monoidₓ

section CommMonoidₓ

open BigOperators

variable {ι 𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [CommMonoidₓ G]
  [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H' M] {s : Set M} {x : M} {t : Finset ι} {f : ι → M → G} {n : ℕ∞} {p : ι → Prop}

@[to_additive]
theorem cont_mdiff_within_at_finset_prod' (h : ∀ i ∈ t, ContMdiffWithinAt I' I n (f i) s x) :
    ContMdiffWithinAt I' I n (∏ i in t, f i) s x :=
  Finset.prod_induction f (fun f => ContMdiffWithinAt I' I n f s x) (fun f g hf hg => hf.mul hg)
    cont_mdiff_within_at_const h

@[to_additive]
theorem cont_mdiff_at_finset_prod' (h : ∀ i ∈ t, ContMdiffAt I' I n (f i) x) : ContMdiffAt I' I n (∏ i in t, f i) x :=
  cont_mdiff_within_at_finset_prod' h

@[to_additive]
theorem cont_mdiff_on_finset_prod' (h : ∀ i ∈ t, ContMdiffOn I' I n (f i) s) : ContMdiffOn I' I n (∏ i in t, f i) s :=
  fun x hx => cont_mdiff_within_at_finset_prod' fun i hi => h i hi x hx

@[to_additive]
theorem cont_mdiff_finset_prod' (h : ∀ i ∈ t, ContMdiff I' I n (f i)) : ContMdiff I' I n (∏ i in t, f i) := fun x =>
  cont_mdiff_at_finset_prod' fun i hi => h i hi x

@[to_additive]
theorem cont_mdiff_within_at_finset_prod (h : ∀ i ∈ t, ContMdiffWithinAt I' I n (f i) s x) :
    ContMdiffWithinAt I' I n (fun x => ∏ i in t, f i x) s x := by
  simp only [← Finset.prod_apply]
  exact cont_mdiff_within_at_finset_prod' h

@[to_additive]
theorem cont_mdiff_at_finset_prod (h : ∀ i ∈ t, ContMdiffAt I' I n (f i) x) :
    ContMdiffAt I' I n (fun x => ∏ i in t, f i x) x :=
  cont_mdiff_within_at_finset_prod h

@[to_additive]
theorem cont_mdiff_on_finset_prod (h : ∀ i ∈ t, ContMdiffOn I' I n (f i) s) :
    ContMdiffOn I' I n (fun x => ∏ i in t, f i x) s := fun x hx =>
  cont_mdiff_within_at_finset_prod fun i hi => h i hi x hx

@[to_additive]
theorem cont_mdiff_finset_prod (h : ∀ i ∈ t, ContMdiff I' I n (f i)) : ContMdiff I' I n fun x => ∏ i in t, f i x :=
  fun x => cont_mdiff_at_finset_prod fun i hi => h i hi x

@[to_additive]
theorem smooth_within_at_finset_prod' (h : ∀ i ∈ t, SmoothWithinAt I' I (f i) s x) :
    SmoothWithinAt I' I (∏ i in t, f i) s x :=
  cont_mdiff_within_at_finset_prod' h

@[to_additive]
theorem smooth_at_finset_prod' (h : ∀ i ∈ t, SmoothAt I' I (f i) x) : SmoothAt I' I (∏ i in t, f i) x :=
  cont_mdiff_at_finset_prod' h

@[to_additive]
theorem smooth_on_finset_prod' (h : ∀ i ∈ t, SmoothOn I' I (f i) s) : SmoothOn I' I (∏ i in t, f i) s :=
  cont_mdiff_on_finset_prod' h

@[to_additive]
theorem smooth_finset_prod' (h : ∀ i ∈ t, Smooth I' I (f i)) : Smooth I' I (∏ i in t, f i) :=
  cont_mdiff_finset_prod' h

@[to_additive]
theorem smooth_within_at_finset_prod (h : ∀ i ∈ t, SmoothWithinAt I' I (f i) s x) :
    SmoothWithinAt I' I (fun x => ∏ i in t, f i x) s x :=
  cont_mdiff_within_at_finset_prod h

@[to_additive]
theorem smooth_at_finset_prod (h : ∀ i ∈ t, SmoothAt I' I (f i) x) : SmoothAt I' I (fun x => ∏ i in t, f i x) x :=
  cont_mdiff_at_finset_prod h

@[to_additive]
theorem smooth_on_finset_prod (h : ∀ i ∈ t, SmoothOn I' I (f i) s) : SmoothOn I' I (fun x => ∏ i in t, f i x) s :=
  cont_mdiff_on_finset_prod h

@[to_additive]
theorem smooth_finset_prod (h : ∀ i ∈ t, Smooth I' I (f i)) : Smooth I' I fun x => ∏ i in t, f i x :=
  cont_mdiff_finset_prod h

open Function Filter

@[to_additive]
theorem cont_mdiff_finprod (h : ∀ i, ContMdiff I' I n (f i)) (hfin : LocallyFinite fun i => MulSupport (f i)) :
    ContMdiff I' I n fun x => ∏ᶠ i, f i x := by
  intro x
  rcases finprod_eventually_eq_prod hfin x with ⟨s, hs⟩
  exact (cont_mdiff_finset_prod (fun i hi => h i) x).congr_of_eventually_eq hs

@[to_additive]
theorem cont_mdiff_finprod_cond (hc : ∀ i, p i → ContMdiff I' I n (f i))
    (hf : LocallyFinite fun i => MulSupport (f i)) : ContMdiff I' I n fun x => ∏ᶠ (i) (hi : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact cont_mdiff_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

@[to_additive]
theorem smooth_finprod (h : ∀ i, Smooth I' I (f i)) (hfin : LocallyFinite fun i => MulSupport (f i)) :
    Smooth I' I fun x => ∏ᶠ i, f i x :=
  cont_mdiff_finprod h hfin

@[to_additive]
theorem smooth_finprod_cond (hc : ∀ i, p i → Smooth I' I (f i)) (hf : LocallyFinite fun i => MulSupport (f i)) :
    Smooth I' I fun x => ∏ᶠ (i) (hi : p i), f i x :=
  cont_mdiff_finprod_cond hc hf

end CommMonoidₓ

