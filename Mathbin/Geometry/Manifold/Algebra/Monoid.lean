/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module geometry.manifold.algebra.monoid
! leanprover-community/mathlib commit 3d7987cda72abc473c7cdbbb075170e9ac620042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
class HasSmoothAdd {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H]
  {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type _)
  [Add G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothManifoldWithCorners I G : Prop where
  smooth_add : Smooth (I.Prod I) I fun p : G × G => p.1 + p.2
#align has_smooth_add HasSmoothAdd

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a smooth (Lie) monoid or a smooth semigroup.
A smooth monoid over `G`, for example, is obtained by requiring both the instances `monoid G`
and `has_smooth_mul I G`. -/
@[to_additive]
class HasSmoothMul {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H]
  {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type _)
  [Mul G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothManifoldWithCorners I G : Prop where
  smooth_mul : Smooth (I.Prod I) I fun p : G × G => p.1 * p.2
#align has_smooth_mul HasSmoothMul
#align has_smooth_add HasSmoothAdd

section HasSmoothMul

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [Mul G]
  [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G] {E' : Type _} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type _} [TopologicalSpace M] [ChartedSpace H' M]

section

variable (I)

@[to_additive]
theorem smooth_mul : Smooth (I.Prod I) I fun p : G × G => p.1 * p.2 :=
  HasSmoothMul.smooth_mul
#align smooth_mul smooth_mul
#align smooth_add smooth_add

/-- If the multiplication is smooth, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive
      "If the addition is smooth, then it is continuous. This is not an instance for technical reasons,\nsee note [Design choices about smooth algebraic structures]."]
theorem continuousMul_of_smooth : ContinuousMul G :=
  ⟨(smooth_mul I).Continuous⟩
#align has_continuous_mul_of_smooth continuousMul_of_smooth
#align has_continuous_add_of_smooth has_continuous_add_of_smooth

end

section

variable {f g : M → G} {s : Set M} {x : M} {n : ℕ∞}

@[to_additive]
theorem ContMdiffWithinAt.mul (hf : ContMdiffWithinAt I' I n f s x)
    (hg : ContMdiffWithinAt I' I n g s x) : ContMdiffWithinAt I' I n (f * g) s x :=
  ((smooth_mul I).SmoothAt.of_le le_top).comp_contMdiffWithinAt x (hf.prod_mk hg)
#align cont_mdiff_within_at.mul ContMdiffWithinAt.mul
#align cont_mdiff_within_at.add ContMdiffWithinAt.add

@[to_additive]
theorem ContMdiffAt.mul (hf : ContMdiffAt I' I n f x) (hg : ContMdiffAt I' I n g x) :
    ContMdiffAt I' I n (f * g) x :=
  hf.mul hg
#align cont_mdiff_at.mul ContMdiffAt.mul
#align cont_mdiff_at.add ContMdiffAt.add

@[to_additive]
theorem ContMdiffOn.mul (hf : ContMdiffOn I' I n f s) (hg : ContMdiffOn I' I n g s) :
    ContMdiffOn I' I n (f * g) s := fun x hx => (hf x hx).mul (hg x hx)
#align cont_mdiff_on.mul ContMdiffOn.mul
#align cont_mdiff_on.add ContMdiffOn.add

@[to_additive]
theorem ContMdiff.mul (hf : ContMdiff I' I n f) (hg : ContMdiff I' I n g) :
    ContMdiff I' I n (f * g) := fun x => (hf x).mul (hg x)
#align cont_mdiff.mul ContMdiff.mul
#align cont_mdiff.add ContMdiff.add

@[to_additive]
theorem SmoothWithinAt.mul (hf : SmoothWithinAt I' I f s x) (hg : SmoothWithinAt I' I g s x) :
    SmoothWithinAt I' I (f * g) s x :=
  hf.mul hg
#align smooth_within_at.mul SmoothWithinAt.mul
#align smooth_within_at.add SmoothWithinAt.add

@[to_additive]
theorem SmoothAt.mul (hf : SmoothAt I' I f x) (hg : SmoothAt I' I g x) : SmoothAt I' I (f * g) x :=
  hf.mul hg
#align smooth_at.mul SmoothAt.mul
#align smooth_at.add SmoothAt.add

@[to_additive]
theorem SmoothOn.mul (hf : SmoothOn I' I f s) (hg : SmoothOn I' I g s) : SmoothOn I' I (f * g) s :=
  hf.mul hg
#align smooth_on.mul SmoothOn.mul
#align smooth_on.add SmoothOn.add

@[to_additive]
theorem Smooth.mul (hf : Smooth I' I f) (hg : Smooth I' I g) : Smooth I' I (f * g) :=
  hf.mul hg
#align smooth.mul Smooth.mul
#align smooth.add Smooth.add

@[to_additive]
theorem smooth_mul_left {a : G} : Smooth I I fun b : G => a * b :=
  smooth_const.mul smooth_id
#align smooth_mul_left smooth_mul_left
#align smooth_add_left smooth_add_left

@[to_additive]
theorem smooth_mul_right {a : G} : Smooth I I fun b : G => b * a :=
  smooth_id.mul smooth_const
#align smooth_mul_right smooth_mul_right
#align smooth_add_right smooth_add_right

end

variable (I) (g h : G)

/-- Left multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smooth_left_mul` with the notation `𝑳` usually use `L` instead of `𝑳` in the
names. -/
def smoothLeftMul : C^∞⟮I, G; I, G⟯ :=
  ⟨leftMul g, smooth_mul_left⟩
#align smooth_left_mul smoothLeftMul

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smooth_right_mul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨rightMul g, smooth_mul_right⟩
#align smooth_right_mul smoothRightMul

-- mathport name: smooth_left_mul
-- Left multiplication. The abbreviation is `MIL`.
scoped[LieGroup] notation "𝑳" => smoothLeftMul

-- mathport name: smooth_right_mul
-- Right multiplication. The abbreviation is `MIR`.
scoped[LieGroup] notation "𝑹" => smoothRightMul

open LieGroup

@[simp]
theorem L_apply : (𝑳 I g) h = g * h :=
  rfl
#align L_apply L_apply

@[simp]
theorem R_apply : (𝑹 I g) h = h * g :=
  rfl
#align R_apply R_apply

@[simp]
theorem L_mul {G : Type _} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G]
    (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) :=
  by
  ext
  simp only [ContMdiffMap.comp_apply, L_apply, mul_assoc]
#align L_mul L_mul

@[simp]
theorem R_mul {G : Type _} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G]
    (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) :=
  by
  ext
  simp only [ContMdiffMap.comp_apply, R_apply, mul_assoc]
#align R_mul R_mul

section

variable {G' : Type _} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H G'] [HasSmoothMul I G']
  (g' : G')

theorem smoothLeftMul_one : (𝑳 I g') 1 = g' :=
  mul_one g'
#align smooth_left_mul_one smoothLeftMul_one

theorem smoothRightMul_one : (𝑹 I g') 1 = g' :=
  one_mul g'
#align smooth_right_mul_one smoothRightMul_one

end

-- Instance of product
@[to_additive]
instance HasSmoothMul.prod {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (G : Type _) [TopologicalSpace G] [ChartedSpace H G] [Mul G]
    [HasSmoothMul I G] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _}
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (G' : Type _) [TopologicalSpace G']
    [ChartedSpace H' G'] [Mul G'] [HasSmoothMul I' G'] : HasSmoothMul (I.Prod I') (G × G') :=
  { SmoothManifoldWithCorners.prod G G' with
    smooth_mul :=
      ((smooth_fst.comp smooth_fst).Smooth.mul (smooth_fst.comp smooth_snd)).prod_mk
        ((smooth_snd.comp smooth_fst).Smooth.mul (smooth_snd.comp smooth_snd)) }
#align has_smooth_mul.prod HasSmoothMul.prod
#align has_smooth_add.sum HasSmoothAdd.sum

end HasSmoothMul

section Monoid

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [Monoid G]
  [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G] {H' : Type _} [TopologicalSpace H']
  {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type _} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G'] [HasSmoothMul I' G']

theorem smooth_pow : ∀ n : ℕ, Smooth I I fun a : G => a ^ n
  | 0 => by
    simp only [pow_zero]
    exact smooth_const
  | k + 1 => by simpa [pow_succ] using smooth_id.mul (smooth_pow _)
#align smooth_pow smooth_pow

/-- Morphism of additive smooth monoids. -/
structure SmoothAddMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  (G : Type _) [TopologicalSpace G] [ChartedSpace H G] [AddMonoid G] [HasSmoothAdd I G]
  (G' : Type _) [TopologicalSpace G'] [ChartedSpace H' G'] [AddMonoid G']
  [HasSmoothAdd I' G'] extends G →+ G' where
  smooth_toFun : Smooth I I' to_fun
#align smooth_add_monoid_morphism SmoothAddMonoidMorphism

/-- Morphism of smooth monoids. -/
@[to_additive]
structure SmoothMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  (G : Type _) [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [HasSmoothMul I G] (G' : Type _)
  [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G'] [HasSmoothMul I' G'] extends G →* G' where
  smooth_toFun : Smooth I I' to_fun
#align smooth_monoid_morphism SmoothMonoidMorphism
#align smooth_add_monoid_morphism SmoothAddMonoidMorphism

@[to_additive]
instance : One (SmoothMonoidMorphism I I' G G') :=
  ⟨{  smooth_toFun := smooth_const
      toMonoidHom := 1 }⟩

@[to_additive]
instance : Inhabited (SmoothMonoidMorphism I I' G G') :=
  ⟨1⟩

@[to_additive]
instance : CoeFun (SmoothMonoidMorphism I I' G G') fun _ => G → G' :=
  ⟨fun a => a.toFun⟩

end Monoid

section CommMonoid

open BigOperators

variable {ι 𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [CommMonoid G]
  [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G] {E' : Type _} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type _} [TopologicalSpace M] [ChartedSpace H' M] {s : Set M} {x : M} {t : Finset ι}
  {f : ι → M → G} {n : ℕ∞} {p : ι → Prop}

@[to_additive]
theorem contMdiffWithinAt_finset_prod' (h : ∀ i ∈ t, ContMdiffWithinAt I' I n (f i) s x) :
    ContMdiffWithinAt I' I n (∏ i in t, f i) s x :=
  Finset.prod_induction f (fun f => ContMdiffWithinAt I' I n f s x) (fun f g hf hg => hf.mul hg)
    contMdiffWithinAt_const h
#align cont_mdiff_within_at_finset_prod' contMdiffWithinAt_finset_prod'
#align cont_mdiff_within_at_finset_sum' contMdiffWithinAt_finset_sum'

@[to_additive]
theorem contMdiffAt_finset_prod' (h : ∀ i ∈ t, ContMdiffAt I' I n (f i) x) :
    ContMdiffAt I' I n (∏ i in t, f i) x :=
  contMdiffWithinAt_finset_prod' h
#align cont_mdiff_at_finset_prod' contMdiffAt_finset_prod'
#align cont_mdiff_at_finset_sum' contMdiffAt_finset_sum'

@[to_additive]
theorem contMdiffOn_finset_prod' (h : ∀ i ∈ t, ContMdiffOn I' I n (f i) s) :
    ContMdiffOn I' I n (∏ i in t, f i) s := fun x hx =>
  contMdiffWithinAt_finset_prod' fun i hi => h i hi x hx
#align cont_mdiff_on_finset_prod' contMdiffOn_finset_prod'
#align cont_mdiff_on_finset_sum' contMdiffOn_finset_sum'

@[to_additive]
theorem contMdiff_finset_prod' (h : ∀ i ∈ t, ContMdiff I' I n (f i)) :
    ContMdiff I' I n (∏ i in t, f i) := fun x => contMdiffAt_finset_prod' fun i hi => h i hi x
#align cont_mdiff_finset_prod' contMdiff_finset_prod'
#align cont_mdiff_finset_sum' contMdiff_finset_sum'

@[to_additive]
theorem contMdiffWithinAt_finset_prod (h : ∀ i ∈ t, ContMdiffWithinAt I' I n (f i) s x) :
    ContMdiffWithinAt I' I n (fun x => ∏ i in t, f i x) s x :=
  by
  simp only [← Finset.prod_apply]
  exact contMdiffWithinAt_finset_prod' h
#align cont_mdiff_within_at_finset_prod contMdiffWithinAt_finset_prod
#align cont_mdiff_within_at_finset_sum contMdiffWithinAt_finset_sum

@[to_additive]
theorem contMdiffAt_finset_prod (h : ∀ i ∈ t, ContMdiffAt I' I n (f i) x) :
    ContMdiffAt I' I n (fun x => ∏ i in t, f i x) x :=
  contMdiffWithinAt_finset_prod h
#align cont_mdiff_at_finset_prod contMdiffAt_finset_prod
#align cont_mdiff_at_finset_sum contMdiffAt_finset_sum

@[to_additive]
theorem contMdiffOn_finset_prod (h : ∀ i ∈ t, ContMdiffOn I' I n (f i) s) :
    ContMdiffOn I' I n (fun x => ∏ i in t, f i x) s := fun x hx =>
  contMdiffWithinAt_finset_prod fun i hi => h i hi x hx
#align cont_mdiff_on_finset_prod contMdiffOn_finset_prod
#align cont_mdiff_on_finset_sum contMdiffOn_finset_sum

@[to_additive]
theorem contMdiff_finset_prod (h : ∀ i ∈ t, ContMdiff I' I n (f i)) :
    ContMdiff I' I n fun x => ∏ i in t, f i x := fun x =>
  contMdiffAt_finset_prod fun i hi => h i hi x
#align cont_mdiff_finset_prod contMdiff_finset_prod
#align cont_mdiff_finset_sum contMdiff_finset_sum

@[to_additive]
theorem smoothWithinAt_finset_prod' (h : ∀ i ∈ t, SmoothWithinAt I' I (f i) s x) :
    SmoothWithinAt I' I (∏ i in t, f i) s x :=
  contMdiffWithinAt_finset_prod' h
#align smooth_within_at_finset_prod' smoothWithinAt_finset_prod'
#align smooth_within_at_finset_sum' smoothWithinAt_finset_sum'

@[to_additive]
theorem smoothAt_finset_prod' (h : ∀ i ∈ t, SmoothAt I' I (f i) x) :
    SmoothAt I' I (∏ i in t, f i) x :=
  contMdiffAt_finset_prod' h
#align smooth_at_finset_prod' smoothAt_finset_prod'
#align smooth_at_finset_sum' smoothAt_finset_sum'

@[to_additive]
theorem smoothOn_finset_prod' (h : ∀ i ∈ t, SmoothOn I' I (f i) s) :
    SmoothOn I' I (∏ i in t, f i) s :=
  contMdiffOn_finset_prod' h
#align smooth_on_finset_prod' smoothOn_finset_prod'
#align smooth_on_finset_sum' smoothOn_finset_sum'

@[to_additive]
theorem smooth_finset_prod' (h : ∀ i ∈ t, Smooth I' I (f i)) : Smooth I' I (∏ i in t, f i) :=
  contMdiff_finset_prod' h
#align smooth_finset_prod' smooth_finset_prod'
#align smooth_finset_sum' smooth_finset_sum'

@[to_additive]
theorem smoothWithinAt_finset_prod (h : ∀ i ∈ t, SmoothWithinAt I' I (f i) s x) :
    SmoothWithinAt I' I (fun x => ∏ i in t, f i x) s x :=
  contMdiffWithinAt_finset_prod h
#align smooth_within_at_finset_prod smoothWithinAt_finset_prod
#align smooth_within_at_finset_sum smoothWithinAt_finset_sum

@[to_additive]
theorem smoothAt_finset_prod (h : ∀ i ∈ t, SmoothAt I' I (f i) x) :
    SmoothAt I' I (fun x => ∏ i in t, f i x) x :=
  contMdiffAt_finset_prod h
#align smooth_at_finset_prod smoothAt_finset_prod
#align smooth_at_finset_sum smoothAt_finset_sum

@[to_additive]
theorem smoothOn_finset_prod (h : ∀ i ∈ t, SmoothOn I' I (f i) s) :
    SmoothOn I' I (fun x => ∏ i in t, f i x) s :=
  contMdiffOn_finset_prod h
#align smooth_on_finset_prod smoothOn_finset_prod
#align smooth_on_finset_sum smoothOn_finset_sum

@[to_additive]
theorem smooth_finset_prod (h : ∀ i ∈ t, Smooth I' I (f i)) :
    Smooth I' I fun x => ∏ i in t, f i x :=
  contMdiff_finset_prod h
#align smooth_finset_prod smooth_finset_prod
#align smooth_finset_sum smooth_finset_sum

open Function Filter

@[to_additive]
theorem contMdiff_finprod (h : ∀ i, ContMdiff I' I n (f i))
    (hfin : LocallyFinite fun i => mulSupport (f i)) : ContMdiff I' I n fun x => ∏ᶠ i, f i x :=
  by
  intro x
  rcases finprod_eventually_eq_prod hfin x with ⟨s, hs⟩
  exact (contMdiff_finset_prod (fun i hi => h i) x).congr_of_eventuallyEq hs
#align cont_mdiff_finprod contMdiff_finprod
#align cont_mdiff_finsum contMdiff_finsum

@[to_additive]
theorem contMdiff_finprod_cond (hc : ∀ i, p i → ContMdiff I' I n (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    ContMdiff I' I n fun x => ∏ᶠ (i) (hi : p i), f i x :=
  by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMdiff_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)
#align cont_mdiff_finprod_cond contMdiff_finprod_cond
#align cont_mdiff_finsum_cond contMdiff_finsum_cond

@[to_additive]
theorem smooth_finprod (h : ∀ i, Smooth I' I (f i))
    (hfin : LocallyFinite fun i => mulSupport (f i)) : Smooth I' I fun x => ∏ᶠ i, f i x :=
  contMdiff_finprod h hfin
#align smooth_finprod smooth_finprod
#align smooth_finsum smooth_finsum

@[to_additive]
theorem smooth_finprod_cond (hc : ∀ i, p i → Smooth I' I (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    Smooth I' I fun x => ∏ᶠ (i) (hi : p i), f i x :=
  contMdiff_finprod_cond hc hf
#align smooth_finprod_cond smooth_finprod_cond
#align smooth_finsum_cond smooth_finsum_cond

end CommMonoid

