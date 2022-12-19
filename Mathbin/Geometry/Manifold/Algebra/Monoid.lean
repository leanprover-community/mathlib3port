/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module geometry.manifold.algebra.monoid
! leanprover-community/mathlib commit d4f69d96f3532729da8ebb763f4bc26fcf640f06
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
  smoothAdd : Smooth (I.Prod I) I fun p : G × G => p.1 + p.2
#align has_smooth_add HasSmoothAdd

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a smooth (Lie) monoid or a smooth semigroup.
A smooth monoid over `G`, for example, is obtained by requiring both the instances `monoid G`
and `has_smooth_mul I G`. -/
@[to_additive]
class HasSmoothMul {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H]
  {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) (G : Type _)
  [Mul G] [TopologicalSpace G] [ChartedSpace H G] extends SmoothManifoldWithCorners I G : Prop where
  smoothMul : Smooth (I.Prod I) I fun p : G × G => p.1 * p.2
#align has_smooth_mul HasSmoothMul

section HasSmoothMul

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [Mul G]
  [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G] {E' : Type _} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type _} [TopologicalSpace M] [ChartedSpace H' M]

section

variable (I)

@[to_additive]
theorem smoothMul : Smooth (I.Prod I) I fun p : G × G => p.1 * p.2 :=
  HasSmoothMul.smoothMul
#align smooth_mul smoothMul

/-- If the multiplication is smooth, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive
      "If the addition is smooth, then it is continuous. This is not an instance for technical reasons,\nsee note [Design choices about smooth algebraic structures]."]
theorem has_continuous_mul_of_smooth : HasContinuousMul G :=
  ⟨(smoothMul I).Continuous⟩
#align has_continuous_mul_of_smooth has_continuous_mul_of_smooth

end

section

variable {f g : M → G} {s : Set M} {x : M} {n : ℕ∞}

@[to_additive]
theorem ContMdiffWithinAt.mul (hf : ContMdiffWithinAt I' I n f s x)
    (hg : ContMdiffWithinAt I' I n g s x) : ContMdiffWithinAt I' I n (f * g) s x :=
  ((smoothMul I).SmoothAt.of_le le_top).compContMdiffWithinAt x (hf.prod_mk hg)
#align cont_mdiff_within_at.mul ContMdiffWithinAt.mul

@[to_additive]
theorem ContMdiffAt.mul (hf : ContMdiffAt I' I n f x) (hg : ContMdiffAt I' I n g x) :
    ContMdiffAt I' I n (f * g) x :=
  hf.mul hg
#align cont_mdiff_at.mul ContMdiffAt.mul

@[to_additive]
theorem ContMdiffOn.mul (hf : ContMdiffOn I' I n f s) (hg : ContMdiffOn I' I n g s) :
    ContMdiffOn I' I n (f * g) s := fun x hx => (hf x hx).mul (hg x hx)
#align cont_mdiff_on.mul ContMdiffOn.mul

@[to_additive]
theorem ContMdiff.mul (hf : ContMdiff I' I n f) (hg : ContMdiff I' I n g) :
    ContMdiff I' I n (f * g) := fun x => (hf x).mul (hg x)
#align cont_mdiff.mul ContMdiff.mul

@[to_additive]
theorem SmoothWithinAt.mul (hf : SmoothWithinAt I' I f s x) (hg : SmoothWithinAt I' I g s x) :
    SmoothWithinAt I' I (f * g) s x :=
  hf.mul hg
#align smooth_within_at.mul SmoothWithinAt.mul

@[to_additive]
theorem SmoothAt.mul (hf : SmoothAt I' I f x) (hg : SmoothAt I' I g x) : SmoothAt I' I (f * g) x :=
  hf.mul hg
#align smooth_at.mul SmoothAt.mul

@[to_additive]
theorem SmoothOn.mul (hf : SmoothOn I' I f s) (hg : SmoothOn I' I g s) : SmoothOn I' I (f * g) s :=
  hf.mul hg
#align smooth_on.mul SmoothOn.mul

@[to_additive]
theorem Smooth.mul (hf : Smooth I' I f) (hg : Smooth I' I g) : Smooth I' I (f * g) :=
  hf.mul hg
#align smooth.mul Smooth.mul

@[to_additive]
theorem smoothMulLeft {a : G} : Smooth I I fun b : G => a * b :=
  smoothConst.mul smoothId
#align smooth_mul_left smoothMulLeft

@[to_additive]
theorem smoothMulRight {a : G} : Smooth I I fun b : G => b * a :=
  smoothId.mul smoothConst
#align smooth_mul_right smoothMulRight

end

variable (I) (g h : G)

/-- Left multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smooth_left_mul` with the notation `𝑳` usually use `L` instead of `𝑳` in the
names. -/
def smoothLeftMul : C^∞⟮I, G; I, G⟯ :=
  ⟨leftMul g, smoothMulLeft⟩
#align smooth_left_mul smoothLeftMul

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smooth_right_mul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨rightMul g, smoothMulRight⟩
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
    (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) := by
  ext
  simp only [ContMdiffMap.comp_apply, L_apply, mul_assoc]
#align L_mul L_mul

@[simp]
theorem R_mul {G : Type _} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G]
    (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) := by
  ext
  simp only [ContMdiffMap.comp_apply, R_apply, mul_assoc]
#align R_mul R_mul

section

variable {G' : Type _} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H G'] [HasSmoothMul I G']
  (g' : G')

theorem smooth_left_mul_one : (𝑳 I g') 1 = g' :=
  mul_one g'
#align smooth_left_mul_one smooth_left_mul_one

theorem smooth_right_mul_one : (𝑹 I g') 1 = g' :=
  one_mul g'
#align smooth_right_mul_one smooth_right_mul_one

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
    smoothMul :=
      ((smoothFst.comp smoothFst).Smooth.mul (smoothFst.comp smoothSnd)).prod_mk
        ((smoothSnd.comp smoothFst).Smooth.mul (smoothSnd.comp smoothSnd)) }
#align has_smooth_mul.prod HasSmoothMul.prod

end HasSmoothMul

section Monoid

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type _} [Monoid G]
  [TopologicalSpace G] [ChartedSpace H G] [HasSmoothMul I G] {H' : Type _} [TopologicalSpace H']
  {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type _} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G'] [HasSmoothMul I' G']

theorem smoothPow : ∀ n : ℕ, Smooth I I fun a : G => a ^ n
  | 0 => by 
    simp only [pow_zero]
    exact smoothConst
  | k + 1 => by simpa [pow_succ] using smooth_id.mul (smoothPow _)
#align smooth_pow smoothPow

/-- Morphism of additive smooth monoids. -/
structure SmoothAddMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  (G : Type _) [TopologicalSpace G] [ChartedSpace H G] [AddMonoid G] [HasSmoothAdd I G]
  (G' : Type _) [TopologicalSpace G'] [ChartedSpace H' G'] [AddMonoid G']
  [HasSmoothAdd I' G'] extends G →+ G' where
  smoothToFun : Smooth I I' to_fun
#align smooth_add_monoid_morphism SmoothAddMonoidMorphism

/-- Morphism of smooth monoids. -/
@[to_additive]
structure SmoothMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  (G : Type _) [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [HasSmoothMul I G] (G' : Type _)
  [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G'] [HasSmoothMul I' G'] extends G →* G' where
  smoothToFun : Smooth I I' to_fun
#align smooth_monoid_morphism SmoothMonoidMorphism

@[to_additive]
instance : One (SmoothMonoidMorphism I I' G G') :=
  ⟨{  smoothToFun := smoothConst
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
theorem contMdiffWithinAtFinsetProd' (h : ∀ i ∈ t, ContMdiffWithinAt I' I n (f i) s x) :
    ContMdiffWithinAt I' I n (∏ i in t, f i) s x :=
  Finset.prod_induction f (fun f => ContMdiffWithinAt I' I n f s x) (fun f g hf hg => hf.mul hg)
    contMdiffWithinAtConst h
#align cont_mdiff_within_at_finset_prod' contMdiffWithinAtFinsetProd'

@[to_additive]
theorem contMdiffAtFinsetProd' (h : ∀ i ∈ t, ContMdiffAt I' I n (f i) x) :
    ContMdiffAt I' I n (∏ i in t, f i) x :=
  contMdiffWithinAtFinsetProd' h
#align cont_mdiff_at_finset_prod' contMdiffAtFinsetProd'

@[to_additive]
theorem contMdiffOnFinsetProd' (h : ∀ i ∈ t, ContMdiffOn I' I n (f i) s) :
    ContMdiffOn I' I n (∏ i in t, f i) s := fun x hx =>
  contMdiffWithinAtFinsetProd' fun i hi => h i hi x hx
#align cont_mdiff_on_finset_prod' contMdiffOnFinsetProd'

@[to_additive]
theorem contMdiffFinsetProd' (h : ∀ i ∈ t, ContMdiff I' I n (f i)) :
    ContMdiff I' I n (∏ i in t, f i) := fun x => contMdiffAtFinsetProd' fun i hi => h i hi x
#align cont_mdiff_finset_prod' contMdiffFinsetProd'

@[to_additive]
theorem contMdiffWithinAtFinsetProd (h : ∀ i ∈ t, ContMdiffWithinAt I' I n (f i) s x) :
    ContMdiffWithinAt I' I n (fun x => ∏ i in t, f i x) s x := by
  simp only [← Finset.prod_apply]
  exact contMdiffWithinAtFinsetProd' h
#align cont_mdiff_within_at_finset_prod contMdiffWithinAtFinsetProd

@[to_additive]
theorem contMdiffAtFinsetProd (h : ∀ i ∈ t, ContMdiffAt I' I n (f i) x) :
    ContMdiffAt I' I n (fun x => ∏ i in t, f i x) x :=
  contMdiffWithinAtFinsetProd h
#align cont_mdiff_at_finset_prod contMdiffAtFinsetProd

@[to_additive]
theorem contMdiffOnFinsetProd (h : ∀ i ∈ t, ContMdiffOn I' I n (f i) s) :
    ContMdiffOn I' I n (fun x => ∏ i in t, f i x) s := fun x hx =>
  contMdiffWithinAtFinsetProd fun i hi => h i hi x hx
#align cont_mdiff_on_finset_prod contMdiffOnFinsetProd

@[to_additive]
theorem contMdiffFinsetProd (h : ∀ i ∈ t, ContMdiff I' I n (f i)) :
    ContMdiff I' I n fun x => ∏ i in t, f i x := fun x => contMdiffAtFinsetProd fun i hi => h i hi x
#align cont_mdiff_finset_prod contMdiffFinsetProd

@[to_additive]
theorem smoothWithinAtFinsetProd' (h : ∀ i ∈ t, SmoothWithinAt I' I (f i) s x) :
    SmoothWithinAt I' I (∏ i in t, f i) s x :=
  contMdiffWithinAtFinsetProd' h
#align smooth_within_at_finset_prod' smoothWithinAtFinsetProd'

@[to_additive]
theorem smoothAtFinsetProd' (h : ∀ i ∈ t, SmoothAt I' I (f i) x) :
    SmoothAt I' I (∏ i in t, f i) x :=
  contMdiffAtFinsetProd' h
#align smooth_at_finset_prod' smoothAtFinsetProd'

@[to_additive]
theorem smoothOnFinsetProd' (h : ∀ i ∈ t, SmoothOn I' I (f i) s) :
    SmoothOn I' I (∏ i in t, f i) s :=
  contMdiffOnFinsetProd' h
#align smooth_on_finset_prod' smoothOnFinsetProd'

@[to_additive]
theorem smoothFinsetProd' (h : ∀ i ∈ t, Smooth I' I (f i)) : Smooth I' I (∏ i in t, f i) :=
  contMdiffFinsetProd' h
#align smooth_finset_prod' smoothFinsetProd'

@[to_additive]
theorem smoothWithinAtFinsetProd (h : ∀ i ∈ t, SmoothWithinAt I' I (f i) s x) :
    SmoothWithinAt I' I (fun x => ∏ i in t, f i x) s x :=
  contMdiffWithinAtFinsetProd h
#align smooth_within_at_finset_prod smoothWithinAtFinsetProd

@[to_additive]
theorem smoothAtFinsetProd (h : ∀ i ∈ t, SmoothAt I' I (f i) x) :
    SmoothAt I' I (fun x => ∏ i in t, f i x) x :=
  contMdiffAtFinsetProd h
#align smooth_at_finset_prod smoothAtFinsetProd

@[to_additive]
theorem smoothOnFinsetProd (h : ∀ i ∈ t, SmoothOn I' I (f i) s) :
    SmoothOn I' I (fun x => ∏ i in t, f i x) s :=
  contMdiffOnFinsetProd h
#align smooth_on_finset_prod smoothOnFinsetProd

@[to_additive]
theorem smoothFinsetProd (h : ∀ i ∈ t, Smooth I' I (f i)) : Smooth I' I fun x => ∏ i in t, f i x :=
  contMdiffFinsetProd h
#align smooth_finset_prod smoothFinsetProd

open Function Filter

@[to_additive]
theorem contMdiffFinprod (h : ∀ i, ContMdiff I' I n (f i))
    (hfin : LocallyFinite fun i => mulSupport (f i)) : ContMdiff I' I n fun x => ∏ᶠ i, f i x := by
  intro x
  rcases finprod_eventually_eq_prod hfin x with ⟨s, hs⟩
  exact (contMdiffFinsetProd (fun i hi => h i) x).congr_of_eventually_eq hs
#align cont_mdiff_finprod contMdiffFinprod

@[to_additive]
theorem contMdiffFinprodCond (hc : ∀ i, p i → ContMdiff I' I n (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    ContMdiff I' I n fun x => ∏ᶠ (i) (hi : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMdiffFinprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)
#align cont_mdiff_finprod_cond contMdiffFinprodCond

@[to_additive]
theorem smoothFinprod (h : ∀ i, Smooth I' I (f i))
    (hfin : LocallyFinite fun i => mulSupport (f i)) : Smooth I' I fun x => ∏ᶠ i, f i x :=
  contMdiffFinprod h hfin
#align smooth_finprod smoothFinprod

@[to_additive]
theorem smoothFinprodCond (hc : ∀ i, p i → Smooth I' I (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    Smooth I' I fun x => ∏ᶠ (i) (hi : p i), f i x :=
  contMdiffFinprodCond hc hf
#align smooth_finprod_cond smoothFinprodCond

end CommMonoid

