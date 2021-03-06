/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Topology.Algebra.ContinuousAffineMap
import Mathbin.Analysis.NormedSpace.AddTorsor
import Mathbin.Analysis.NormedSpace.AffineIsometry
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# Continuous affine maps between normed spaces.

This file develops the theory of continuous affine maps between affine spaces modelled on normed
spaces.

In the particular case that the affine spaces are just normed vector spaces `V`, `W`, we define a
norm on the space of continuous affine maps by defining the norm of `f : V βA[π] W` to be
`β₯fβ₯ = max β₯f 0β₯ β₯f.cont_linearβ₯`. This is chosen so that we have a linear isometry:
`(V βA[π] W) ββα΅’[π] W Γ (V βL[π] W)`.

The abstract picture is that for an affine space `P` modelled on a vector space `V`, together with
a vector space `W`, there is an exact sequence of `π`-modules: `0 β C β A β L β 0` where `C`, `A`
are the spaces of constant and affine maps `P β W` and `L` is the space of linear maps `V β W`.

Any choice of a base point in `P` corresponds to a splitting of this sequence so in particular if we
take `P = V`, using `0 : V` as the base point provides a splitting, and we prove this is an
isometric decomposition.

On the other hand, choosing a base point breaks the affine invariance so the norm fails to be
submultiplicative: for a composition of maps, we have only `β₯f.comp gβ₯ β€ β₯fβ₯ * β₯gβ₯ + β₯f 0β₯`.

## Main definitions:

 * `continuous_affine_map.cont_linear`
 * `continuous_affine_map.has_norm`
 * `continuous_affine_map.norm_comp_le`
 * `continuous_affine_map.to_const_prod_continuous_linear_map`

-/


namespace ContinuousAffineMap

variable {π R V W Wβ P Q Qβ : Type _}

variable [NormedGroup V] [MetricSpace P] [NormedAddTorsor V P]

variable [NormedGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

variable [NormedGroup Wβ] [MetricSpace Qβ] [NormedAddTorsor Wβ Qβ]

variable [NormedField R] [NormedSpace R V] [NormedSpace R W] [NormedSpace R Wβ]

variable [NondiscreteNormedField π] [NormedSpace π V] [NormedSpace π W] [NormedSpace π Wβ]

include V W

/-- The linear map underlying a continuous affine map is continuous. -/
def contLinear (f : P βA[R] Q) : V βL[R] W :=
  { f.linear with toFun := f.linear,
    cont := by
      rw [AffineMap.continuous_linear_iff]
      exact f.cont }

@[simp]
theorem coe_cont_linear (f : P βA[R] Q) : (f.contLinear : V β W) = f.linear :=
  rfl

@[simp]
theorem coe_cont_linear_eq_linear (f : P βA[R] Q) : (f.contLinear : V ββ[R] W) = (f : P βα΅[R] Q).linear := by
  ext
  rfl

@[simp]
theorem coe_mk_const_linear_eq_linear (f : P βα΅[R] Q) (h) : ((β¨f, hβ© : P βA[R] Q).contLinear : V β W) = f.linear :=
  rfl

theorem coe_linear_eq_coe_cont_linear (f : P βA[R] Q) : ((f : P βα΅[R] Q).linear : V β W) = (βf.contLinear : V β W) :=
  rfl

include Wβ

@[simp]
theorem comp_cont_linear (f : P βA[R] Q) (g : Q βA[R] Qβ) : (g.comp f).contLinear = g.contLinear.comp f.contLinear :=
  rfl

omit Wβ

@[simp]
theorem map_vadd (f : P βA[R] Q) (p : P) (v : V) : f (v +α΅₯ p) = f.contLinear v +α΅₯ f p :=
  f.map_vadd' p v

@[simp]
theorem cont_linear_map_vsub (f : P βA[R] Q) (pβ pβ : P) : f.contLinear (pβ -α΅₯ pβ) = f pβ -α΅₯ f pβ :=
  f.toAffineMap.linear_map_vsub pβ pβ

@[simp]
theorem const_cont_linear (q : Q) : (const R P q).contLinear = 0 :=
  rfl

theorem cont_linear_eq_zero_iff_exists_const (f : P βA[R] Q) : f.contLinear = 0 β β q, f = const R P q := by
  have hβ : f.cont_linear = 0 β (f : P βα΅[R] Q).linear = 0 := by
    refine' β¨fun h => _, fun h => _β© <;> ext
    Β· rw [β coe_cont_linear_eq_linear, h]
      rfl
      
    Β· rw [β coe_linear_eq_coe_cont_linear, h]
      rfl
      
  have hβ : β q : Q, f = const R P q β (f : P βα΅[R] Q) = AffineMap.const R P q := by
    intro q
    refine' β¨fun h => _, fun h => _β© <;> ext
    Β· rw [h]
      rfl
      
    Β· rw [β coe_to_affine_map, h]
      rfl
      
  simp_rw [hβ, hβ]
  exact (f : P βα΅[R] Q).linear_eq_zero_iff_exists_const

@[simp]
theorem to_affine_map_cont_linear (f : V βL[R] W) : f.toContinuousAffineMap.contLinear = f := by
  ext
  rfl

@[simp]
theorem zero_cont_linear : (0 : P βA[R] W).contLinear = 0 :=
  rfl

@[simp]
theorem add_cont_linear (f g : P βA[R] W) : (f + g).contLinear = f.contLinear + g.contLinear :=
  rfl

@[simp]
theorem sub_cont_linear (f g : P βA[R] W) : (f - g).contLinear = f.contLinear - g.contLinear :=
  rfl

@[simp]
theorem neg_cont_linear (f : P βA[R] W) : (-f).contLinear = -f.contLinear :=
  rfl

@[simp]
theorem smul_cont_linear (t : R) (f : P βA[R] W) : (t β’ f).contLinear = t β’ f.contLinear :=
  rfl

theorem decomp (f : V βA[R] W) : (f : V β W) = f.contLinear + Function.const V (f 0) := by
  rcases f with β¨f, hβ©
  rw [coe_mk_const_linear_eq_linear, coe_mk, f.decomp, Pi.add_apply, LinearMap.map_zero, zero_addβ]

section NormedSpaceStructure

variable (f : V βA[π] W)

/-- Note that unlike the operator norm for linear maps, this norm is _not_ submultiplicative:
we do _not_ necessarily have `β₯f.comp gβ₯ β€ β₯fβ₯ * β₯gβ₯`. See `norm_comp_le` for what we can say. -/
noncomputable instance hasNorm : HasNorm (V βA[π] W) :=
  β¨fun f => max β₯f 0β₯ β₯f.contLinearβ₯β©

theorem norm_def : β₯fβ₯ = max β₯f 0β₯ β₯f.contLinearβ₯ :=
  rfl

theorem norm_cont_linear_le : β₯f.contLinearβ₯ β€ β₯fβ₯ :=
  le_max_rightβ _ _

theorem norm_image_zero_le : β₯f 0β₯ β€ β₯fβ₯ :=
  le_max_leftβ _ _

@[simp]
theorem norm_eq (h : f 0 = 0) : β₯fβ₯ = β₯f.contLinearβ₯ :=
  calc
    β₯fβ₯ = max β₯f 0β₯ β₯f.contLinearβ₯ := by
      rw [norm_def]
    _ = max 0 β₯f.contLinearβ₯ := by
      rw [h, norm_zero]
    _ = β₯f.contLinearβ₯ := max_eq_rightβ (norm_nonneg _)
    

noncomputable instance : NormedGroup (V βA[π] W) :=
  NormedGroup.ofCore _
    { norm_eq_zero_iff := fun f => by
        rw [norm_def]
        refine'
          β¨fun hβ => _, by
            rintro rfl
            simp β©
        rcases max_eq_iff.mp hβ with (β¨hβ, hββ© | β¨hβ, hββ©) <;> rw [hβ] at hβ
        Β· rw [norm_le_zero_iff, cont_linear_eq_zero_iff_exists_const] at hβ
          obtain β¨q, rflβ© := hβ
          simp only [β Function.const_applyβ, β coe_const, β norm_eq_zero] at hβ
          rw [hβ]
          rfl
          
        Β· rw [norm_eq_zero_iff', cont_linear_eq_zero_iff_exists_const] at hβ
          obtain β¨q, rflβ© := hβ
          simp only [β Function.const_applyβ, β coe_const, β norm_le_zero_iff] at hβ
          rw [hβ]
          rfl
          ,
      triangle := fun f g => by
        simp only [β norm_def, β Pi.add_apply, β add_cont_linear, β coe_add, β max_le_iff]
        exact
          β¨(norm_add_le _ _).trans (add_le_add (le_max_leftβ _ _) (le_max_leftβ _ _)),
            (norm_add_le _ _).trans (add_le_add (le_max_rightβ _ _) (le_max_rightβ _ _))β©,
      norm_neg := fun f => by
        simp [β norm_def] }

instance :
    NormedSpace π (V βA[π] W) where norm_smul_le := fun t f => by
    simp only [β norm_def, β smul_cont_linear, β coe_smul, β Pi.smul_apply, β norm_smul,
      mul_max_of_nonneg _ _ (norm_nonneg t)]

theorem norm_comp_le (g : Wβ βA[π] V) : β₯f.comp gβ₯ β€ β₯fβ₯ * β₯gβ₯ + β₯f 0β₯ := by
  rw [norm_def, max_le_iff]
  constructor
  Β· calc β₯f.comp g 0β₯ = β₯f (g 0)β₯ := by
        simp _ = β₯f.cont_linear (g 0) + f 0β₯ := by
        rw [f.decomp]
        simp _ β€ β₯f.cont_linearβ₯ * β₯g 0β₯ + β₯f 0β₯ :=
        (norm_add_le _ _).trans (add_le_add_right (f.cont_linear.le_op_norm _) _)_ β€ β₯fβ₯ * β₯gβ₯ + β₯f 0β₯ :=
        add_le_add_right (mul_le_mul f.norm_cont_linear_le g.norm_image_zero_le (norm_nonneg _) (norm_nonneg _)) _
    
  Β· calc β₯(f.comp g).contLinearβ₯ β€ β₯f.cont_linearβ₯ * β₯g.cont_linearβ₯ :=
        (g.comp_cont_linear f).symm βΈ f.cont_linear.op_norm_comp_le _ _ β€ β₯fβ₯ * β₯gβ₯ :=
        mul_le_mul f.norm_cont_linear_le g.norm_cont_linear_le (norm_nonneg _) (norm_nonneg _)_ β€ β₯fβ₯ * β₯gβ₯ + β₯f 0β₯ :=
        by
        rw [le_add_iff_nonneg_right]
        apply norm_nonneg
    

variable (π V W)

/-- The space of affine maps between two normed spaces is linearly isometric to the product of the
codomain with the space of linear maps, by taking the value of the affine map at `(0 : V)` and the
linear part. -/
def toConstProdContinuousLinearMap : (V βA[π] W) ββα΅’[π] W Γ (V βL[π] W) where
  toFun := fun f => β¨f 0, f.contLinearβ©
  invFun := fun p => p.2.toContinuousAffineMap + const π V p.1
  left_inv := fun f => by
    ext
    rw [f.decomp]
    simp
  right_inv := by
    rintro β¨v, fβ©
    ext <;> simp
  map_add' := by
    simp
  map_smul' := by
    simp
  norm_map' := fun f => by
    simp [β Prod.norm_def, β norm_def]

@[simp]
theorem to_const_prod_continuous_linear_map_fst (f : V βA[π] W) : (toConstProdContinuousLinearMap π V W f).fst = f 0 :=
  rfl

@[simp]
theorem to_const_prod_continuous_linear_map_snd (f : V βA[π] W) :
    (toConstProdContinuousLinearMap π V W f).snd = f.contLinear :=
  rfl

end NormedSpaceStructure

end ContinuousAffineMap

