/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Analysis.NormedSpace.AddTorsor
import Mathbin.Analysis.NormedSpace.LinearIsometry

/-!
# Affine isometries

In this file we define `affine_isometry ๐ P Pโ` to be an affine isometric embedding of normed
add-torsors `P` into `Pโ` over normed `๐`-spaces and `affine_isometry_equiv` to be an affine
isometric equivalence between `P` and `Pโ`.

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `linear_isometry` and `affine_map` theories.

Since many elementary properties don't require `โฅxโฅ = 0 โ x = 0` we initially set up the theory for
`semi_normed_group` and specialize to `normed_group` only when needed.

## Notation

We introduce the notation `P โแตโฑ[๐] Pโ` for `affine_isometry ๐ P Pโ`, and `P โแตโฑ[๐] Pโ` for
`affine_isometry_equiv ๐ P Pโ`.  In contrast with the notation `โโแตข` for linear isometries, `โแตข`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `โแต` is an affine map, since `โโ` has been taken by
algebra-homomorphisms.)

-/


open Function Set

variable (๐ : Type _) {V Vโ Vโ Vโ Vโ : Type _} {Pโ : Type _} (P Pโ : Type _) {Pโ Pโ : Type _} [NormedField ๐]
  [SemiNormedGroup V] [SemiNormedGroup Vโ] [SemiNormedGroup Vโ] [SemiNormedGroup Vโ] [SemiNormedGroup Vโ]
  [NormedSpace ๐ V] [NormedSpace ๐ Vโ] [NormedSpace ๐ Vโ] [NormedSpace ๐ Vโ] [NormedSpace ๐ Vโ] [PseudoMetricSpace P]
  [MetricSpace Pโ] [PseudoMetricSpace Pโ] [PseudoMetricSpace Pโ] [PseudoMetricSpace Pโ] [NormedAddTorsor V P]
  [NormedAddTorsor Vโ Pโ] [NormedAddTorsor Vโ Pโ] [NormedAddTorsor Vโ Pโ] [NormedAddTorsor Vโ Pโ]

include V Vโ

/-- An `๐`-affine isometric embedding of one normed add-torsor over a normed `๐`-space into
another. -/
structure AffineIsometry extends P โแต[๐] Pโ where
  norm_map : โ x : V, โฅlinear xโฅ = โฅxโฅ

omit V Vโ

variable {๐ P Pโ}

-- mathport name: ยซexpr โแตโฑ[ ] ยป
notation:25 P " โแตโฑ[" ๐-- `โแตแตข` would be more consistent with the linear isometry notation, but it is uglier
:25 "] " Pโ:0 => AffineIsometry ๐ P Pโ

namespace AffineIsometry

variable (f : P โแตโฑ[๐] Pโ)

/-- The underlying linear map of an affine isometry is in fact a linear isometry. -/
protected def linearIsometry : V โโแตข[๐] Vโ :=
  { f.linear with norm_map' := f.norm_map }

@[simp]
theorem linear_eq_linear_isometry : f.linear = f.LinearIsometry.toLinearMap := by
  ext
  rfl

include V Vโ

instance : CoeFun (P โแตโฑ[๐] Pโ) fun _ => P โ Pโ :=
  โจfun f => f.toFunโฉ

omit V Vโ

@[simp]
theorem coe_to_affine_map : โf.toAffineMap = f :=
  rfl

include V Vโ

theorem to_affine_map_injective : Injective (toAffineMap : (P โแตโฑ[๐] Pโ) โ P โแต[๐] Pโ)
  | โจf, _โฉ, โจg, _โฉ, rfl => rfl

theorem coe_fn_injective : @Injective (P โแตโฑ[๐] Pโ) (P โ Pโ) coeFn :=
  AffineMap.coe_fn_injective.comp to_affine_map_injective

@[ext]
theorem ext {f g : P โแตโฑ[๐] Pโ} (h : โ x, f x = g x) : f = g :=
  coe_fn_injective <| funext h

omit V Vโ

end AffineIsometry

namespace LinearIsometry

variable (f : V โโแตข[๐] Vโ)

/-- Reinterpret a linear isometry as an affine isometry. -/
def toAffineIsometry : V โแตโฑ[๐] Vโ :=
  { f.toLinearMap.toAffineMap with norm_map := f.norm_map }

@[simp]
theorem coe_to_affine_isometry : โ(f.toAffineIsometry : V โแตโฑ[๐] Vโ) = f :=
  rfl

@[simp]
theorem to_affine_isometry_linear_isometry : f.toAffineIsometry.LinearIsometry = f := by
  ext
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
theorem to_affine_isometry_to_affine_map : f.toAffineIsometry.toAffineMap = f.toLinearMap.toAffineMap :=
  rfl

end LinearIsometry

namespace AffineIsometry

variable (f : P โแตโฑ[๐] Pโ) (fโ : Pโ โแตโฑ[๐] Pโ)

@[simp]
theorem map_vadd (p : P) (v : V) : f (v +แตฅ p) = f.LinearIsometry v +แตฅ f p :=
  f.toAffineMap.map_vadd p v

@[simp]
theorem map_vsub (p1 p2 : P) : f.LinearIsometry (p1 -แตฅ p2) = f p1 -แตฅ f p2 :=
  f.toAffineMap.linear_map_vsub p1 p2

@[simp]
theorem dist_map (x y : P) : dist (f x) (f y) = dist x y := by
  rw [dist_eq_norm_vsub Vโ, dist_eq_norm_vsub V, โ map_vsub, f.linear_isometry.norm_map]

@[simp]
theorem nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by
  simp [โ nndist_dist]

@[simp]
theorem edist_map (x y : P) : edist (f x) (f y) = edist x y := by
  simp [โ edist_dist]

protected theorem isometry : Isometry f :=
  f.edist_map

protected theorem injective : Injective fโ :=
  fโ.Isometry.Injective

@[simp]
theorem map_eq_iff {x y : Pโ} : fโ x = fโ y โ x = y :=
  fโ.Injective.eq_iff

theorem map_ne {x y : Pโ} (h : x โ? y) : fโ x โ? fโ y :=
  fโ.Injective.Ne h

protected theorem lipschitz : LipschitzWith 1 f :=
  f.Isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.Isometry.antilipschitz

@[continuity]
protected theorem continuous : Continuous f :=
  f.Isometry.Continuous

theorem ediam_image (s : Set P) : Emetric.diam (f '' s) = Emetric.diam s :=
  f.Isometry.ediam_image s

theorem ediam_range : Emetric.diam (Range f) = Emetric.diam (Univ : Set P) :=
  f.Isometry.ediam_range

theorem diam_image (s : Set P) : Metric.diam (f '' s) = Metric.diam s :=
  f.Isometry.diam_image s

theorem diam_range : Metric.diam (Range f) = Metric.diam (Univ : Set P) :=
  f.Isometry.diam_range

@[simp]
theorem comp_continuous_iff {ฮฑ : Type _} [TopologicalSpace ฮฑ] {g : ฮฑ โ P} : Continuous (f โ g) โ Continuous g :=
  f.Isometry.comp_continuous_iff

include V

/-- The identity affine isometry. -/
def id : P โแตโฑ[๐] P :=
  โจAffineMap.id ๐ P, fun x => rflโฉ

@[simp]
theorem coe_id : โ(id : P โแตโฑ[๐] P) = _root_.id :=
  rfl

@[simp]
theorem id_apply (x : P) : (AffineIsometry.id : P โแตโฑ[๐] P) x = x :=
  rfl

@[simp]
theorem id_to_affine_map : (id.toAffineMap : P โแต[๐] P) = AffineMap.id ๐ P :=
  rfl

instance : Inhabited (P โแตโฑ[๐] P) :=
  โจidโฉ

include Vโ Vโ

/-- Composition of affine isometries. -/
def comp (g : Pโ โแตโฑ[๐] Pโ) (f : P โแตโฑ[๐] Pโ) : P โแตโฑ[๐] Pโ :=
  โจg.toAffineMap.comp f.toAffineMap, fun x => (g.norm_map _).trans (f.norm_map _)โฉ

@[simp]
theorem coe_comp (g : Pโ โแตโฑ[๐] Pโ) (f : P โแตโฑ[๐] Pโ) : โ(g.comp f) = g โ f :=
  rfl

omit V Vโ Vโ

@[simp]
theorem id_comp : (id : Pโ โแตโฑ[๐] Pโ).comp f = f :=
  ext fun x => rfl

@[simp]
theorem comp_id : f.comp id = f :=
  ext fun x => rfl

include V Vโ Vโ Vโ

theorem comp_assoc (f : Pโ โแตโฑ[๐] Pโ) (g : Pโ โแตโฑ[๐] Pโ) (h : P โแตโฑ[๐] Pโ) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

omit Vโ Vโ Vโ

instance : Monoidโ (P โแตโฑ[๐] P) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
theorem coe_one : โ(1 : P โแตโฑ[๐] P) = _root_.id :=
  rfl

@[simp]
theorem coe_mul (f g : P โแตโฑ[๐] P) : โ(f * g) = f โ g :=
  rfl

end AffineIsometry

-- remark: by analogy with the `linear_isometry` file from which this is adapted, there should
-- follow here a section defining an "inclusion" affine isometry from `p : affine_subspace ๐ P`
-- into `P`; we omit this for now
variable (๐ P Pโ)

include V Vโ

/-- A affine isometric equivalence between two normed vector spaces. -/
structure AffineIsometryEquiv extends P โแต[๐] Pโ where
  norm_map : โ x, โฅlinear xโฅ = โฅxโฅ

variable {๐ P Pโ}

omit V Vโ

-- mathport name: ยซexpr โแตโฑ[ ] ยป
notation:25 P " โแตโฑ[" ๐-- `โแตแตข` would be more consistent with the linear isometry equiv notation, but it is uglier
:25 "] " Pโ:0 => AffineIsometryEquiv ๐ P Pโ

namespace AffineIsometryEquiv

variable (e : P โแตโฑ[๐] Pโ)

/-- The underlying linear equiv of an affine isometry equiv is in fact a linear isometry equiv. -/
protected def linearIsometryEquiv : V โโแตข[๐] Vโ :=
  { e.linear with norm_map' := e.norm_map }

@[simp]
theorem linear_eq_linear_isometry : e.linear = e.LinearIsometryEquiv.toLinearEquiv := by
  ext
  rfl

include V Vโ

instance : CoeFun (P โแตโฑ[๐] Pโ) fun _ => P โ Pโ :=
  โจfun f => f.toFunโฉ

@[simp]
theorem coe_mk (e : P โแต[๐] Pโ) (he : โ x, โฅe.linear xโฅ = โฅxโฅ) : โ(mk e he) = e :=
  rfl

@[simp]
theorem coe_to_affine_equiv (e : P โแตโฑ[๐] Pโ) : โe.toAffineEquiv = e :=
  rfl

theorem to_affine_equiv_injective : Injective (toAffineEquiv : (P โแตโฑ[๐] Pโ) โ P โแต[๐] Pโ)
  | โจe, _โฉ, โจ_, _โฉ, rfl => rfl

@[ext]
theorem ext {e e' : P โแตโฑ[๐] Pโ} (h : โ x, e x = e' x) : e = e' :=
  to_affine_equiv_injective <| AffineEquiv.ext h

omit V Vโ

/-- Reinterpret a `affine_isometry_equiv` as a `affine_isometry`. -/
def toAffineIsometry : P โแตโฑ[๐] Pโ :=
  โจe.1.toAffineMap, e.2โฉ

@[simp]
theorem coe_to_affine_isometry : โe.toAffineIsometry = e :=
  rfl

/-- Construct an affine isometry equivalence by verifying the relation between the map and its
linear part at one base point. Namely, this function takes a map `e : Pโ โ Pโ`, a linear isometry
equivalence `e' : Vโ โแตขโ[k] Vโ`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -แตฅ p) +แตฅ e p`. -/
def mk' (e : Pโ โ Pโ) (e' : Vโ โโแตข[๐] Vโ) (p : Pโ) (h : โ p' : Pโ, e p' = e' (p' -แตฅ p) +แตฅ e p) : Pโ โแตโฑ[๐] Pโ :=
  { AffineEquiv.mk' e e'.toLinearEquiv p h with norm_map := e'.norm_map }

@[simp]
theorem coe_mk' (e : Pโ โ Pโ) (e' : Vโ โโแตข[๐] Vโ) (p h) : โ(mk' e e' p h) = e :=
  rfl

@[simp]
theorem linear_isometry_equiv_mk' (e : Pโ โ Pโ) (e' : Vโ โโแตข[๐] Vโ) (p h) : (mk' e e' p h).LinearIsometryEquiv = e' :=
  by
  ext
  rfl

end AffineIsometryEquiv

namespace LinearIsometryEquiv

variable (e : V โโแตข[๐] Vโ)

/-- Reinterpret a linear isometry equiv as an affine isometry equiv. -/
def toAffineIsometryEquiv : V โแตโฑ[๐] Vโ :=
  { e.toLinearEquiv.toAffineEquiv with norm_map := e.norm_map }

@[simp]
theorem coe_to_affine_isometry_equiv : โ(e.toAffineIsometryEquiv : V โแตโฑ[๐] Vโ) = e :=
  rfl

@[simp]
theorem to_affine_isometry_equiv_linear_isometry_equiv : e.toAffineIsometryEquiv.LinearIsometryEquiv = e := by
  ext
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
theorem to_affine_isometry_equiv_to_affine_equiv :
    e.toAffineIsometryEquiv.toAffineEquiv = e.toLinearEquiv.toAffineEquiv :=
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
theorem to_affine_isometry_equiv_to_affine_isometry :
    e.toAffineIsometryEquiv.toAffineIsometry = e.toLinearIsometry.toAffineIsometry :=
  rfl

end LinearIsometryEquiv

namespace AffineIsometryEquiv

variable (e : P โแตโฑ[๐] Pโ)

protected theorem isometry : Isometry e :=
  e.toAffineIsometry.Isometry

/-- Reinterpret a `affine_isometry_equiv` as an `isometric`. -/
def toIsometric : P โแตข Pโ :=
  โจe.toAffineEquiv.toEquiv, e.Isometryโฉ

@[simp]
theorem coe_to_isometric : โe.toIsometric = e :=
  rfl

include V Vโ

theorem range_eq_univ (e : P โแตโฑ[๐] Pโ) : Set.Range e = Set.Univ := by
  rw [โ coe_to_isometric]
  exact Isometric.range_eq_univ _

omit V Vโ

/-- Reinterpret a `affine_isometry_equiv` as an `homeomorph`. -/
def toHomeomorph : P โโ Pโ :=
  e.toIsometric.toHomeomorph

@[simp]
theorem coe_to_homeomorph : โe.toHomeomorph = e :=
  rfl

protected theorem continuous : Continuous e :=
  e.Isometry.Continuous

protected theorem continuous_at {x} : ContinuousAt e x :=
  e.Continuous.ContinuousAt

protected theorem continuous_on {s} : ContinuousOn e s :=
  e.Continuous.ContinuousOn

protected theorem continuous_within_at {s x} : ContinuousWithinAt e s x :=
  e.Continuous.ContinuousWithinAt

variable (๐ P)

include V

/-- Identity map as a `affine_isometry_equiv`. -/
def refl : P โแตโฑ[๐] P :=
  โจAffineEquiv.refl ๐ P, fun x => rflโฉ

variable {๐ P}

instance : Inhabited (P โแตโฑ[๐] P) :=
  โจrefl ๐ Pโฉ

@[simp]
theorem coe_refl : โ(refl ๐ P) = id :=
  rfl

@[simp]
theorem to_affine_equiv_refl : (refl ๐ P).toAffineEquiv = AffineEquiv.refl ๐ P :=
  rfl

@[simp]
theorem to_isometric_refl : (refl ๐ P).toIsometric = Isometric.refl P :=
  rfl

@[simp]
theorem to_homeomorph_refl : (refl ๐ P).toHomeomorph = Homeomorph.refl P :=
  rfl

omit V

/-- The inverse `affine_isometry_equiv`. -/
def symm : Pโ โแตโฑ[๐] P :=
  { e.toAffineEquiv.symm with norm_map := e.LinearIsometryEquiv.symm.norm_map }

@[simp]
theorem apply_symm_apply (x : Pโ) : e (e.symm x) = x :=
  e.toAffineEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (x : P) : e.symm (e x) = x :=
  e.toAffineEquiv.symm_apply_apply x

@[simp]
theorem symm_symm : e.symm.symm = e :=
  ext fun x => rfl

@[simp]
theorem to_affine_equiv_symm : e.toAffineEquiv.symm = e.symm.toAffineEquiv :=
  rfl

@[simp]
theorem to_isometric_symm : e.toIsometric.symm = e.symm.toIsometric :=
  rfl

@[simp]
theorem to_homeomorph_symm : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl

include Vโ

/-- Composition of `affine_isometry_equiv`s as a `affine_isometry_equiv`. -/
def trans (e' : Pโ โแตโฑ[๐] Pโ) : P โแตโฑ[๐] Pโ :=
  โจe.toAffineEquiv.trans e'.toAffineEquiv, fun x => (e'.norm_map _).trans (e.norm_map _)โฉ

include V Vโ

@[simp]
theorem coe_trans (eโ : P โแตโฑ[๐] Pโ) (eโ : Pโ โแตโฑ[๐] Pโ) : โ(eโ.trans eโ) = eโ โ eโ :=
  rfl

omit V Vโ Vโ

@[simp]
theorem trans_refl : e.trans (refl ๐ Pโ) = e :=
  ext fun x => rfl

@[simp]
theorem refl_trans : (refl ๐ P).trans e = e :=
  ext fun x => rfl

@[simp]
theorem self_trans_symm : e.trans e.symm = refl ๐ P :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self : e.symm.trans e = refl ๐ Pโ :=
  ext e.apply_symm_apply

include V Vโ Vโ

@[simp]
theorem coe_symm_trans (eโ : P โแตโฑ[๐] Pโ) (eโ : Pโ โแตโฑ[๐] Pโ) : โ(eโ.trans eโ).symm = eโ.symm โ eโ.symm :=
  rfl

include Vโ

theorem trans_assoc (ePPโ : P โแตโฑ[๐] Pโ) (ePโG : Pโ โแตโฑ[๐] Pโ) (eGG' : Pโ โแตโฑ[๐] Pโ) :
    ePPโ.trans (ePโG.trans eGG') = (ePPโ.trans ePโG).trans eGG' :=
  rfl

omit Vโ Vโ Vโ

/-- The group of affine isometries of a `normed_add_torsor`, `P`. -/
instance : Groupโ (P โแตโฑ[๐] P) where
  mul := fun eโ eโ => eโ.trans eโ
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc := fun _ _ _ => trans_assoc _ _ _
  mul_left_inv := self_trans_symm

@[simp]
theorem coe_one : โ(1 : P โแตโฑ[๐] P) = id :=
  rfl

@[simp]
theorem coe_mul (e e' : P โแตโฑ[๐] P) : โ(e * e') = e โ e' :=
  rfl

@[simp]
theorem coe_inv (e : P โแตโฑ[๐] P) : โeโปยน = e.symm :=
  rfl

omit V

@[simp]
theorem map_vadd (p : P) (v : V) : e (v +แตฅ p) = e.LinearIsometryEquiv v +แตฅ e p :=
  e.toAffineIsometry.map_vadd p v

@[simp]
theorem map_vsub (p1 p2 : P) : e.LinearIsometryEquiv (p1 -แตฅ p2) = e p1 -แตฅ e p2 :=
  e.toAffineIsometry.map_vsub p1 p2

@[simp]
theorem dist_map (x y : P) : dist (e x) (e y) = dist x y :=
  e.toAffineIsometry.dist_map x y

@[simp]
theorem edist_map (x y : P) : edist (e x) (e y) = edist x y :=
  e.toAffineIsometry.edist_map x y

protected theorem bijective : Bijective e :=
  e.1.Bijective

protected theorem injective : Injective e :=
  e.1.Injective

protected theorem surjective : Surjective e :=
  e.1.Surjective

@[simp]
theorem map_eq_iff {x y : P} : e x = e y โ x = y :=
  e.Injective.eq_iff

theorem map_ne {x y : P} (h : x โ? y) : e x โ? e y :=
  e.Injective.Ne h

protected theorem lipschitz : LipschitzWith 1 e :=
  e.Isometry.lipschitz

protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.Isometry.antilipschitz

@[simp]
theorem ediam_image (s : Set P) : Emetric.diam (e '' s) = Emetric.diam s :=
  e.Isometry.ediam_image s

@[simp]
theorem diam_image (s : Set P) : Metric.diam (e '' s) = Metric.diam s :=
  e.Isometry.diam_image s

variable {ฮฑ : Type _} [TopologicalSpace ฮฑ]

@[simp]
theorem comp_continuous_on_iff {f : ฮฑ โ P} {s : Set ฮฑ} : ContinuousOn (e โ f) s โ ContinuousOn f s :=
  e.Isometry.comp_continuous_on_iff

@[simp]
theorem comp_continuous_iff {f : ฮฑ โ P} : Continuous (e โ f) โ Continuous f :=
  e.Isometry.comp_continuous_iff

section Constructions

variable (๐)

/-- The map `v โฆ v +แตฅ p` as an affine isometric equivalence between `V` and `P`. -/
def vaddConst (p : P) : V โแตโฑ[๐] P :=
  { AffineEquiv.vaddConst ๐ p with norm_map := fun x => rfl }

variable {๐}

include V

@[simp]
theorem coe_vadd_const (p : P) : โ(vaddConst ๐ p) = fun v => v +แตฅ p :=
  rfl

@[simp]
theorem coe_vadd_const_symm (p : P) : โ(vaddConst ๐ p).symm = fun p' => p' -แตฅ p :=
  rfl

@[simp]
theorem vadd_const_to_affine_equiv (p : P) : (vaddConst ๐ p).toAffineEquiv = AffineEquiv.vaddConst ๐ p :=
  rfl

omit V

variable (๐)

/-- `p' โฆ p -แตฅ p'` as an affine isometric equivalence. -/
def constVsub (p : P) : P โแตโฑ[๐] V :=
  { AffineEquiv.constVsub ๐ p with norm_map := norm_neg }

variable {๐}

include V

@[simp]
theorem coe_const_vsub (p : P) : โ(constVsub ๐ p) = (ยท -แตฅ ยท) p :=
  rfl

@[simp]
theorem symm_const_vsub (p : P) :
    (constVsub ๐ p).symm = (LinearIsometryEquiv.neg ๐).toAffineIsometryEquiv.trans (vaddConst ๐ p) := by
  ext
  rfl

omit V

variable (๐ P)

/-- Translation by `v` (that is, the map `p โฆ v +แตฅ p`) as an affine isometric automorphism of `P`.
-/
def constVadd (v : V) : P โแตโฑ[๐] P :=
  { AffineEquiv.constVadd ๐ P v with norm_map := fun x => rfl }

variable {๐ P}

@[simp]
theorem coe_const_vadd (v : V) : โ(constVadd ๐ P v : P โแตโฑ[๐] P) = (ยท +แตฅ ยท) v :=
  rfl

@[simp]
theorem const_vadd_zero : constVadd ๐ P (0 : V) = refl ๐ P :=
  ext <| zero_vadd V

include ๐ V

/-- The map `g` from `V` to `Vโ` corresponding to a map `f` from `P` to `Pโ`, at a base point `p`,
is an isometry if `f` is one. -/
theorem vadd_vsub {f : P โ Pโ} (hf : Isometry f) {p : P} {g : V โ Vโ} (hg : โ v, g v = f (v +แตฅ p) -แตฅ f p) :
    Isometry g := by
  convert (vadd_const ๐ (f p)).symm.Isometry.comp (hf.comp (vadd_const ๐ p).Isometry)
  exact funext hg

omit ๐

variable (๐)

/-- Point reflection in `x` as an affine isometric automorphism. -/
def pointReflection (x : P) : P โแตโฑ[๐] P :=
  (constVsub ๐ x).trans (vaddConst ๐ x)

variable {๐}

theorem point_reflection_apply (x y : P) : (pointReflection ๐ x) y = x -แตฅ y +แตฅ x :=
  rfl

@[simp]
theorem point_reflection_to_affine_equiv (x : P) :
    (pointReflection ๐ x).toAffineEquiv = AffineEquiv.pointReflection ๐ x :=
  rfl

@[simp]
theorem point_reflection_self (x : P) : pointReflection ๐ x x = x :=
  AffineEquiv.point_reflection_self ๐ x

theorem point_reflection_involutive (x : P) : Function.Involutive (pointReflection ๐ x) :=
  Equivโ.point_reflection_involutive x

@[simp]
theorem point_reflection_symm (x : P) : (pointReflection ๐ x).symm = pointReflection ๐ x :=
  to_affine_equiv_injective <| AffineEquiv.point_reflection_symm ๐ x

@[simp]
theorem dist_point_reflection_fixed (x y : P) : dist (pointReflection ๐ x y) x = dist y x := by
  rw [โ (point_reflection ๐ x).dist_map y x, point_reflection_self]

theorem dist_point_reflection_self' (x y : P) : dist (pointReflection ๐ x y) y = โฅbit0 (x -แตฅ y)โฅ := by
  rw [point_reflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, bit0]

theorem dist_point_reflection_self (x y : P) : dist (pointReflection ๐ x y) y = โฅ(2 : ๐)โฅ * dist x y := by
  rw [dist_point_reflection_self', โ two_smul' ๐ (x -แตฅ y), norm_smul, โ dist_eq_norm_vsub V]

theorem point_reflection_fixed_iff [Invertible (2 : ๐)] {x y : P} : pointReflection ๐ x y = y โ y = x :=
  AffineEquiv.point_reflection_fixed_iff_of_module ๐

variable [NormedSpace โ V]

theorem dist_point_reflection_self_real (x y : P) : dist (pointReflection โ x y) y = 2 * dist x y := by
  rw [dist_point_reflection_self, Real.norm_two]

@[simp]
theorem point_reflection_midpoint_left (x y : P) : pointReflection โ (midpoint โ x y) x = y :=
  AffineEquiv.point_reflection_midpoint_left x y

@[simp]
theorem point_reflection_midpoint_right (x y : P) : pointReflection โ (midpoint โ x y) y = x :=
  AffineEquiv.point_reflection_midpoint_right x y

end Constructions

end AffineIsometryEquiv

include V Vโ

/-- If `f` is an affine map, then its linear part is continuous iff `f` is continuous. -/
theorem AffineMap.continuous_linear_iff {f : P โแต[๐] Pโ} : Continuous f.linear โ Continuous f := by
  inhabit P
  have :
    (f.linear : V โ Vโ) =
      (AffineIsometryEquiv.vaddConst ๐ <| f default).toHomeomorph.symm โ
        f โ (AffineIsometryEquiv.vaddConst ๐ default).toHomeomorph :=
    by
    ext v
    simp
  rw [this]
  simp only [โ Homeomorph.comp_continuous_iff, โ Homeomorph.comp_continuous_iff']

/-- If `f` is an affine map, then its linear part is an open map iff `f` is an open map. -/
theorem AffineMap.is_open_map_linear_iff {f : P โแต[๐] Pโ} : IsOpenMap f.linear โ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V โ Vโ) =
      (AffineIsometryEquiv.vaddConst ๐ <| f default).toHomeomorph.symm โ
        f โ (AffineIsometryEquiv.vaddConst ๐ default).toHomeomorph :=
    by
    ext v
    simp
  rw [this]
  simp only [โ Homeomorph.comp_is_open_map_iff, โ Homeomorph.comp_is_open_map_iff']

