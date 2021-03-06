/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, FrΓ©dΓ©ric Dupuis
-/
import Mathbin.Analysis.Convex.Hull
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Convex cones

In a `π`-module `E`, we define a convex cone as a set `s` such that `a β’ x + b β’ y β s` whenever
`x, y β s` and `a, b > 0`. We prove that convex cones form a `complete_lattice`, and define their
images (`convex_cone.map`) and preimages (`convex_cone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We also define `convex.to_cone` to be the minimal cone that includes a given convex set.

We define `set.inner_dual_cone` to be the cone consisting of all points `y` such that for
all points `x` in a given set `0 β€ βͺ x, y β«`.

## Main statements

We prove two extension theorems:
* `riesz_extension`:
  [M. Riesz extension theorem](https://en.wikipedia.org/wiki/M._Riesz_extension_theorem) says that
  if `s` is a convex cone in a real vector space `E`, `p` is a submodule of `E`
  such that `p + s = E`, and `f` is a linear function `p β β` which is
  nonnegative on `p β© s`, then there exists a globally defined linear function
  `g : E β β` that agrees with `f` on `p`, and is nonnegative on `s`.
* `exists_extension_of_le_sublinear`:
  Hahn-Banach theorem: if `N : E β β` is a sublinear map, `f` is a linear map
  defined on a subspace of `E`, and `f x β€ N x` for all `x` in the domain of `f`,
  then `f` can be extended to the whole space to a linear map `g` such that `g x β€ N x`
  for all `x`

## Implementation notes

While `convex π` is a predicate on sets, `convex_cone π E` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
-/


open Set LinearMap

open Classical Pointwise

variable {π E F G : Type _}

/-! ### Definition of `convex_cone` and basic properties -/


section Definitions

variable (π E) [OrderedSemiring π]

/-- A convex cone is a subset `s` of a `π`-module such that `a β’ x + b β’ y β s` whenever `a, b > 0`
and `x, y β s`. -/
structure ConvexCone [AddCommMonoidβ E] [HasSmul π E] where
  Carrier : Set E
  smul_mem' : β β¦c : πβ¦, 0 < c β β β¦x : Eβ¦, x β carrier β c β’ x β carrier
  add_mem' : β β¦xβ¦ (hx : x β carrier) β¦yβ¦ (hy : y β carrier), x + y β carrier

end Definitions

variable {π E}

namespace ConvexCone

section OrderedSemiring

variable [OrderedSemiring π] [AddCommMonoidβ E]

section HasSmul

variable [HasSmul π E] (S T : ConvexCone π E)

instance : Coe (ConvexCone π E) (Set E) :=
  β¨ConvexCone.Carrierβ©

instance : HasMem E (ConvexCone π E) :=
  β¨fun m S => m β S.Carrierβ©

instance : LE (ConvexCone π E) :=
  β¨fun S T => S.Carrier β T.Carrierβ©

instance : LT (ConvexCone π E) :=
  β¨fun S T => S.Carrier β T.Carrierβ©

@[simp, norm_cast]
theorem mem_coe {x : E} : x β (S : Set E) β x β S :=
  Iff.rfl

@[simp]
theorem mem_mk {s : Set E} {hβ hβ x} : x β @mk π _ _ _ _ s hβ hβ β x β s :=
  Iff.rfl

/-- Two `convex_cone`s are equal if the underlying sets are equal. -/
theorem ext' {S T : ConvexCone π E} (h : (S : Set E) = T) : S = T := by
  cases S <;> cases T <;> congr

/-- Two `convex_cone`s are equal if and only if the underlying sets are equal. -/
protected theorem ext'_iff {S T : ConvexCone π E} : (S : Set E) = T β S = T :=
  β¨ext', fun h => h βΈ rflβ©

/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext]
theorem ext {S T : ConvexCone π E} (h : β x, x β S β x β T) : S = T :=
  ext' <| Set.ext h

theorem smul_mem {c : π} {x : E} (hc : 0 < c) (hx : x β S) : c β’ x β S :=
  S.smul_mem' hc hx

theorem add_mem β¦xβ¦ (hx : x β S) β¦yβ¦ (hy : y β S) : x + y β S :=
  S.add_mem' hx hy

instance : HasInf (ConvexCone π E) :=
  β¨fun S T =>
    β¨S β© T, fun c hc x hx => β¨S.smul_mem hc hx.1, T.smul_mem hc hx.2β©, fun x hx y hy =>
      β¨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2β©β©β©

theorem coe_inf : ((SβT : ConvexCone π E) : Set E) = βS β© βT :=
  rfl

theorem mem_inf {x} : x β SβT β x β S β§ x β T :=
  Iff.rfl

instance : HasInfβ (ConvexCone π E) :=
  β¨fun S =>
    β¨β s β S, βs, fun c hc x hx => mem_bInter fun s hs => s.smul_mem hc <| mem_Interβ.1 hx s hs, fun x hx y hy =>
      mem_bInter fun s hs => s.add_mem (mem_Interβ.1 hx s hs) (mem_Interβ.1 hy s hs)β©β©

theorem mem_Inf {x : E} {S : Set (ConvexCone π E)} : x β inf S β β, β s β S, β, x β s :=
  mem_Interβ

variable (π)

instance : HasBot (ConvexCone π E) :=
  β¨β¨β, fun c hc x => False.elim, fun x => False.elimβ©β©

theorem mem_bot (x : E) : (x β (β₯ : ConvexCone π E)) = False :=
  rfl

instance : HasTop (ConvexCone π E) :=
  β¨β¨Univ, fun c hc x hx => mem_univ _, fun x hx y hy => mem_univ _β©β©

theorem mem_top (x : E) : x β (β€ : ConvexCone π E) :=
  mem_univ x

instance : CompleteLattice (ConvexCone π E) :=
  { PartialOrderβ.lift (coe : ConvexCone π E β Set E) fun a b => ext' with le := (Β· β€ Β·), lt := (Β· < Β·), bot := β₯,
    bot_le := fun S x => False.elim, top := β€, le_top := fun S x hx => mem_top π x, inf := (Β·βΒ·), inf := HasInfβ.inf,
    sup := fun a b => inf { x | a β€ x β§ b β€ x }, sup := fun s => inf { T | β, β S β s, β, S β€ T },
    le_sup_left := fun a b => fun x hx => mem_Inf.2 fun s hs => hs.1 hx,
    le_sup_right := fun a b => fun x hx => mem_Inf.2 fun s hs => hs.2 hx,
    sup_le := fun a b c ha hb x hx => mem_Inf.1 hx c β¨ha, hbβ©, le_inf := fun a b c ha hb x hx => β¨ha hx, hb hxβ©,
    inf_le_left := fun a b x => And.left, inf_le_right := fun a b x => And.right,
    le_Sup := fun s p hs x hx => mem_Inf.2 fun t ht => ht p hs hx, Sup_le := fun s p hs x hx => mem_Inf.1 hx p hs,
    le_Inf := fun s a ha x hx => mem_Inf.2 fun t ht => ha t ht hx, Inf_le := fun s a ha x hx => mem_Inf.1 hx _ ha }

instance : Inhabited (ConvexCone π E) :=
  β¨β₯β©

end HasSmul

section Module

variable [Module π E] (S : ConvexCone π E)

protected theorem convex : Convex π (S : Set E) :=
  convex_iff_forall_pos.2 fun x y hx hy a b ha hb hab => S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

end Module

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField π]

section AddCommMonoidβ

variable [AddCommMonoidβ E] [AddCommMonoidβ F] [AddCommMonoidβ G]

section MulAction

variable [MulAction π E] (S : ConvexCone π E)

theorem smul_mem_iff {c : π} (hc : 0 < c) {x : E} : c β’ x β S β x β S :=
  β¨fun h => inv_smul_smulβ hc.ne' x βΈ S.smul_mem (inv_pos.2 hc) h, S.smul_mem hcβ©

end MulAction

section Module

variable [Module π E] [Module π F] [Module π G]

/-- The image of a convex cone under a `π`-linear map is a convex cone. -/
def map (f : E ββ[π] F) (S : ConvexCone π E) : ConvexCone π F where
  Carrier := f '' S
  smul_mem' := fun c hc y β¨x, hx, hyβ© => hy βΈ f.map_smul c x βΈ mem_image_of_mem f (S.smul_mem hc hx)
  add_mem' := fun yβ β¨xβ, hxβ, hyββ© yβ β¨xβ, hxβ, hyββ© =>
    hyβ βΈ hyβ βΈ f.map_add xβ xβ βΈ mem_image_of_mem f (S.add_mem hxβ hxβ)

theorem map_map (g : F ββ[π] G) (f : E ββ[π] F) (S : ConvexCone π E) : (S.map f).map g = S.map (g.comp f) :=
  ext' <| image_image g f S

@[simp]
theorem map_id (S : ConvexCone π E) : S.map LinearMap.id = S :=
  ext' <| image_id _

/-- The preimage of a convex cone under a `π`-linear map is a convex cone. -/
def comap (f : E ββ[π] F) (S : ConvexCone π F) : ConvexCone π E where
  Carrier := f β»ΒΉ' S
  smul_mem' := fun c hc x hx => by
    rw [mem_preimage, f.map_smul c]
    exact S.smul_mem hc hx
  add_mem' := fun x hx y hy => by
    rw [mem_preimage, f.map_add]
    exact S.add_mem hx hy

@[simp]
theorem comap_id (S : ConvexCone π E) : S.comap LinearMap.id = S :=
  ext' preimage_id

theorem comap_comap (g : F ββ[π] G) (f : E ββ[π] F) (S : ConvexCone π G) : (S.comap g).comap f = S.comap (g.comp f) :=
  ext' <| preimage_comp.symm

@[simp]
theorem mem_comap {f : E ββ[π] F} {S : ConvexCone π F} {x : E} : x β S.comap f β f x β S :=
  Iff.rfl

end Module

end AddCommMonoidβ

section OrderedAddCommGroup

variable [OrderedAddCommGroup E] [Module π E]

/-- Constructs an ordered module given an `ordered_add_comm_group`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
theorem to_ordered_smul (S : ConvexCone π E) (h : β x y : E, x β€ y β y - x β S) : OrderedSmul π E :=
  OrderedSmul.mk'
    (by
      intro x y z xy hz
      rw [h (z β’ x) (z β’ y), β smul_sub z y x]
      exact smul_mem S hz ((h x y).mp xy.le))

end OrderedAddCommGroup

end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable [OrderedSemiring π]

section AddCommMonoidβ

variable [AddCommMonoidβ E] [HasSmul π E] (S : ConvexCone π E)

/-- A convex cone is pointed if it includes `0`. -/
def Pointed (S : ConvexCone π E) : Prop :=
  (0 : E) β S

/-- A convex cone is blunt if it doesn't include `0`. -/
def Blunt (S : ConvexCone π E) : Prop :=
  (0 : E) β S

theorem pointed_iff_not_blunt (S : ConvexCone π E) : S.Pointed β Β¬S.Blunt :=
  β¨fun hβ hβ => hβ hβ, not_not.mpβ©

theorem blunt_iff_not_pointed (S : ConvexCone π E) : S.Blunt β Β¬S.Pointed := by
  rw [pointed_iff_not_blunt, not_not]

end AddCommMonoidβ

section AddCommGroupβ

variable [AddCommGroupβ E] [HasSmul π E] (S : ConvexCone π E)

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def Flat : Prop :=
  β x β S, x β  (0 : E) β§ -x β S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def Salient : Prop :=
  β, β x β S, β, x β  (0 : E) β -x β S

theorem salient_iff_not_flat (S : ConvexCone π E) : S.Salient β Β¬S.Flat := by
  constructor
  Β· rintro hβ β¨x, xs, Hβ, Hββ©
    exact hβ x xs Hβ Hβ
    
  Β· intro h
    unfold flat  at h
    push_neg  at h
    exact h
    

/-- A flat cone is always pointed (contains `0`). -/
theorem Flat.pointed {S : ConvexCone π E} (hS : S.Flat) : S.Pointed := by
  obtain β¨x, hx, _, hxnegβ© := hS
  rw [pointed, β add_neg_selfβ x]
  exact add_mem S hx hxneg

/-- A blunt cone (one not containing `0`) is always salient. -/
theorem Blunt.salient {S : ConvexCone π E} : S.Blunt β S.Salient := by
  rw [salient_iff_not_flat, blunt_iff_not_pointed]
  exact mt flat.pointed

/-- A pointed convex cone defines a preorder. -/
def toPreorder (hβ : S.Pointed) : Preorderβ E where
  le := fun x y => y - x β S
  le_refl := fun x => by
    change x - x β S <;> rw [sub_self x] <;> exact hβ
  le_trans := fun x y z xy zy => by
    simpa using add_mem S zy xy

/-- A pointed and salient cone defines a partial order. -/
def toPartialOrder (hβ : S.Pointed) (hβ : S.Salient) : PartialOrderβ E :=
  { toPreorder S hβ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a β  0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := hβ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

/-- A pointed and salient cone defines an `ordered_add_comm_group`. -/
def toOrderedAddCommGroup (hβ : S.Pointed) (hβ : S.Salient) : OrderedAddCommGroup E :=
  { toPartialOrder S hβ hβ,
    show AddCommGroupβ E by
      infer_instance with
    add_le_add_left := by
      intro a b hab c
      change c + b - (c + a) β S
      rw [add_sub_add_left_eq_sub]
      exact hab }

end AddCommGroupβ

end OrderedSemiring

/-! ### Positive cone of an ordered module -/


section PositiveCone

variable (π E) [OrderedSemiring π] [OrderedAddCommGroup E] [Module π E] [OrderedSmul π E]

/-- The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positiveCone : ConvexCone π E where
  Carrier := { x | 0 β€ x }
  smul_mem' := by
    rintro c hc x (hx : _ β€ _)
    rw [β smul_zero c]
    exact smul_le_smul_of_nonneg hx hc.le
  add_mem' := fun x (hx : _ β€ _) y (hy : _ β€ _) => add_nonneg hx hy

/-- The positive cone of an ordered module is always salient. -/
theorem salient_positive_cone : Salient (positiveCone π E) := fun x xs hx hx' =>
  lt_irreflβ (0 : E)
    (calc
      0 < x := lt_of_le_of_neβ xs hx.symm
      _ β€ x + -x := le_add_of_nonneg_right hx'
      _ = 0 := add_neg_selfβ x
      )

/-- The positive cone of an ordered module is always pointed. -/
theorem pointed_positive_cone : Pointed (positiveCone π E) :=
  le_reflβ 0

end PositiveCone

end ConvexCone

/-! ### Cone over a convex set -/


section ConeFromConvex

variable [LinearOrderedField π] [OrderedAddCommGroup E] [Module π E]

namespace Convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def toCone (s : Set E) (hs : Convex π s) : ConvexCone π E := by
  apply ConvexCone.mk (β (c : π) (H : 0 < c), c β’ s) <;> simp only [β mem_Union, β mem_smul_set]
  Β· rintro c c_pos _ β¨c', c'_pos, x, hx, rflβ©
    exact β¨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symmβ©
    
  Β· rintro _ β¨cx, cx_pos, x, hx, rflβ© _ β¨cy, cy_pos, y, hy, rflβ©
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine' β¨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, _β©
    simp only [β smul_add, β smul_smul, β mul_div_assoc', β mul_div_cancel_left _ this.ne']
    

variable {s : Set E} (hs : Convex π s) {x : E}

theorem mem_to_cone : x β hs.toCone s β β c : π, 0 < c β§ β y β s, c β’ y = x := by
  simp only [β to_cone, β ConvexCone.mem_mk, β mem_Union, β mem_smul_set, β eq_comm, β exists_prop]

theorem mem_to_cone' : x β hs.toCone s β β c : π, 0 < c β§ c β’ x β s := by
  refine' hs.mem_to_cone.trans β¨_, _β©
  Β· rintro β¨c, hc, y, hy, rflβ©
    exact
      β¨cβ»ΒΉ, inv_pos.2 hc, by
        rwa [smul_smul, inv_mul_cancel hc.ne', one_smul]β©
    
  Β· rintro β¨c, hc, hcxβ©
    exact
      β¨cβ»ΒΉ, inv_pos.2 hc, _, hcx, by
        rw [smul_smul, inv_mul_cancel hc.ne', one_smul]β©
    

theorem subset_to_cone : s β hs.toCone s := fun x hx =>
  hs.mem_to_cone'.2
    β¨1, zero_lt_one, by
      rwa [one_smul]β©

/-- `hs.to_cone s` is the least cone that includes `s`. -/
theorem to_cone_is_least : IsLeast { t : ConvexCone π E | s β t } (hs.toCone s) := by
  refine' β¨hs.subset_to_cone, fun t ht x hx => _β©
  rcases hs.mem_to_cone.1 hx with β¨c, hc, y, hy, rflβ©
  exact t.smul_mem hc (ht hy)

theorem to_cone_eq_Inf : hs.toCone s = inf { t : ConvexCone π E | s β t } :=
  hs.to_cone_is_least.IsGlb.Inf_eq.symm

end Convex

theorem convex_hull_to_cone_is_least (s : Set E) :
    IsLeast { t : ConvexCone π E | s β t } ((convex_convex_hull π s).toCone _) := by
  convert (convex_convex_hull π s).to_cone_is_least
  ext t
  exact β¨fun h => convex_hull_min h t.convex, (subset_convex_hull π s).transβ©

theorem convex_hull_to_cone_eq_Inf (s : Set E) :
    (convex_convex_hull π s).toCone _ = inf { t : ConvexCone π E | s β t } :=
  (convex_hull_to_cone_is_least s).IsGlb.Inf_eq.symm

end ConeFromConvex

/-!
### M. Riesz extension theorem

Given a convex cone `s` in a vector space `E`, a submodule `p`, and a linear `f : p β β`, assume
that `f` is nonnegative on `p β© s` and `p + s = E`. Then there exists a globally defined linear
function `g : E β β` that agrees with `f` on `p`, and is nonnegative on `s`.

We prove this theorem using Zorn's lemma. `riesz_extension.step` is the main part of the proof.
It says that if the domain `p` of `f` is not the whole space, then `f` can be extended to a larger
subspace `p β span β {y}` without breaking the non-negativity condition.

In `riesz_extension.exists_top` we use Zorn's lemma to prove that we can extend `f`
to a linear map `g` on `β€ : submodule E`. Mathematically this is the same as a linear map on `E`
but in Lean `β€ : submodule E` is isomorphic but is not equal to `E`. In `riesz_extension`
we use this isomorphism to prove the theorem.
-/


variable [AddCommGroupβ E] [Module β E]

namespace riesz_extension

open Submodule

variable (s : ConvexCone β E) (f : LinearPmap β E β)

/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain β β`, assume that `f` is nonnegative on `f.domain β© p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
theorem step (nonneg : β x : f.domain, (x : E) β s β 0 β€ f x) (dense : β y, β x : f.domain, (x : E) + y β s)
    (hdom : f.domain β  β€) : β g, f < g β§ β x : g.domain, (x : E) β s β 0 β€ g x := by
  obtain β¨y, -, hyβ© : β (y : E)(h : y β β€), y β f.domain :=
    @SetLike.exists_of_lt (Submodule β E) _ _ _ _ (lt_top_iff_ne_top.2 hdom)
  obtain β¨c, le_c, c_leβ© :
    β c, (β x : f.domain, -(x : E) - y β s β f x β€ c) β§ β x : f.domain, (x : E) + y β s β c β€ f x := by
    set Sp := f '' { x : f.domain | (x : E) + y β s }
    set Sn := f '' { x : f.domain | -(x : E) - y β s }
    suffices (UpperBounds Sn β© LowerBounds Sp).Nonempty by
      simpa only [β Set.Nonempty, β UpperBounds, β LowerBounds, β ball_image_iff] using this
    refine' exists_between_of_forall_le (nonempty.image f _) (nonempty.image f (Dense y)) _
    Β· rcases Dense (-y) with β¨x, hxβ©
      rw [β neg_negβ x, AddSubgroupClass.coe_neg, β sub_eq_add_neg] at hx
      exact β¨_, hxβ©
      
    rintro a β¨xn, hxn, rflβ© b β¨xp, hxp, rflβ©
    have := s.add_mem hxp hxn
    rw [add_assocβ, add_sub_cancel'_right, β sub_eq_add_neg, β AddSubgroupClass.coe_sub] at this
    replace := nonneg _ this
    rwa [f.map_sub, sub_nonneg] at this
  have hy' : y β  0 := fun hyβ => hy (hyβ.symm βΈ zero_mem _)
  refine' β¨f.sup_span_singleton y (-c) hy, _, _β©
  Β· refine' lt_iff_le_not_leβ.2 β¨f.left_le_sup _ _, fun H => _β©
    replace H := linear_pmap.domain_mono.monotone H
    rw [LinearPmap.domain_sup_span_singleton, sup_le_iff, span_le, singleton_subset_iff] at H
    exact hy H.2
    
  Β· rintro β¨z, hzβ© hzs
    rcases mem_sup.1 hz with β¨x, hx, y', hy', rflβ©
    rcases mem_span_singleton.1 hy' with β¨r, rflβ©
    simp only [β Subtype.coe_mk] at hzs
    erw [LinearPmap.sup_span_singleton_apply_mk _ _ _ _ _ hx, smul_neg, β sub_eq_add_neg, sub_nonneg]
    rcases lt_trichotomyβ r 0 with (hr | hr | hr)
    Β· have : -(rβ»ΒΉ β’ x) - y β s := by
        rwa [β s.smul_mem_iff (neg_pos.2 hr), smul_sub, smul_neg, neg_smul, neg_negβ, smul_smul, mul_inv_cancel hr.ne,
          one_smul, sub_eq_add_neg, neg_smul, neg_negβ]
      replace := le_c (rβ»ΒΉ β’ β¨x, hxβ©) this
      rwa [β mul_le_mul_left (neg_pos.2 hr), neg_mul, neg_mul, neg_le_neg_iff, f.map_smul, smul_eq_mul, β mul_assoc,
        mul_inv_cancel hr.ne, one_mulβ] at this
      
    Β· subst r
      simp only [β zero_smul, β add_zeroβ] at hzsβ’
      apply nonneg
      exact hzs
      
    Β· have : rβ»ΒΉ β’ x + y β s := by
        rwa [β s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel hr.ne', one_smul]
      replace := c_le (rβ»ΒΉ β’ β¨x, hxβ©) this
      rwa [β mul_le_mul_left hr, f.map_smul, smul_eq_mul, β mul_assoc, mul_inv_cancel hr.ne', one_mulβ] at this
      
    

theorem exists_top (p : LinearPmap β E β) (hp_nonneg : β x : p.domain, (x : E) β s β 0 β€ p x)
    (hp_dense : β y, β x : p.domain, (x : E) + y β s) : β q β₯ p, q.domain = β€ β§ β x : q.domain, (x : E) β s β 0 β€ q x :=
  by
  replace hp_nonneg : p β { p | _ }
  Β· rw [mem_set_of_eq]
    exact hp_nonneg
    
  obtain β¨q, hqs, hpq, hqβ© := zorn_nonempty_partial_orderβ _ _ _ hp_nonneg
  Β· refine' β¨q, hpq, _, hqsβ©
    contrapose! hq
    rcases step s q hqs _ hq with β¨r, hqr, hrβ©
    Β· exact β¨r, hr, hqr.le, hqr.ne'β©
      
    Β· exact fun y =>
        let β¨x, hxβ© := hp_dense y
        β¨of_le hpq.left x, hxβ©
      
    
  Β· intro c hcs c_chain y hy
    clear hp_nonneg hp_dense p
    have cne : c.nonempty := β¨y, hyβ©
    refine' β¨LinearPmap.supβ c c_chain.directed_on, _, fun _ => LinearPmap.le_Sup c_chain.directed_onβ©
    rintro β¨x, hxβ© hxs
    have hdir : DirectedOn (Β· β€ Β·) (LinearPmap.domain '' c) :=
      directed_on_image.2 (c_chain.directed_on.mono linear_pmap.domain_mono.monotone)
    rcases(mem_Sup_of_directed (cne.image _) hdir).1 hx with β¨_, β¨f, hfc, rflβ©, hfxβ©
    have : f β€ LinearPmap.supβ c c_chain.directed_on := LinearPmap.le_Sup _ hfc
    convert β hcs hfc β¨x, hfxβ© hxs
    apply this.2
    rfl
    

end riesz_extension

/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p β β`, assume that `f` is nonnegative on `p β© s` and `p + s = E`. Then
there exists a globally defined linear function `g : E β β` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem riesz_extension (s : ConvexCone β E) (f : LinearPmap β E β) (nonneg : β x : f.domain, (x : E) β s β 0 β€ f x)
    (dense : β y, β x : f.domain, (x : E) + y β s) :
    β g : E ββ[β] β, (β x : f.domain, g x = f x) β§ β, β x β s, β, 0 β€ g x := by
  rcases RieszExtension.exists_top s f nonneg Dense with β¨β¨g_dom, gβ©, β¨hpg, hfgβ©, htop, hgsβ©
  clear hpg
  refine' β¨g ββ β(LinearEquiv.ofTop _ htop).symm, _, _β© <;>
    simp only [β comp_apply, β LinearEquiv.coe_coe, β LinearEquiv.of_top_symm_apply]
  Β· exact fun x => (hfg (Submodule.coe_mk _ _).symm).symm
    
  Β· exact fun x hx => hgs β¨x, _β© hx
    

/-- **Hahn-Banach theorem**: if `N : E β β` is a sublinear map, `f` is a linear map
defined on a subspace of `E`, and `f x β€ N x` for all `x` in the domain of `f`,
then `f` can be extended to the whole space to a linear map `g` such that `g x β€ N x`
for all `x`. -/
theorem exists_extension_of_le_sublinear (f : LinearPmap β E β) (N : E β β)
    (N_hom : β c : β, 0 < c β β x, N (c β’ x) = c * N x) (N_add : β x y, N (x + y) β€ N x + N y)
    (hf : β x : f.domain, f x β€ N x) : β g : E ββ[β] β, (β x : f.domain, g x = f x) β§ β x, g x β€ N x := by
  let s : ConvexCone β (E Γ β) :=
    { Carrier := { p : E Γ β | N p.1 β€ p.2 },
      smul_mem' := fun c hc p hp =>
        calc
          N (c β’ p.1) = c * N p.1 := N_hom c hc p.1
          _ β€ c * p.2 := mul_le_mul_of_nonneg_left hp hc.le
          ,
      add_mem' := fun x hx y hy => (N_add _ _).trans (add_le_add hx hy) }
  obtain β¨g, g_eq, g_nonnegβ© := riesz_extension s ((-f).coprod (linear_map.id.to_pmap β€)) _ _ <;>
    try
      simp only [β LinearPmap.coprod_apply, β to_pmap_apply, β id_apply, β LinearPmap.neg_apply, sub_eq_neg_add, β
        sub_nonneg, β Subtype.coe_mk] at *
  replace g_eq : β (x : f.domain) (y : β), g (x, y) = y - f x
  Β· intro x y
    simpa only [β Subtype.coe_mk, β Subtype.coe_eta] using g_eq β¨(x, y), β¨x.2, trivialββ©β©
    
  Β· refine' β¨-g.comp (inl β E β), _, _β© <;> simp only [β neg_apply, β inl_apply, β comp_apply]
    Β· intro x
      simp [β g_eq x 0]
      
    Β· intro x
      have A : (x, N x) = (x, 0) + (0, N x) := by
        simp
      have B := g_nonneg β¨x, N xβ© (le_reflβ (N x))
      rw [A, map_add, β neg_le_iff_add_nonneg'] at B
      have C := g_eq 0 (N x)
      simp only [β Submodule.coe_zero, β f.map_zero, β sub_zero] at C
      rwa [β C]
      
    
  Β· exact fun x hx => le_transβ (hf _) hx
    
  Β· rintro β¨x, yβ©
    refine' β¨β¨(0, N x - y), β¨f.domain.zero_mem, trivialββ©β©, _β©
    simp only [β ConvexCone.mem_mk, β mem_set_of_eq, β Subtype.coe_mk, β Prod.fst_add, β Prod.snd_add, β zero_addβ, β
      sub_add_cancel]
    

/-! ### The dual cone -/


section Dual

variable {H : Type _} [InnerProductSpace β H] (s t : Set H)

open RealInnerProductSpace

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 β€ βͺ x, y β«`. -/
def Set.innerDualCone (s : Set H) : ConvexCone β H where
  Carrier := { y | β, β x β s, β, 0 β€ βͺx, yβ« }
  smul_mem' := fun c hc y hy x hx => by
    rw [real_inner_smul_right]
    exact mul_nonneg hc.le (hy x hx)
  add_mem' := fun u hu v hv x hx => by
    rw [inner_add_right]
    exact add_nonneg (hu x hx) (hv x hx)

theorem mem_inner_dual_cone (y : H) (s : Set H) : y β s.innerDualCone β β, β x β s, β, 0 β€ βͺx, yβ« := by
  rfl

@[simp]
theorem inner_dual_cone_empty : (β : Set H).innerDualCone = β€ :=
  ConvexCone.ext' (eq_univ_of_forall fun x y hy => False.elim (Set.not_mem_empty _ hy))

theorem inner_dual_cone_le_inner_dual_cone (h : t β s) : s.innerDualCone β€ t.innerDualCone := fun y hy x hx =>
  hy x (h hx)

theorem pointed_inner_dual_cone : s.innerDualCone.Pointed := fun x hx => by
  rw [inner_zero_right]

end Dual

