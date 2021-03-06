/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury G. Kudryashov
-/
import Mathbin.Topology.ContinuousOn
import Mathbin.Data.Setoid.Basic
import Mathbin.Tactic.Tfae

/-!
# Inseparable points in a topological space

In this file we define

* `specializes` (notation: `x โคณ y`) : a relation saying that `๐ x โค ๐ y`;

* `inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `inseparable_setoid X`: same relation, as a `setoid`;

* `separation_quotient X`: the quotient of `X` by its `inseparable_setoid`.

We also prove various basic properties of the relation `inseparable`.

## Notations

- `x โคณ y`: notation for `specializes x y`;
- `x ~ y` is used as a local notation for `inseparable x y`;
- `๐ x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/


open Set Filter Function

open TopologicalSpace

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {s : Set X} {f : X โ Y}

/-!
### `specializes` relation
-/


/-- `x` specializes to `y` (notation: `x โคณ y`) if either of the following equivalent properties
hold:

* `๐ x โค ๐ y`; this property is used as the definition;
* `pure x โค ๐ y`; in other words, any neighbourhood of `y` contains `x`;
* `y โ closure {x}`;
* `closure {y} โ closure {x}`;
* for any closed set `s` we have `x โ s โ y โ s`;
* for any open set `s` we have `y โ s โ x โ s`;
* `y` is a cluster point of the filter `pure x = ๐ {x}`.

This relation defines a `preorder` on `X`. If `X` is a Tโ space, then this preorder is a partial
order. If `X` is a Tโ space, then this partial order is trivial : `x โคณ y โ x = y`. -/
def Specializes (x y : X) : Prop :=
  ๐ x โค ๐ y

-- mathport name: ยซexpr โคณ ยป
infixl:300 " โคณ " => Specializes

/-- A collection of equivalent definitions of `x โคณ y`. The public API is given by `iff` lemmas
below. -/
theorem specializes_tfae (x y : X) :
    Tfae
      [x โคณ y, pure x โค ๐ y, โ s : Set X, IsOpen s โ y โ s โ x โ s, โ s : Set X, IsClosed s โ x โ s โ y โ s,
        y โ Closure ({x} : Set X), Closure ({y} : Set X) โ Closure {x}, ClusterPt y (pure x)] :=
  by
  tfae_have 1 โ 2
  exact (pure_le_nhds _).trans
  tfae_have 2 โ 3
  exact fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 โ 4
  exact fun h s hsc hx => of_not_not fun hy => h (sแถ) hsc.is_open_compl hy hx
  tfae_have 4 โ 5
  exact fun h => h _ is_closed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 โ 5
  exact is_closed_closure.closure_subset_iff.trans singleton_subset_iff
  tfae_have 5 โ 7
  ยท rw [mem_closure_iff_cluster_pt, principal_singleton]
    
  tfae_have 5 โ 1
  ยท refine' fun h => (nhds_basis_opens _).ge_iff.2 _
    rintro s โจhy, hoโฉ
    rcases mem_closure_iff.1 h s ho hy with โจz, hxs, rfl : z = xโฉ
    exact ho.mem_nhds hxs
    
  tfae_finish

theorem specializes_iff_nhds : x โคณ y โ ๐ x โค ๐ y :=
  Iff.rfl

theorem specializes_iff_pure : x โคณ y โ pure x โค ๐ y :=
  (specializes_tfae x y).out 0 1

alias specializes_iff_nhds โ Specializes.nhds_le_nhds _

alias specializes_iff_pure โ Specializes.pure_le_nhds _

theorem specializes_iff_forall_open : x โคณ y โ โ s : Set X, IsOpen s โ y โ s โ x โ s :=
  (specializes_tfae x y).out 0 2

theorem Specializes.mem_open (h : x โคณ y) (hs : IsOpen s) (hy : y โ s) : x โ s :=
  specializes_iff_forall_open.1 h s hs hy

theorem IsOpen.not_specializes (hs : IsOpen s) (hx : x โ s) (hy : y โ s) : ยฌx โคณ y := fun h => hx <| h.mem_open hs hy

theorem specializes_iff_forall_closed : x โคณ y โ โ s : Set X, IsClosed s โ x โ s โ y โ s :=
  (specializes_tfae x y).out 0 3

theorem Specializes.mem_closed (h : x โคณ y) (hs : IsClosed s) (hx : x โ s) : y โ s :=
  specializes_iff_forall_closed.1 h s hs hx

theorem IsClosed.not_specializes (hs : IsClosed s) (hx : x โ s) (hy : y โ s) : ยฌx โคณ y := fun h =>
  hy <| h.mem_closed hs hx

theorem specializes_iff_mem_closure : x โคณ y โ y โ Closure ({x} : Set X) :=
  (specializes_tfae x y).out 0 4

alias specializes_iff_mem_closure โ Specializes.mem_closure _

theorem specializes_iff_closure_subset : x โคณ y โ Closure ({y} : Set X) โ Closure {x} :=
  (specializes_tfae x y).out 0 5

alias specializes_iff_closure_subset โ Specializes.closure_subset _

theorem specializes_rfl : x โคณ x :=
  le_rfl

@[refl]
theorem specializes_refl (x : X) : x โคณ x :=
  specializes_rfl

@[trans]
theorem Specializes.trans : x โคณ y โ y โคณ z โ x โคณ z :=
  le_transโ

theorem specializes_of_nhds_within (hโ : ๐[s] x โค ๐[s] y) (hโ : x โ s) : x โคณ y :=
  specializes_iff_pure.2 <|
    calc
      pure x โค ๐[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 hโ)
      _ โค ๐[s] y := hโ
      _ โค ๐ y := inf_le_left
      

theorem Specializes.map_of_continuous_at (h : x โคณ y) (hy : ContinuousAt f y) : f x โคณ f y :=
  specializes_iff_pure.2 fun s hs => mem_pure.2 <| mem_preimage.1 <| mem_of_mem_nhds <| hy.mono_left h hs

theorem Specializes.map (h : x โคณ y) (hf : Continuous f) : f x โคณ f y :=
  h.map_of_continuous_at hf.ContinuousAt

theorem Inducing.specializes_iff (hf : Inducing f) : f x โคณ f y โ x โคณ y := by
  simp only [โ specializes_iff_mem_closure, โ hf.closure_eq_preimage_closure_image, โ image_singleton, โ mem_preimage]

theorem subtype_specializes_iff {p : X โ Prop} (x y : Subtype p) : x โคณ y โ (x : X) โคณ y :=
  inducing_coe.specializes_iff.symm

variable (X)

/-- Specialization forms a preorder on the topological space. -/
def specializationPreorder : Preorderโ X :=
  { Preorderโ.lift (OrderDual.toDual โ ๐) with le := fun x y => y โคณ x, lt := fun x y => y โคณ x โง ยฌx โคณ y }

variable {X}

/-- A continuous function is monotone with respect to the specialization preorders on the domain and
the codomain. -/
theorem Continuous.specialization_monotone (hf : Continuous f) :
    @Monotone _ _ (specializationPreorder X) (specializationPreorder Y) f := fun x y h => h.map hf

/-!
### `inseparable` relation
-/


/-- Two points `x` and `y` in a topological space are `inseparable` if any of the following
equivalent properties hold:

- `๐ x = ๐ y`; we use this property as the definition;
- for any open set `s`, `x โ s โ y โ s`, see `inseparable_iff_open`;
- for any closed set `s`, `x โ s โ y โ s`, see `inseparable_iff_closed`;
- `x โ closure {y}` and `y โ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.
-/
def Inseparable (x y : X) : Prop :=
  ๐ x = ๐ y

-- mathport name: ยซexpr ~ ยป
local infixl:0 " ~ " => Inseparable

theorem inseparable_def : (x ~ y) โ ๐ x = ๐ y :=
  Iff.rfl

theorem inseparable_iff_specializes_and : (x ~ y) โ x โคณ y โง y โคณ x :=
  le_antisymm_iffโ

theorem Inseparable.specializes (h : x ~ y) : x โคณ y :=
  h.le

theorem Inseparable.specializes' (h : x ~ y) : y โคณ x :=
  h.Ge

theorem Specializes.antisymm (hโ : x โคณ y) (hโ : y โคณ x) : x ~ y :=
  le_antisymmโ hโ hโ

theorem inseparable_iff_forall_open : (x ~ y) โ โ s : Set X, IsOpen s โ (x โ s โ y โ s) := by
  simp only [โ inseparable_iff_specializes_and, โ specializes_iff_forall_open, forall_and_distrib, iff_def, โ Iff.comm]

theorem not_inseparable_iff_exists_open : ยฌ(x ~ y) โ โ s : Set X, IsOpen s โง Xorโ (x โ s) (y โ s) := by
  simp [โ inseparable_iff_forall_open, xor_iff_not_iff]

theorem inseparable_iff_forall_closed : (x ~ y) โ โ s : Set X, IsClosed s โ (x โ s โ y โ s) := by
  simp only [โ inseparable_iff_specializes_and, โ specializes_iff_forall_closed, forall_and_distrib, iff_def]

theorem inseparable_iff_mem_closure : (x ~ y) โ x โ Closure ({y} : Set X) โง y โ Closure ({x} : Set X) :=
  inseparable_iff_specializes_and.trans <| by
    simp only [โ specializes_iff_mem_closure, โ and_comm]

theorem inseparable_iff_closure_eq : (x ~ y) โ Closure ({x} : Set X) = Closure {y} := by
  simp only [โ inseparable_iff_specializes_and, โ specializes_iff_closure_subset, subset_antisymm_iff, โ eq_comm]

theorem inseparable_of_nhds_within_eq (hx : x โ s) (hy : y โ s) (h : ๐[s] x = ๐[s] y) : x ~ y :=
  (specializes_of_nhds_within h.le hx).antisymm (specializes_of_nhds_within h.Ge hy)

theorem Inducing.inseparable_iff (hf : Inducing f) : (f x ~ f y) โ (x ~ y) := by
  simp only [โ inseparable_iff_specializes_and, โ hf.specializes_iff]

theorem subtype_inseparable_iff {p : X โ Prop} (x y : Subtype p) : (x ~ y) โ ((x : X) ~ y) :=
  inducing_coe.inseparable_iff.symm

namespace Inseparable

@[refl]
theorem refl (x : X) : x ~ x :=
  Eq.refl (๐ x)

theorem rfl : x ~ x :=
  refl x

@[symm]
theorem symm (h : x ~ y) : y ~ x :=
  h.symm

@[trans]
theorem trans (hโ : x ~ y) (hโ : y ~ z) : x ~ z :=
  hโ.trans hโ

theorem nhds_eq (h : x ~ y) : ๐ x = ๐ y :=
  h

theorem mem_open_iff (h : x ~ y) (hs : IsOpen s) : x โ s โ y โ s :=
  inseparable_iff_forall_open.1 h s hs

theorem mem_closed_iff (h : x ~ y) (hs : IsClosed s) : x โ s โ y โ s :=
  inseparable_iff_forall_closed.1 h s hs

theorem map_of_continuous_at (h : x ~ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y) : f x ~ f y :=
  (h.Specializes.map_of_continuous_at hy).antisymm (h.specializes'.map_of_continuous_at hx)

theorem map (h : x ~ y) (hf : Continuous f) : f x ~ f y :=
  h.map_of_continuous_at hf.ContinuousAt hf.ContinuousAt

end Inseparable

theorem IsClosed.not_inseparable (hs : IsClosed s) (hx : x โ s) (hy : y โ s) : ยฌ(x ~ y) := fun h =>
  hy <| (h.mem_closed_iff hs).1 hx

theorem IsOpen.not_inseparable (hs : IsOpen s) (hx : x โ s) (hy : y โ s) : ยฌ(x ~ y) := fun h =>
  hy <| (h.mem_open_iff hs).1 hx

/-!
### Separation quotient

In this section we define the quotient of a topological space by the `inseparable` relation.
-/


variable (X)

/-- A `setoid` version of `inseparable`, used to define the `separation_quotient`. -/
def inseparableSetoid : Setoidโ X :=
  { Setoidโ.comap ๐ โฅ with R := (ยท ~ ยท) }

/-- The quotient of a topological space by its `inseparable_setoid`. This quotient is guaranteed to
be a Tโ space. -/
def SeparationQuotient :=
  Quotientโ (inseparableSetoid X)deriving TopologicalSpace

variable {X}

namespace SeparationQuotient

/-- The natural map from a topological space to its separation quotient. -/
def mk : X โ SeparationQuotient X :=
  Quotientโ.mk'

theorem quotient_map_mk : QuotientMap (mk : X โ SeparationQuotient X) :=
  quotient_map_quot_mk

theorem continuous_mk : Continuous (mk : X โ SeparationQuotient X) :=
  continuous_quot_mk

@[simp]
theorem mk_eq_mk : mk x = mk y โ (x ~ y) :=
  Quotientโ.eq'

theorem surjective_mk : Surjective (mk : X โ SeparationQuotient X) :=
  surjective_quot_mk _

@[simp]
theorem range_mk : Range (mk : X โ SeparationQuotient X) = univ :=
  surjective_mk.range_eq

instance [Nonempty X] : Nonempty (SeparationQuotient X) :=
  Nonempty.map mk โน_โบ

instance [Inhabited X] : Inhabited (SeparationQuotient X) :=
  โจmk defaultโฉ

instance [Subsingleton X] : Subsingleton (SeparationQuotient X) :=
  surjective_mk.Subsingleton

theorem preimage_image_mk_open (hs : IsOpen s) : mk โปยน' (mk '' s) = s := by
  refine' subset.antisymm _ (subset_preimage_image _ _)
  rintro x โจy, hys, hxyโฉ
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys

theorem is_open_map_mk : IsOpenMap (mk : X โ SeparationQuotient X) := fun s hs =>
  quotient_map_mk.is_open_preimage.1 <| by
    rwa [preimage_image_mk_open hs]

theorem preimage_image_mk_closed (hs : IsClosed s) : mk โปยน' (mk '' s) = s := by
  refine' subset.antisymm _ (subset_preimage_image _ _)
  rintro x โจy, hys, hxyโฉ
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys

theorem inducing_mk : Inducing (mk : X โ SeparationQuotient X) :=
  โจle_antisymmโ (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      โจmk '' s, is_open_map_mk s hs, preimage_image_mk_open hsโฉโฉ

theorem is_closed_map_mk : IsClosedMap (mk : X โ SeparationQuotient X) :=
  inducing_mk.IsClosedMap <| by
    rw [range_mk]
    exact is_closed_univ

theorem map_mk_nhds : map mk (๐ x) = ๐ (mk x) := by
  rw [inducing_mk.nhds_eq_comap, map_comap_of_surjective surjective_mk]

end SeparationQuotient

