/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.Group.InjSurj
import Algebra.BigOperators.Group.List
import Data.List.FinRange
import GroupTheory.GroupAction.Defs
import Algebra.Group.Submonoid.Basic
import Data.SetLike.Basic
import Data.Sigma.Basic

#align_import algebra.graded_monoid from "leanprover-community/mathlib"@"fac369018417f980cec5fcdafc766a69f88d8cfe"

/-!
# Additively-graded multiplicative structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `graded_monoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `graded_monoid.ghas_one A`
* `graded_monoid.ghas_mul A`
* `graded_monoid.gmonoid A`
* `graded_monoid.gcomm_monoid A`

With the `sigma_graded` locale open, these respectively imbue:

* `has_one (graded_monoid A)`
* `has_mul (graded_monoid A)`
* `monoid (graded_monoid A)`
* `comm_monoid (graded_monoid A)`

the base type `A 0` with:

* `graded_monoid.grade_zero.has_one`
* `graded_monoid.grade_zero.has_mul`
* `graded_monoid.grade_zero.monoid`
* `graded_monoid.grade_zero.comm_monoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `graded_monoid.grade_zero.has_smul (A 0)`
* `graded_monoid.grade_zero.mul_action (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `direct_sum.ring` and the rest
of that file.

## Dependent graded products

This also introduces `list.dprod`, which takes the (possibly non-commutative) product of a list
of graded elements of type `A i`. This definition primarily exist to allow `graded_monoid.mk`
and `direct_sum.of` to be pulled outside a product, such as in `graded_monoid.mk_list_dprod` and
`direct_sum.of_list_dprod`.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_one A` (which provides the obvious `graded_monoid.ghas_one A` instance)
* `set_like.has_graded_mul A` (which provides the obvious `graded_monoid.ghas_mul A` instance)
* `set_like.graded_monoid A` (which provides the obvious `graded_monoid.gmonoid A` and
  `graded_monoid.gcomm_monoid A` instances)

which respectively provide the API lemmas

* `set_like.one_mem_graded`
* `set_like.mul_mem_graded`
* `set_like.pow_mem_graded`, `set_like.list_prod_map_mem_graded`

Strictly this last class is unecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `set_like.graded_ring` or similar, as all
the information it would contain is already supplied by `graded_monoid` when `A` is a collection
of objects satisfying `add_submonoid_class` such as `submodule`s. These constructions are explored
in `algebra.direct_sum.internal`.

This file also defines:

* `set_like.is_homogeneous A` (which says that `a` is homogeneous iff `a ∈ A i` for some `i : ι`)
* `set_like.homogeneous_submonoid A`, which is, as the name suggests, the submonoid consisting of
  all the homogeneous elements.

## tags

graded monoid
-/


variable {ι : Type _}

#print GradedMonoid /-
/-- A type alias of sigma types for graded monoids. -/
def GradedMonoid (A : ι → Type _) :=
  Sigma A
#align graded_monoid GradedMonoid
-/

namespace GradedMonoid

instance {A : ι → Type _} [Inhabited ι] [Inhabited (A default)] : Inhabited (GradedMonoid A) :=
  Sigma.inhabited

#print GradedMonoid.mk /-
/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type _} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk
#align graded_monoid.mk GradedMonoid.mk
-/

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _)

#print GradedMonoid.GOne /-
/-- A graded version of `has_one`, which must be of grade 0. -/
class GOne [Zero ι] where
  one : A 0
#align graded_monoid.ghas_one GradedMonoid.GOne
-/

#print GradedMonoid.GOne.toOne /-
/-- `ghas_one` implies `has_one (graded_monoid A)` -/
instance GOne.toOne [Zero ι] [GOne A] : One (GradedMonoid A) :=
  ⟨⟨_, GOne.one⟩⟩
#align graded_monoid.ghas_one.to_has_one GradedMonoid.GOne.toOne
-/

#print GradedMonoid.GMul /-
/-- A graded version of `has_mul`. Multiplication combines grades additively, like
`add_monoid_algebra`. -/
class GMul [Add ι] where
  mul {i j} : A i → A j → A (i + j)
#align graded_monoid.ghas_mul GradedMonoid.GMul
-/

#print GradedMonoid.GMul.toMul /-
/-- `ghas_mul` implies `has_mul (graded_monoid A)`. -/
instance GMul.toMul [Add ι] [GMul A] : Mul (GradedMonoid A) :=
  ⟨fun x y : GradedMonoid A => ⟨_, GMul.mul x.snd y.snd⟩⟩
#align graded_monoid.ghas_mul.to_has_mul GradedMonoid.GMul.toMul
-/

#print GradedMonoid.mk_mul_mk /-
theorem mk_mul_mk [Add ι] [GMul A] {i j} (a : A i) (b : A j) :
    mk i a * mk j b = mk (i + j) (GMul.mul a b) :=
  rfl
#align graded_monoid.mk_mul_mk GradedMonoid.mk_mul_mk
-/

namespace Gmonoid

variable {A} [AddMonoid ι] [GMul A] [GOne A]

#print GradedMonoid.GMonoid.gnpowRec /-
/-- A default implementation of power on a graded monoid, like `npow_rec`.
`gmonoid.gnpow` should be used instead. -/
def gnpowRec : ∀ (n : ℕ) {i}, A i → A (n • i)
  | 0, i, a => cast (congr_arg A (zero_nsmul i).symm) GOne.one
  | n + 1, i, a => cast (congr_arg A (succ_nsmul' i n).symm) (GMul.mul a <| gnpow_rec _ a)
#align graded_monoid.gmonoid.gnpow_rec GradedMonoid.GMonoid.gnpowRec
-/

#print GradedMonoid.GMonoid.gnpowRec_zero /-
@[simp]
theorem gnpowRec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpowRec 0 a.snd) = 1 :=
  Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm
#align graded_monoid.gmonoid.gnpow_rec_zero GradedMonoid.GMonoid.gnpowRec_zero
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_zero'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
unsafe def apply_gnpow_rec_zero_tac : tactic Unit :=
  sorry
#align graded_monoid.gmonoid.apply_gnpow_rec_zero_tac graded_monoid.gmonoid.apply_gnpow_rec_zero_tac

#print GradedMonoid.GMonoid.gnpowRec_succ /-
@[simp]
theorem gnpowRec_succ (n : ℕ) (a : GradedMonoid A) :
    (GradedMonoid.mk _ <| gnpowRec n.succ a.snd) = a * ⟨_, gnpowRec n a.snd⟩ :=
  Sigma.ext (succ_nsmul' _ _) (heq_of_cast_eq _ rfl).symm
#align graded_monoid.gmonoid.gnpow_rec_succ GradedMonoid.GMonoid.gnpowRec_succ
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_succ'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
unsafe def apply_gnpow_rec_succ_tac : tactic Unit :=
  sorry
#align graded_monoid.gmonoid.apply_gnpow_rec_succ_tac graded_monoid.gmonoid.apply_gnpow_rec_succ_tac

end Gmonoid

#print GradedMonoid.GMonoid /-
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic gmonoid.apply_gnpow_rec_zero_tac -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic gmonoid.apply_gnpow_rec_succ_tac -/
/-- A graded version of `monoid`.

Like `monoid.npow`, this has an optional `gmonoid.gnpow` field to allow definitional control of
natural powers of a graded monoid. -/
class GMonoid [AddMonoid ι] extends GMul A, GOne A where
  one_mul (a : GradedMonoid A) : 1 * a = a
  mul_one (a : GradedMonoid A) : a * 1 = a
  mul_assoc (a b c : GradedMonoid A) : a * b * c = a * (b * c)
  gnpow : ∀ (n : ℕ) {i}, A i → A (n • i) := GMonoid.gnpowRec
  gnpow_zero' : ∀ a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1 := by
    run_tac
      gmonoid.apply_gnpow_rec_zero_tac
  gnpow_succ' :
    ∀ (n : ℕ) (a : GradedMonoid A),
      (GradedMonoid.mk _ <| gnpow n.succ a.snd) = a * ⟨_, gnpow n a.snd⟩ := by
    run_tac
      gmonoid.apply_gnpow_rec_succ_tac
#align graded_monoid.gmonoid GradedMonoid.GMonoid
-/

#print GradedMonoid.GMonoid.toMonoid /-
/-- `gmonoid` implies a `monoid (graded_monoid A)`. -/
instance GMonoid.toMonoid [AddMonoid ι] [GMonoid A] : Monoid (GradedMonoid A)
    where
  one := 1
  mul := (· * ·)
  npow n a := GradedMonoid.mk _ (GMonoid.gnpow n a.snd)
  npow_zero a := GMonoid.gnpow_zero' a
  npow_succ n a := GMonoid.gnpow_succ' n a
  one_mul := GMonoid.one_hMul
  mul_one := GMonoid.hMul_one
  mul_assoc := GMonoid.hMul_assoc
#align graded_monoid.gmonoid.to_monoid GradedMonoid.GMonoid.toMonoid
-/

#print GradedMonoid.mk_pow /-
theorem mk_pow [AddMonoid ι] [GMonoid A] {i} (a : A i) (n : ℕ) :
    mk i a ^ n = mk (n • i) (GMonoid.gnpow _ a) :=
  by
  induction' n with n
  · rw [pow_zero]
    exact (gmonoid.gnpow_zero' ⟨_, a⟩).symm
  · rw [pow_succ', n_ih, mk_mul_mk]
    exact (gmonoid.gnpow_succ' n ⟨_, a⟩).symm
#align graded_monoid.mk_pow GradedMonoid.mk_pow
-/

#print GradedMonoid.GCommMonoid /-
/-- A graded version of `comm_monoid`. -/
class GCommMonoid [AddCommMonoid ι] extends GMonoid A where
  mul_comm (a : GradedMonoid A) (b : GradedMonoid A) : a * b = b * a
#align graded_monoid.gcomm_monoid GradedMonoid.GCommMonoid
-/

#print GradedMonoid.GCommMonoid.toCommMonoid /-
/-- `gcomm_monoid` implies a `comm_monoid (graded_monoid A)`, although this is only used as an
instance locally to define notation in `gmonoid` and similar typeclasses. -/
instance GCommMonoid.toCommMonoid [AddCommMonoid ι] [GCommMonoid A] : CommMonoid (GradedMonoid A) :=
  { GMonoid.toMonoid A with mul_comm := GCommMonoid.hMul_comm }
#align graded_monoid.gcomm_monoid.to_comm_monoid GradedMonoid.GCommMonoid.toCommMonoid
-/

end Defs

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

variable (A : ι → Type _)

section One

variable [Zero ι] [GOne A]

#print GradedMonoid.GradeZero.one /-
/-- `1 : A 0` is the value provided in `ghas_one.one`. -/
@[nolint unused_arguments]
instance GradeZero.one : One (A 0) :=
  ⟨GOne.one⟩
#align graded_monoid.grade_zero.has_one GradedMonoid.GradeZero.one
-/

end One

section Mul

variable [AddZeroClass ι] [GMul A]

#print GradedMonoid.GradeZero.smul /-
/-- `(•) : A 0 → A i → A i` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance GradeZero.smul (i : ι) : SMul (A 0) (A i) where smul x y := (zero_add i).rec (GMul.mul x y)
#align graded_monoid.grade_zero.has_smul GradedMonoid.GradeZero.smul
-/

#print GradedMonoid.GradeZero.mul /-
/-- `(*) : A 0 → A 0 → A 0` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance GradeZero.mul : Mul (A 0) where mul := (· • ·)
#align graded_monoid.grade_zero.has_mul GradedMonoid.GradeZero.mul
-/

variable {A}

#print GradedMonoid.mk_zero_smul /-
@[simp]
theorem mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a * mk _ b :=
  Sigma.ext (zero_add _).symm <| eq_rec_hEq _ _
#align graded_monoid.mk_zero_smul GradedMonoid.mk_zero_smul
-/

#print GradedMonoid.GradeZero.smul_eq_mul /-
@[simp]
theorem GradeZero.smul_eq_mul (a b : A 0) : a • b = a * b :=
  rfl
#align graded_monoid.grade_zero.smul_eq_mul GradedMonoid.GradeZero.smul_eq_mul
-/

end Mul

section Monoid

variable [AddMonoid ι] [GMonoid A]

instance : Pow (A 0) ℕ where pow x n := (nsmul_zero n).rec (GMonoid.gnpow n x : A (n • 0))

variable {A}

#print GradedMonoid.mk_zero_pow /-
@[simp]
theorem mk_zero_pow (a : A 0) (n : ℕ) : mk _ (a ^ n) = mk _ a ^ n :=
  Sigma.ext (nsmul_zero n).symm <| eq_rec_hEq _ _
#align graded_monoid.mk_zero_pow GradedMonoid.mk_zero_pow
-/

variable (A)

#print GradedMonoid.GradeZero.monoid /-
/-- The `monoid` structure derived from `gmonoid A`. -/
instance GradeZero.monoid : Monoid (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.monoid GradedMonoid.GradeZero.monoid
-/

end Monoid

section Monoid

variable [AddCommMonoid ι] [GCommMonoid A]

#print GradedMonoid.GradeZero.commMonoid /-
/-- The `comm_monoid` structure derived from `gcomm_monoid A`. -/
instance GradeZero.commMonoid : CommMonoid (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.comm_monoid GradedMonoid.GradeZero.commMonoid
-/

end Monoid

section MulAction

variable [AddMonoid ι] [GMonoid A]

#print GradedMonoid.mkZeroMonoidHom /-
/-- `graded_monoid.mk 0` is a `monoid_hom`, using the `graded_monoid.grade_zero.monoid` structure.
-/
def mkZeroMonoidHom : A 0 →* GradedMonoid A
    where
  toFun := mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul
#align graded_monoid.mk_zero_monoid_hom GradedMonoid.mkZeroMonoidHom
-/

#print GradedMonoid.GradeZero.mulAction /-
/-- Each grade `A i` derives a `A 0`-action structure from `gmonoid A`. -/
instance GradeZero.mulAction {i} : MulAction (A 0) (A i) :=
  letI := MulAction.compHom (GradedMonoid A) (mk_zero_monoid_hom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul
#align graded_monoid.grade_zero.mul_action GradedMonoid.GradeZero.mulAction
-/

end MulAction

end GradeZero

end GradedMonoid

/-! ### Dependent products of graded elements -/


section Dprod

variable {α : Type _} {A : ι → Type _} [AddMonoid ι] [GradedMonoid.GMonoid A]

#print List.dProdIndex /-
/-- The index used by `list.dprod`. Propositionally this is equal to `(l.map fι).sum`, but
definitionally it needs to have a different form to avoid introducing `eq.rec`s in `list.dprod`. -/
def List.dProdIndex (l : List α) (fι : α → ι) : ι :=
  l.foldr (fun i b => fι i + b) 0
#align list.dprod_index List.dProdIndex
-/

#print List.dProdIndex_nil /-
@[simp]
theorem List.dProdIndex_nil (fι : α → ι) : ([] : List α).dProdIndex fι = 0 :=
  rfl
#align list.dprod_index_nil List.dProdIndex_nil
-/

#print List.dProdIndex_cons /-
@[simp]
theorem List.dProdIndex_cons (a : α) (l : List α) (fι : α → ι) :
    (a :: l).dProdIndex fι = fι a + l.dProdIndex fι :=
  rfl
#align list.dprod_index_cons List.dProdIndex_cons
-/

#print List.dProdIndex_eq_map_sum /-
theorem List.dProdIndex_eq_map_sum (l : List α) (fι : α → ι) : l.dProdIndex fι = (l.map fι).Sum :=
  by
  dsimp only [List.dProdIndex]
  induction l
  · simp
  · simp [l_ih]
#align list.dprod_index_eq_map_sum List.dProdIndex_eq_map_sum
-/

#print List.dProd /-
/-- A dependent product for graded monoids represented by the indexed family of types `A i`.
This is a dependent version of `(l.map fA).prod`.

For a list `l : list α`, this computes the product of `fA a` over `a`, where each `fA` is of type
`A (fι a)`. -/
def List.dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) : A (l.dProdIndex fι) :=
  l.foldrRecOn _ _ GradedMonoid.GOne.one fun i x a ha => GradedMonoid.GMul.mul (fA a) x
#align list.dprod List.dProd
-/

#print List.dProd_nil /-
@[simp]
theorem List.dProd_nil (fι : α → ι) (fA : ∀ a, A (fι a)) :
    (List.nil : List α).dProd fι fA = GradedMonoid.GOne.one :=
  rfl
#align list.dprod_nil List.dProd_nil
-/

#print List.dProd_cons /-
-- the `( : _)` in this lemma statement results in the type on the RHS not being unfolded, which
-- is nicer in the goal view.
@[simp]
theorem List.dProd_cons (fι : α → ι) (fA : ∀ a, A (fι a)) (a : α) (l : List α) :
    (a :: l).dProd fι fA = (GradedMonoid.GMul.mul (fA a) (l.dProd fι fA) : _) :=
  rfl
#align list.dprod_cons List.dProd_cons
-/

#print GradedMonoid.mk_list_dProd /-
theorem GradedMonoid.mk_list_dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    GradedMonoid.mk _ (l.dProd fι fA) = (l.map fun a => GradedMonoid.mk (fι a) (fA a)).Prod :=
  by
  induction l
  · simp; rfl
  · simp [← l_ih, GradedMonoid.mk_mul_mk, List.prod_cons]
    rfl
#align graded_monoid.mk_list_dprod GradedMonoid.mk_list_dProd
-/

#print GradedMonoid.list_prod_map_eq_dProd /-
/-- A variant of `graded_monoid.mk_list_dprod` for rewriting in the other direction. -/
theorem GradedMonoid.list_prod_map_eq_dProd (l : List α) (f : α → GradedMonoid A) :
    (l.map f).Prod = GradedMonoid.mk _ (l.dProd (fun i => (f i).1) fun i => (f i).2) :=
  by
  rw [GradedMonoid.mk_list_dProd, GradedMonoid.mk]
  simp_rw [Sigma.eta]
#align graded_monoid.list_prod_map_eq_dprod GradedMonoid.list_prod_map_eq_dProd
-/

#print GradedMonoid.list_prod_ofFn_eq_dProd /-
theorem GradedMonoid.list_prod_ofFn_eq_dProd {n : ℕ} (f : Fin n → GradedMonoid A) :
    (List.ofFn f).Prod =
      GradedMonoid.mk _ ((List.finRange n).dProd (fun i => (f i).1) fun i => (f i).2) :=
  by rw [List.ofFn_eq_map, GradedMonoid.list_prod_map_eq_dProd]
#align graded_monoid.list_prod_of_fn_eq_dprod GradedMonoid.list_prod_ofFn_eq_dProd
-/

end Dprod

/-! ### Concrete instances -/


section

variable (ι) {R : Type _}

#print One.gOne /-
@[simps one]
instance One.gOne [Zero ι] [One R] : GradedMonoid.GOne fun i : ι => R where one := 1
#align has_one.ghas_one One.gOne
-/

#print Mul.gMul /-
@[simps mul]
instance Mul.gMul [Add ι] [Mul R] : GradedMonoid.GMul fun i : ι => R where mul i j := (· * ·)
#align has_mul.ghas_mul Mul.gMul
-/

#print Monoid.gMonoid /-
/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
instance Monoid.gMonoid [AddMonoid ι] [Monoid R] : GradedMonoid.GMonoid fun i : ι => R :=
  { One.gOne ι,
    Mul.gMul ι with
    one_mul := fun a => Sigma.ext (zero_add _) (hEq_of_eq (one_mul _))
    mul_one := fun a => Sigma.ext (add_zero _) (hEq_of_eq (mul_one _))
    mul_assoc := fun a b c => Sigma.ext (add_assoc _ _ _) (hEq_of_eq (mul_assoc _ _ _))
    gnpow := fun n i a => a ^ n
    gnpow_zero' := fun a => Sigma.ext (zero_nsmul _) (hEq_of_eq (Monoid.npow_zero _))
    gnpow_succ' := fun n ⟨i, a⟩ => Sigma.ext (succ_nsmul' _ _) (hEq_of_eq (Monoid.npow_succ _ _)) }
#align monoid.gmonoid Monoid.gMonoid
-/

#print CommMonoid.gCommMonoid /-
/-- If all grades are the same type and themselves form a commutative monoid, then there is a
trivial grading structure. -/
instance CommMonoid.gCommMonoid [AddCommMonoid ι] [CommMonoid R] :
    GradedMonoid.GCommMonoid fun i : ι => R :=
  { Monoid.gMonoid ι with
    mul_comm := fun a b => Sigma.ext (add_comm _ _) (hEq_of_eq (mul_comm _ _)) }
#align comm_monoid.gcomm_monoid CommMonoid.gCommMonoid
-/

#print List.dProd_monoid /-
/-- When all the indexed types are the same, the dependent product is just the regular product. -/
@[simp]
theorem List.dProd_monoid {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α → ι) (fA : α → R) :
    (l.dProd fι fA : (fun i : ι => R) _) = ((l.map fA).Prod : _) :=
  by
  induction l
  · rw [List.dProd_nil, List.map_nil, List.prod_nil]; rfl
  · rw [List.dProd_cons, List.map_cons, List.prod_cons, l_ih]; rfl
#align list.dprod_monoid List.dProd_monoid
-/

end

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type _}

#print SetLike.GradedOne /-
/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class SetLike.GradedOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S) : Prop where
  one_mem : (1 : R) ∈ A 0
#align set_like.has_graded_one SetLike.GradedOne
-/

#print SetLike.one_mem_graded /-
theorem SetLike.one_mem_graded {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : (1 : R) ∈ A 0 :=
  SetLike.GradedOne.one_mem
#align set_like.one_mem_graded SetLike.one_mem_graded
-/

#print SetLike.gOne /-
instance SetLike.gOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : GradedMonoid.GOne fun i => A i
    where one := ⟨1, SetLike.one_mem_graded _⟩
#align set_like.ghas_one SetLike.gOne
-/

#print SetLike.coe_gOne /-
@[simp]
theorem SetLike.coe_gOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => A i) _ _) = (1 : R) :=
  rfl
#align set_like.coe_ghas_one SetLike.coe_gOne
-/

#print SetLike.GradedMul /-
/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class SetLike.GradedMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) : Prop where
  hMul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → gi * gj ∈ A (i + j)
#align set_like.has_graded_mul SetLike.GradedMul
-/

#print SetLike.mul_mem_graded /-
theorem SetLike.mul_mem_graded {S : Type _} [SetLike S R] [Mul R] [Add ι] {A : ι → S}
    [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi ∈ A i) (hj : gj ∈ A j) : gi * gj ∈ A (i + j) :=
  SetLike.GradedMul.hMul_mem hi hj
#align set_like.mul_mem_graded SetLike.mul_mem_graded
-/

#print SetLike.gMul /-
instance SetLike.gMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) [SetLike.GradedMul A] :
    GradedMonoid.GMul fun i => A i
    where mul i j a b := ⟨(a * b : R), SetLike.mul_mem_graded a.Prop b.Prop⟩
#align set_like.ghas_mul SetLike.gMul
-/

#print SetLike.coe_gMul /-
@[simp]
theorem SetLike.coe_gMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.GradedMul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@GradedMonoid.GMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) :=
  rfl
#align set_like.coe_ghas_mul SetLike.coe_gMul
-/

#print SetLike.GradedMonoid /-
/-- A version of `graded_monoid.gmonoid` for internally graded objects. -/
class SetLike.GradedMonoid {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S) extends
    SetLike.GradedOne A, SetLike.GradedMul A : Prop
#align set_like.graded_monoid SetLike.GradedMonoid
-/

namespace SetLike

variable {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

#print SetLike.pow_mem_graded /-
theorem pow_mem_graded (n : ℕ) {r : R} {i : ι} (h : r ∈ A i) : r ^ n ∈ A (n • i) :=
  by
  induction n
  · rw [pow_zero, zero_nsmul]; exact one_mem_graded _
  · rw [pow_succ, succ_nsmul]; exact mul_mem_graded n_ih h
#align set_like.pow_mem_graded SetLike.pow_mem_graded
-/

#print SetLike.list_prod_map_mem_graded /-
theorem list_prod_map_mem_graded {ι'} (l : List ι') (i : ι' → ι) (r : ι' → R)
    (h : ∀ j ∈ l, r j ∈ A (i j)) : (l.map r).Prod ∈ A (l.map i).Sum :=
  by
  induction l
  · rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil]
    exact one_mem_graded _
  · rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact
      mul_mem_graded (h _ <| List.mem_cons_self _ _)
        (l_ih fun j hj => h _ <| List.mem_cons_of_mem _ hj)
#align set_like.list_prod_map_mem_graded SetLike.list_prod_map_mem_graded
-/

#print SetLike.list_prod_ofFn_mem_graded /-
theorem list_prod_ofFn_mem_graded {n} (i : Fin n → ι) (r : Fin n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFn r).Prod ∈ A (List.ofFn i).Sum :=
  by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact list_prod_map_mem_graded _ _ _ fun _ _ => h _
#align set_like.list_prod_of_fn_mem_graded SetLike.list_prod_ofFn_mem_graded
-/

end SetLike

#print SetLike.gMonoid /-
/-- Build a `gmonoid` instance for a collection of subobjects. -/
instance SetLike.gMonoid {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GMonoid fun i => A i :=
  { SetLike.gOne A,
    SetLike.gMul
      A with
    one_mul := fun ⟨i, a, h⟩ => Sigma.subtype_ext (zero_add _) (one_mul _)
    mul_one := fun ⟨i, a, h⟩ => Sigma.subtype_ext (add_zero _) (mul_one _)
    mul_assoc := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ ⟨k, c, hc⟩ =>
      Sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _)
    gnpow := fun n i a => ⟨a ^ n, SetLike.pow_mem_graded n a.Prop⟩
    gnpow_zero' := fun n => Sigma.subtype_ext (zero_nsmul _) (pow_zero _)
    gnpow_succ' := fun n a => Sigma.subtype_ext (succ_nsmul' _ _) (pow_succ' _ _) }
#align set_like.gmonoid SetLike.gMonoid
-/

#print SetLike.coe_gnpow /-
@[simp]
theorem SetLike.coe_gnpow {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : ℕ) :
    ↑(@GradedMonoid.GMonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x ^ n : R) :=
  rfl
#align set_like.coe_gnpow SetLike.coe_gnpow
-/

#print SetLike.gCommMonoid /-
/-- Build a `gcomm_monoid` instance for a collection of subobjects. -/
instance SetLike.gCommMonoid {S : Type _} [SetLike S R] [CommMonoid R] [AddCommMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GCommMonoid fun i => A i :=
  { SetLike.gMonoid A with
    mul_comm := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ => Sigma.subtype_ext (add_comm _ _) (mul_comm _ _) }
#align set_like.gcomm_monoid SetLike.gCommMonoid
-/

section Dprod

open SetLike SetLike.GradedMonoid

variable {α S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι]

#print SetLike.coe_list_dProd /-
/-- Coercing a dependent product of subtypes is the same as taking the regular product of the
coercions. -/
@[simp]
theorem SetLike.coe_list_dProd (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι)
    (fA : ∀ a, A (fι a)) (l : List α) :
    ↑(l.dProd fι fA : (fun i => ↥(A i)) _) = (List.prod (l.map fun a => fA a) : R) :=
  by
  induction l
  · rw [List.dProd_nil, coe_ghas_one, List.map_nil, List.prod_nil]
  · rw [List.dProd_cons, coe_ghas_mul, List.map_cons, List.prod_cons, l_ih]
#align set_like.coe_list_dprod SetLike.coe_list_dProd
-/

#print SetLike.list_dProd_eq /-
/-- A version of `list.coe_dprod_set_like` with `subtype.mk`. -/
theorem SetLike.list_dProd_eq (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι) (fA : ∀ a, A (fι a))
    (l : List α) :
    (l.dProd fι fA : (fun i => ↥(A i)) _) =
      ⟨List.prod (l.map fun a => fA a),
        (l.dProdIndex_eq_map_sum fι).symm ▸
          list_prod_map_mem_graded l _ _ fun i hi => (fA i).Prop⟩ :=
  Subtype.ext <| SetLike.coe_list_dProd _ _ _ _
#align set_like.list_dprod_eq SetLike.list_dProd_eq
-/

end Dprod

end Subobjects

section HomogeneousElements

variable {R S : Type _} [SetLike S R]

#print SetLike.Homogeneous /-
/-- An element `a : R` is said to be homogeneous if there is some `i : ι` such that `a ∈ A i`. -/
def SetLike.Homogeneous (A : ι → S) (a : R) : Prop :=
  ∃ i, a ∈ A i
#align set_like.is_homogeneous SetLike.Homogeneous
-/

#print SetLike.homogeneous_coe /-
@[simp]
theorem SetLike.homogeneous_coe {A : ι → S} {i} (x : A i) : SetLike.Homogeneous A (x : R) :=
  ⟨i, x.Prop⟩
#align set_like.is_homogeneous_coe SetLike.homogeneous_coe
-/

#print SetLike.homogeneous_one /-
theorem SetLike.homogeneous_one [Zero ι] [One R] (A : ι → S) [SetLike.GradedOne A] :
    SetLike.Homogeneous A (1 : R) :=
  ⟨0, SetLike.one_mem_graded _⟩
#align set_like.is_homogeneous_one SetLike.homogeneous_one
-/

#print SetLike.homogeneous_mul /-
theorem SetLike.homogeneous_mul [Add ι] [Mul R] {A : ι → S} [SetLike.GradedMul A] {a b : R} :
    SetLike.Homogeneous A a → SetLike.Homogeneous A b → SetLike.Homogeneous A (a * b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.mul_mem_graded hi hj⟩
#align set_like.is_homogeneous.mul SetLike.homogeneous_mul
-/

#print SetLike.homogeneousSubmonoid /-
/-- When `A` is a `set_like.graded_monoid A`, then the homogeneous elements forms a submonoid. -/
def SetLike.homogeneousSubmonoid [AddMonoid ι] [Monoid R] (A : ι → S) [SetLike.GradedMonoid A] :
    Submonoid R where
  carrier := {a | SetLike.Homogeneous A a}
  one_mem' := SetLike.homogeneous_one A
  hMul_mem' a b := SetLike.homogeneous_mul
#align set_like.homogeneous_submonoid SetLike.homogeneousSubmonoid
-/

end HomogeneousElements

