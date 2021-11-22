import Mathbin.Algebra.Group.InjSurj 
import Mathbin.Algebra.GroupPower.Basic 
import Mathbin.Data.SetLike.Basic 
import Mathbin.Data.Sigma.Basic 
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Additively-graded multiplicative structures

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
* `graded_monoid.grade_zero.has_scalar (A 0)`
* `graded_monoid.grade_zero.mul_action (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `direct_sum.ring` and the rest
of that file.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_one A` (which provides the obvious `graded_monoid.ghas_one A` instance)
* `set_like.has_graded_mul A` (which provides the obvious `graded_monoid.ghas_mul A` instance)
* `set_like.graded_monoid A` (which provides the obvious `graded_monoid.gmonoid A` and
  `graded_monoid.gcomm_monoid A` instances)

Strictly this last class is unecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `graded_ring` or similar, as all the
information it would contain is already supplied by `graded_monoid` when `A` is a collection
of additively-closed set_like objects such as `submodules`. These constructions are explored in
`algebra.direct_sum.internal`.

## tags

graded monoid
-/


variable{ι : Type _}

/-- A type alias of sigma types for graded monoids. -/
def GradedMonoid (A : ι → Type _) :=
  Sigma A

namespace GradedMonoid

instance  {A : ι → Type _} [Inhabited ι] [Inhabited (A (default ι))] : Inhabited (GradedMonoid A) :=
  Sigma.inhabited

/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type _} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk

/-! ### Typeclasses -/


section Defs

variable(A : ι → Type _)

/-- A graded version of `has_one`, which must be of grade 0. -/
class ghas_one[HasZero ι] where 
  one : A 0

/-- `ghas_one` implies `has_one (graded_monoid A)` -/
instance ghas_one.to_has_one [HasZero ι] [ghas_one A] : HasOne (GradedMonoid A) :=
  ⟨⟨_, ghas_one.one⟩⟩

/-- A graded version of `has_mul`. Multiplication combines grades additively, like
`add_monoid_algebra`. -/
class ghas_mul[Add ι] where 
  mul {i j} : A i → A j → A (i+j)

/-- `ghas_mul` implies `has_mul (graded_monoid A)`. -/
instance ghas_mul.to_has_mul [Add ι] [ghas_mul A] : Mul (GradedMonoid A) :=
  ⟨fun x y : GradedMonoid A => ⟨_, ghas_mul.mul x.snd y.snd⟩⟩

theorem mk_mul_mk [Add ι] [ghas_mul A] {i j} (a : A i) (b : A j) : (mk i a*mk j b) = mk (i+j) (ghas_mul.mul a b) :=
  rfl

namespace Gmonoid

variable{A}[AddMonoidₓ ι][ghas_mul A][ghas_one A]

/-- A default implementation of power on a graded monoid, like `npow_rec`.
`gmonoid.gnpow` should be used instead. -/
def gnpow_rec : ∀ n : ℕ {i}, A i → A (n • i)
| 0, i, a => cast (congr_argₓ A (zero_nsmul i).symm) ghas_one.one
| n+1, i, a => cast (congr_argₓ A (succ_nsmul i n).symm) (ghas_mul.mul a$ gnpow_rec _ a)

@[simp]
theorem gnpow_rec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpow_rec 0 a.snd) = 1 :=
  Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm

/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_zero'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
unsafe def apply_gnpow_rec_zero_tac : tactic Unit :=
  sorry

@[simp]
theorem gnpow_rec_succ (n : ℕ) (a : GradedMonoid A) :
  (GradedMonoid.mk _$ gnpow_rec n.succ a.snd) = a*⟨_, gnpow_rec n a.snd⟩ :=
  Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_succ'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
unsafe def apply_gnpow_rec_succ_tac : tactic Unit :=
  sorry

end Gmonoid

/-- A graded version of `monoid`.

Like `monoid.npow`, this has an optional `gmonoid.gnpow` field to allow definitional control of
natural powers of a graded monoid. -/
class gmonoid[AddMonoidₓ ι] extends ghas_mul A, ghas_one A where 
  one_mul (a : GradedMonoid A) : (1*a) = a 
  mul_one (a : GradedMonoid A) : (a*1) = a 
  mul_assoc (a b c : GradedMonoid A) : ((a*b)*c) = a*b*c 
  gnpow : ∀ n : ℕ {i}, A i → A (n • i) := gmonoid.gnpow_rec 
  gnpow_zero' : ∀ a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1 :=  by 
  runTac 
    gmonoid.apply_gnpow_rec_zero_tac 
  gnpow_succ' : ∀ n : ℕ a : GradedMonoid A, (GradedMonoid.mk _$ gnpow n.succ a.snd) = a*⟨_, gnpow n a.snd⟩ :=  by 
  runTac 
    gmonoid.apply_gnpow_rec_succ_tac

/-- `gmonoid` implies a `monoid (graded_monoid A)`. -/
instance gmonoid.to_monoid [AddMonoidₓ ι] [gmonoid A] : Monoidₓ (GradedMonoid A) :=
  { one := 1, mul := ·*·, npow := fun n a => GradedMonoid.mk _ (gmonoid.gnpow n a.snd),
    npow_zero' := fun a => gmonoid.gnpow_zero' a, npow_succ' := fun n a => gmonoid.gnpow_succ' n a,
    one_mul := gmonoid.one_mul, mul_one := gmonoid.mul_one, mul_assoc := gmonoid.mul_assoc }

theorem mk_pow [AddMonoidₓ ι] [gmonoid A] {i} (a : A i) (n : ℕ) : mk i a ^ n = mk (n • i) (gmonoid.gnpow _ a) :=
  by 
    induction' n with n
    ·
      rw [pow_zeroₓ]
      exact (gmonoid.gnpow_zero' ⟨_, a⟩).symm
    ·
      rw [pow_succₓ, n_ih, mk_mul_mk]
      exact (gmonoid.gnpow_succ' n ⟨_, a⟩).symm

/-- A graded version of `comm_monoid`. -/
class gcomm_monoid[AddCommMonoidₓ ι] extends gmonoid A where 
  mul_comm (a : GradedMonoid A) (b : GradedMonoid A) : (a*b) = b*a

/-- `gcomm_monoid` implies a `comm_monoid (graded_monoid A)`, although this is only used as an
instance locally to define notation in `gmonoid` and similar typeclasses. -/
instance gcomm_monoid.to_comm_monoid [AddCommMonoidₓ ι] [gcomm_monoid A] : CommMonoidₓ (GradedMonoid A) :=
  { gmonoid.to_monoid A with mul_comm := gcomm_monoid.mul_comm }

end Defs

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

variable(A : ι → Type _)

section One

variable[HasZero ι][ghas_one A]

/-- `1 : A 0` is the value provided in `ghas_one.one`. -/
@[nolint unused_arguments]
instance grade_zero.has_one : HasOne (A 0) :=
  ⟨ghas_one.one⟩

end One

section Mul

variable[AddMonoidₓ ι][ghas_mul A]

/-- `(•) : A 0 → A i → A i` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance grade_zero.has_scalar (i : ι) : HasScalar (A 0) (A i) :=
  { smul := fun x y => (zero_addₓ i).rec (ghas_mul.mul x y) }

/-- `(*) : A 0 → A 0 → A 0` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance grade_zero.has_mul : Mul (A 0) :=
  { mul := · • · }

variable{A}

@[simp]
theorem mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a*mk _ b :=
  Sigma.ext (zero_addₓ _).symm$ eq_rec_heqₓ _ _

@[simp]
theorem grade_zero.smul_eq_mul (a b : A 0) : a • b = a*b :=
  rfl

end Mul

section Monoidₓ

variable[AddMonoidₓ ι][gmonoid A]

/-- The `monoid` structure derived from `gmonoid A`. -/
instance grade_zero.monoid : Monoidₓ (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul

end Monoidₓ

section Monoidₓ

variable[AddCommMonoidₓ ι][gcomm_monoid A]

/-- The `comm_monoid` structure derived from `gcomm_monoid A`. -/
instance grade_zero.comm_monoid : CommMonoidₓ (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul

end Monoidₓ

section MulAction

variable[AddMonoidₓ ι][gmonoid A]

/-- `graded_monoid.mk 0` is a `monoid_hom`, using the `graded_monoid.grade_zero.monoid` structure.
-/
def mk_zero_monoid_hom : A 0 →* GradedMonoid A :=
  { toFun := mk 0, map_one' := rfl, map_mul' := mk_zero_smul }

/-- Each grade `A i` derives a `A 0`-action structure from `gmonoid A`. -/
instance grade_zero.mul_action {i} : MulAction (A 0) (A i) :=
  by 
    letI this := MulAction.compHom (GradedMonoid A) (mk_zero_monoid_hom A)
    exact Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul

end MulAction

end GradeZero

end GradedMonoid

/-! ### Concrete instances -/


section 

variable(ι){R : Type _}

@[simps one]
instance HasOne.ghasOne [HasZero ι] [HasOne R] : GradedMonoid.GhasOne fun i : ι => R :=
  { one := 1 }

@[simps mul]
instance Mul.ghasMul [Add ι] [Mul R] : GradedMonoid.GhasMul fun i : ι => R :=
  { mul := fun i j => ·*· }

/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
instance Monoidₓ.gmonoid [AddMonoidₓ ι] [Monoidₓ R] : GradedMonoid.Gmonoid fun i : ι => R :=
  { HasOne.ghasOne ι, Mul.ghasMul ι with one_mul := fun a => Sigma.ext (zero_addₓ _) (heq_of_eq (one_mulₓ _)),
    mul_one := fun a => Sigma.ext (add_zeroₓ _) (heq_of_eq (mul_oneₓ _)),
    mul_assoc := fun a b c => Sigma.ext (add_assocₓ _ _ _) (heq_of_eq (mul_assocₓ _ _ _)), gnpow := fun n i a => a ^ n,
    gnpow_zero' := fun a => Sigma.ext (zero_nsmul _) (heq_of_eq (Monoidₓ.npow_zero' _)),
    gnpow_succ' := fun n ⟨i, a⟩ => Sigma.ext (succ_nsmul _ _) (heq_of_eq (Monoidₓ.npow_succ' _ _)) }

/-- If all grades are the same type and themselves form a commutative monoid, then there is a
trivial grading structure. -/
instance CommMonoidₓ.gcommMonoid [AddCommMonoidₓ ι] [CommMonoidₓ R] : GradedMonoid.GcommMonoid fun i : ι => R :=
  { Monoidₓ.gmonoid ι with mul_comm := fun a b => Sigma.ext (add_commₓ _ _) (heq_of_eq (mul_commₓ _ _)) }

end 

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable{R : Type _}

/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class SetLike.HasGradedOne{S : Type _}[SetLike S R][HasOne R][HasZero ι](A : ι → S) : Prop where 
  one_mem : (1 : R) ∈ A 0

instance SetLike.ghasOne {S : Type _} [SetLike S R] [HasOne R] [HasZero ι] (A : ι → S) [SetLike.HasGradedOne A] :
  GradedMonoid.GhasOne fun i => A i :=
  { one := ⟨1, SetLike.HasGradedOne.one_mem⟩ }

@[simp]
theorem SetLike.coe_ghas_one {S : Type _} [SetLike S R] [HasOne R] [HasZero ι] (A : ι → S) [SetLike.HasGradedOne A] :
  «expr↑ » (@GradedMonoid.GhasOne.one _ (fun i => A i) _ _) = (1 : R) :=
  rfl

/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class SetLike.HasGradedMul{S : Type _}[SetLike S R][Mul R][Add ι](A : ι → S) : Prop where 
  mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → (gi*gj) ∈ A (i+j)

instance SetLike.ghasMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) [SetLike.HasGradedMul A] :
  GradedMonoid.GhasMul fun i => A i :=
  { mul := fun i j a b => ⟨(a*b : R), SetLike.HasGradedMul.mul_mem a.prop b.prop⟩ }

@[simp]
theorem SetLike.coe_ghas_mul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) [SetLike.HasGradedMul A] {i j : ι}
  (x : A i) (y : A j) : «expr↑ » (@GradedMonoid.GhasMul.mul _ (fun i => A i) _ _ _ _ x y) = (x*y : R) :=
  rfl

/-- A version of `graded_monoid.gmonoid` for internally graded objects. -/
class SetLike.GradedMonoid{S : Type _}[SetLike S R][Monoidₓ R][AddMonoidₓ ι](A : ι → S) extends SetLike.HasGradedOne A,
  SetLike.HasGradedMul A : Prop

/-- Build a `gmonoid` instance for a collection of subobjects. -/
instance SetLike.gmonoid {S : Type _} [SetLike S R] [Monoidₓ R] [AddMonoidₓ ι] (A : ι → S) [SetLike.GradedMonoid A] :
  GradedMonoid.Gmonoid fun i => A i :=
  { SetLike.ghasOne A, SetLike.ghasMul A with one_mul := fun ⟨i, a, h⟩ => Sigma.subtype_ext (zero_addₓ _) (one_mulₓ _),
    mul_one := fun ⟨i, a, h⟩ => Sigma.subtype_ext (add_zeroₓ _) (mul_oneₓ _),
    mul_assoc := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ ⟨k, c, hc⟩ => Sigma.subtype_ext (add_assocₓ _ _ _) (mul_assocₓ _ _ _),
    gnpow :=
      fun n i a =>
        ⟨a ^ n,
          by 
            induction n
            ·
              rw [pow_zeroₓ, zero_nsmul]
              exact SetLike.HasGradedOne.one_mem
            ·
              rw [pow_succ'ₓ, succ_nsmul']
              exact SetLike.HasGradedMul.mul_mem n_ih a.prop⟩,
    gnpow_zero' := fun n => Sigma.subtype_ext (zero_nsmul _) (pow_zeroₓ _),
    gnpow_succ' := fun n a => Sigma.subtype_ext (succ_nsmul _ _) (pow_succₓ _ _) }

@[simp]
theorem SetLike.coe_gpow {S : Type _} [SetLike S R] [Monoidₓ R] [AddMonoidₓ ι] (A : ι → S) [SetLike.GradedMonoid A]
  {i : ι} (x : A i) (n : ℕ) : «expr↑ » (@GradedMonoid.Gmonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x ^ n : R) :=
  rfl

/-- Build a `gcomm_monoid` instance for a collection of subobjects. -/
instance SetLike.gcommMonoid {S : Type _} [SetLike S R] [CommMonoidₓ R] [AddCommMonoidₓ ι] (A : ι → S)
  [SetLike.GradedMonoid A] : GradedMonoid.GcommMonoid fun i => A i :=
  { SetLike.gmonoid A with mul_comm := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ => Sigma.subtype_ext (add_commₓ _ _) (mul_commₓ _ _) }

end Subobjects

