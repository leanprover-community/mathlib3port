/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathbin.RingTheory.Localization.AtPrime
import Mathbin.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous Localization

## Notation
- `ฮน` is a commutative monoid;
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `๐ : ฮน โ submodule R A` is the grading of `A`;
- `x : ideal A` is a prime ideal.

## Main definitions and results

This file constructs the subring of `Aโ` where the numerator and denominator have the same grading,
i.e. `{a/b โ Aโ | โ (i : ฮน), a โ ๐แตข โง b โ ๐แตข}`.

* `homogeneous_localization.num_denom_same_deg`: a structure with a numerator and denominator field
  where they are required to have the same grading.

However `num_denom_same_deg ๐ x` cannot have a ring structure for many reasons, for example if `c`
is a `num_denom_same_deg`, then generally, `c + (-c)` is not necessarily `0` for degree reasons ---
`0` is considered to have grade zero (see `deg_zero`) but `c + (-c)` has the same degree as `c`. To
circumvent this, we quotient `num_denom_same_deg ๐ x` by the kernel of `c โฆ c.num / c.denom`.

* `homogeneous_localization.num_denom_same_deg.embedding` : for `x : prime ideal of A` and any
  `c : num_denom_same_deg ๐ x`, or equivalent a numerator and a denominator of the same degree,
  we get an element `c.num / c.denom` of `Aโ`.
* `homogeneous_localization`: `num_denom_same_deg ๐ x` quotiented by kernel of `embedding ๐ x`.
* `homogeneous_localization.val`: if `f : homogeneous_localization ๐ x`, then `f.val` is an element
  of `Aโ`. In another word, one can view `homogeneous_localization ๐ x` as a subring of `Aโ`
  through `homogeneous_localization.val`.
* `homogeneous_localization.num`: if `f : homogeneous_localization ๐ x`, then `f.num : A` is the
  numerator of `f`.
* `homogeneous_localization.num`: if `f : homogeneous_localization ๐ x`, then `f.denom : A` is the
  denominator of `f`.
* `homogeneous_localization.deg`: if `f : homogeneous_localization ๐ x`, then `f.deg : ฮน` is the
  degree of `f` such that `f.num โ ๐ f.deg` and `f.denom โ ๐ f.deg`
  (see `homogeneous_localization.num_mem` and `homogeneous_localization.denom_mem`).
* `homogeneous_localization.num_mem`: if `f : homogeneous_localization ๐ x`, then `f.num_mem` is a
  proof that `f.num โ f.deg`.
* `homogeneous_localization.denom_mem`: if `f : homogeneous_localization ๐ x`, then `f.denom_mem`
  is a proof that `f.denom โ f.deg`.
* `homogeneous_localization.eq_num_div_denom`: if `f : homogeneous_localization ๐ x`, then
  `f.val : Aโ` is equal to `f.num / f.denom`.

* `homogeneous_localization.local_ring`: `homogeneous_localization ๐ x` is a local ring.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


noncomputable section

open DirectSum BigOperators Pointwise

open DirectSum SetLike

variable {ฮน R A : Type _}

variable [AddCommMonoidโ ฮน] [DecidableEq ฮน]

variable [CommRingโ R] [CommRingโ A] [Algebra R A]

variable (๐ : ฮน โ Submodule R A) [GradedAlgebra ๐]

variable (x : Ideal A) [Ideal.IsPrime x]

-- mathport name: ยซexprat ยป
local notation "at " x => Localization.AtPrime x

namespace HomogeneousLocalization

section

/-- Let `x` be a prime ideal, then `num_denom_same_deg ๐ x` is a structure with a numerator and a
denominator with same grading such that the denominator is not contained in `x`.
-/
@[nolint has_inhabited_instance]
structure NumDenomSameDeg where
  deg : ฮน
  (num denom : ๐ deg)
  denom_not_mem : (denom : A) โ x

end

namespace NumDenomSameDeg

open SetLike.GradedMonoid Submodule

variable {๐}

@[ext]
theorem ext {c1 c2 : NumDenomSameDeg ๐ x} (hdeg : c1.deg = c2.deg) (hnum : (c1.num : A) = c2.num)
    (hdenom : (c1.denom : A) = c2.denom) : c1 = c2 := by
  rcases c1 with โจi1, โจn1, hn1โฉ, โจd1, hd1โฉ, h1โฉ
  rcases c2 with โจi2, โจn2, hn2โฉ, โจd2, hd2โฉ, h2โฉ
  dsimp' only [โ Subtype.coe_mk]  at *
  simp only
  exact
    โจhdeg, by
      subst hdeg <;> subst hnum, by
      subst hdeg <;> subst hdenomโฉ

instance :
    One
      (NumDenomSameDeg ๐
        x) where one :=
    { deg := 0, num := โจ1, one_memโฉ, denom := โจ1, one_memโฉ,
      denom_not_mem := fun r => (inferInstance : x.IsPrime).ne_top <| x.eq_top_iff_one.mpr r }

@[simp]
theorem deg_one : (1 : NumDenomSameDeg ๐ x).deg = 0 :=
  rfl

@[simp]
theorem num_one : ((1 : NumDenomSameDeg ๐ x).num : A) = 1 :=
  rfl

@[simp]
theorem denom_one : ((1 : NumDenomSameDeg ๐ x).denom : A) = 1 :=
  rfl

instance :
    Zero
      (NumDenomSameDeg ๐
        x) where zero := โจ0, 0, โจ1, one_memโฉ, fun r => (inferInstance : x.IsPrime).ne_top <| x.eq_top_iff_one.mpr rโฉ

@[simp]
theorem deg_zero : (0 : NumDenomSameDeg ๐ x).deg = 0 :=
  rfl

@[simp]
theorem num_zero : (0 : NumDenomSameDeg ๐ x).num = 0 :=
  rfl

@[simp]
theorem denom_zero : ((0 : NumDenomSameDeg ๐ x).denom : A) = 1 :=
  rfl

instance :
    Mul
      (NumDenomSameDeg ๐
        x) where mul := fun p q =>
    { deg := p.deg + q.deg, num := โจp.num * q.num, mul_mem p.num.Prop q.num.Propโฉ,
      denom := โจp.denom * q.denom, mul_mem p.denom.Prop q.denom.Propโฉ,
      denom_not_mem := fun r => Or.elim ((inferInstance : x.IsPrime).mem_or_mem r) p.denom_not_mem q.denom_not_mem }

@[simp]
theorem deg_mul (c1 c2 : NumDenomSameDeg ๐ x) : (c1 * c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
theorem num_mul (c1 c2 : NumDenomSameDeg ๐ x) : ((c1 * c2).num : A) = c1.num * c2.num :=
  rfl

@[simp]
theorem denom_mul (c1 c2 : NumDenomSameDeg ๐ x) : ((c1 * c2).denom : A) = c1.denom * c2.denom :=
  rfl

instance :
    Add
      (NumDenomSameDeg ๐
        x) where add := fun c1 c2 =>
    { deg := c1.deg + c2.deg,
      num :=
        โจc1.denom * c2.num + c2.denom * c1.num,
          add_mem (mul_mem c1.denom.2 c2.num.2) (add_commโ c2.deg c1.deg โธ mul_mem c2.denom.2 c1.num.2)โฉ,
      denom := โจc1.denom * c2.denom, mul_mem c1.denom.2 c2.denom.2โฉ,
      denom_not_mem := fun r => Or.elim ((inferInstance : x.IsPrime).mem_or_mem r) c1.denom_not_mem c2.denom_not_mem }

@[simp]
theorem deg_add (c1 c2 : NumDenomSameDeg ๐ x) : (c1 + c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
theorem num_add (c1 c2 : NumDenomSameDeg ๐ x) : ((c1 + c2).num : A) = c1.denom * c2.num + c2.denom * c1.num :=
  rfl

@[simp]
theorem denom_add (c1 c2 : NumDenomSameDeg ๐ x) : ((c1 + c2).denom : A) = c1.denom * c2.denom :=
  rfl

instance : Neg (NumDenomSameDeg ๐ x) where neg := fun c => โจc.deg, โจ-c.num, neg_mem c.num.2โฉ, c.denom, c.denom_not_memโฉ

@[simp]
theorem deg_neg (c : NumDenomSameDeg ๐ x) : (-c).deg = c.deg :=
  rfl

@[simp]
theorem num_neg (c : NumDenomSameDeg ๐ x) : ((-c).num : A) = -c.num :=
  rfl

@[simp]
theorem denom_neg (c : NumDenomSameDeg ๐ x) : ((-c).denom : A) = c.denom :=
  rfl

instance : CommMonoidโ (NumDenomSameDeg ๐ x) where
  one := 1
  mul := (ยท * ยท)
  mul_assoc := fun c1 c2 c3 => ext _ (add_assocโ _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul := fun c => ext _ (zero_addโ _) (one_mulโ _) (one_mulโ _)
  mul_one := fun c => ext _ (add_zeroโ _) (mul_oneโ _) (mul_oneโ _)
  mul_comm := fun c1 c2 => ext _ (add_commโ _ _) (mul_comm _ _) (mul_comm _ _)

instance :
    Pow (NumDenomSameDeg ๐ x)
      โ where pow := fun c n =>
    โจn โข c.deg, โจc.num ^ n, pow_mem n c.num.2โฉ, โจc.denom ^ n, pow_mem n c.denom.2โฉ, by
      cases n
      ยท simp only [โ pow_zeroโ]
        exact fun r => (inferInstance : x.is_prime).ne_top <| (Ideal.eq_top_iff_one _).mpr r
        
      ยท exact fun r =>
          c.denom_not_mem <| ((inferInstance : x.is_prime).pow_mem_iff_mem n.succ (Nat.zero_lt_succโ _)).mp r
        โฉ

@[simp]
theorem deg_pow (c : NumDenomSameDeg ๐ x) (n : โ) : (c ^ n).deg = n โข c.deg :=
  rfl

@[simp]
theorem num_pow (c : NumDenomSameDeg ๐ x) (n : โ) : ((c ^ n).num : A) = c.num ^ n :=
  rfl

@[simp]
theorem denom_pow (c : NumDenomSameDeg ๐ x) (n : โ) : ((c ^ n).denom : A) = c.denom ^ n :=
  rfl

section HasSmul

variable {ฮฑ : Type _} [HasSmul ฮฑ R] [HasSmul ฮฑ A] [IsScalarTower ฮฑ R A]

instance : HasSmul ฮฑ (NumDenomSameDeg ๐ x) where smul := fun m c => โจc.deg, m โข c.num, c.denom, c.denom_not_memโฉ

@[simp]
theorem deg_smul (c : NumDenomSameDeg ๐ x) (m : ฮฑ) : (m โข c).deg = c.deg :=
  rfl

@[simp]
theorem num_smul (c : NumDenomSameDeg ๐ x) (m : ฮฑ) : ((m โข c).num : A) = m โข c.num :=
  rfl

@[simp]
theorem denom_smul (c : NumDenomSameDeg ๐ x) (m : ฮฑ) : ((m โข c).denom : A) = c.denom :=
  rfl

end HasSmul

variable (๐)

/-- For `x : prime ideal of A` and any `p : num_denom_same_deg ๐ x`, or equivalent a numerator and a
denominator of the same degree, we get an element `p.num / p.denom` of `Aโ`.
-/
def embedding (p : NumDenomSameDeg ๐ x) : at x :=
  Localization.mk p.num โจp.denom, p.denom_not_memโฉ

end NumDenomSameDeg

end HomogeneousLocalization

/-- For `x : prime ideal of A`, `homogeneous_localization ๐ x` is `num_denom_same_deg ๐ x` modulo the
kernel of `embedding ๐ x`. This is essentially the subring of `Aโ` where the numerator and
denominator share the same grading.
-/
@[nolint has_inhabited_instance]
def HomogeneousLocalization : Type _ :=
  Quotientโ (Setoidโ.ker <| HomogeneousLocalization.NumDenomSameDeg.embedding ๐ x)

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenomSameDeg

variable {๐} {x}

/-- View an element of `homogeneous_localization ๐ x` as an element of `Aโ` by forgetting that the
numerator and denominator are of the same grading.
-/
def val (y : HomogeneousLocalization ๐ x) : at x :=
  (Quotientโ.liftOn' y (NumDenomSameDeg.embedding ๐ x)) fun _ _ => id

@[simp]
theorem val_mk' (i : NumDenomSameDeg ๐ x) : val (Quotientโ.mk' i) = Localization.mk i.num โจi.denom, i.denom_not_memโฉ :=
  rfl

variable (x)

theorem val_injective : Function.Injective (@HomogeneousLocalization.val _ _ _ _ _ _ _ _ ๐ _ x _) := fun a b =>
  (Quotientโ.recOnSubsingletonโ' a b) fun a b h => Quotientโ.sound' h

instance hasPow :
    Pow (HomogeneousLocalization ๐ x)
      โ where pow := fun z n =>
    (Quotientโ.map' (ยท ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
        change Localization.mk _ _ = Localization.mk _ _
        simp only [โ num_pow, โ denom_pow]
        convert congr_arg (fun z => z ^ n) h <;> erw [Localization.mk_pow] <;> rfl :
        HomogeneousLocalization ๐ x โ HomogeneousLocalization ๐ x)
      z

section HasSmul

variable {ฮฑ : Type _} [HasSmul ฮฑ R] [HasSmul ฮฑ A] [IsScalarTower ฮฑ R A]

variable [IsScalarTower ฮฑ A A]

instance :
    HasSmul ฮฑ
      (HomogeneousLocalization ๐
        x) where smul := fun m =>
    Quotientโ.map' ((ยท โข ยท) m) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [โ num_smul, โ denom_smul]
      convert congr_arg (fun z : at x => m โข z) h <;> rw [Localization.smul_mk] <;> rfl

@[simp]
theorem smul_val (y : HomogeneousLocalization ๐ x) (n : ฮฑ) : (n โข y).val = n โข y.val := by
  induction y using Quotientโ.induction_on
  unfold HomogeneousLocalization.val HasSmul.smul
  simp only [โ Quotientโ.lift_onโ'_mk, โ Quotientโ.lift_on'_mk]
  change Localization.mk _ _ = n โข Localization.mk _ _
  dsimp' only
  rw [Localization.smul_mk]
  congr 1

end HasSmul

instance :
    Neg
      (HomogeneousLocalization ๐
        x) where neg :=
    Quotientโ.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [โ num_neg, โ denom_neg, Localization.neg_mk]
      exact congr_arg (fun c => -c) h

instance :
    Add
      (HomogeneousLocalization ๐
        x) where add :=
    Quotientโ.mapโ' (ยท + ยท)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) =>
      by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [โ num_add, โ denom_add, Localization.add_mk]
      convert congr_arg2โ (ยท + ยท) h h' <;> erw [Localization.add_mk] <;> rfl

instance : Sub (HomogeneousLocalization ๐ x) where sub := fun z1 z2 => z1 + -z2

instance :
    Mul
      (HomogeneousLocalization ๐
        x) where mul :=
    Quotientโ.mapโ' (ยท * ยท)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) =>
      by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [โ num_mul, โ denom_mul]
      convert congr_arg2โ (ยท * ยท) h h' <;> erw [Localization.mk_mul] <;> rfl

instance : One (HomogeneousLocalization ๐ x) where one := Quotientโ.mk' 1

instance : Zero (HomogeneousLocalization ๐ x) where zero := Quotientโ.mk' 0

theorem zero_eq : (0 : HomogeneousLocalization ๐ x) = Quotientโ.mk' 0 :=
  rfl

theorem one_eq : (1 : HomogeneousLocalization ๐ x) = Quotientโ.mk' 1 :=
  rfl

variable {x}

theorem zero_val : (0 : HomogeneousLocalization ๐ x).val = 0 :=
  Localization.mk_zero _

theorem one_val : (1 : HomogeneousLocalization ๐ x).val = 1 :=
  Localization.mk_one

@[simp]
theorem add_val (y1 y2 : HomogeneousLocalization ๐ x) : (y1 + y2).val = y1.val + y2.val := by
  induction y1 using Quotientโ.induction_on
  induction y2 using Quotientโ.induction_on
  unfold HomogeneousLocalization.val Add.add
  simp only [โ Quotientโ.lift_onโ'_mk, โ Quotientโ.lift_on'_mk]
  change Localization.mk _ _ = Localization.mk _ _ + Localization.mk _ _
  dsimp' only
  rw [Localization.add_mk]
  rfl

@[simp]
theorem mul_val (y1 y2 : HomogeneousLocalization ๐ x) : (y1 * y2).val = y1.val * y2.val := by
  induction y1 using Quotientโ.induction_on
  induction y2 using Quotientโ.induction_on
  unfold HomogeneousLocalization.val Mul.mul
  simp only [โ Quotientโ.lift_onโ'_mk, โ Quotientโ.lift_on'_mk]
  change Localization.mk _ _ = Localization.mk _ _ * Localization.mk _ _
  dsimp' only
  rw [Localization.mk_mul]
  rfl

@[simp]
theorem neg_val (y : HomogeneousLocalization ๐ x) : (-y).val = -y.val := by
  induction y using Quotientโ.induction_on
  unfold HomogeneousLocalization.val Neg.neg
  simp only [โ Quotientโ.lift_onโ'_mk, โ Quotientโ.lift_on'_mk]
  change Localization.mk _ _ = -Localization.mk _ _
  dsimp' only
  rw [Localization.neg_mk]
  rfl

@[simp]
theorem sub_val (y1 y2 : HomogeneousLocalization ๐ x) : (y1 - y2).val = y1.val - y2.val := by
  rw [show y1 - y2 = y1 + -y2 from rfl, add_val, neg_val] <;> rfl

@[simp]
theorem pow_val (y : HomogeneousLocalization ๐ x) (n : โ) : (y ^ n).val = y.val ^ n := by
  induction y using Quotientโ.induction_on
  unfold HomogeneousLocalization.val Pow.pow
  simp only [โ Quotientโ.lift_onโ'_mk, โ Quotientโ.lift_on'_mk]
  change Localization.mk _ _ = Localization.mk _ _ ^ n
  rw [Localization.mk_pow]
  dsimp' only
  congr 1

instance : HasNatCast (HomogeneousLocalization ๐ x) :=
  โจNat.unaryCastโฉ

instance : HasIntCast (HomogeneousLocalization ๐ x) :=
  โจInt.castDefโฉ

@[simp]
theorem nat_cast_val (n : โ) : (n : HomogeneousLocalization ๐ x).val = n :=
  show val (Nat.unaryCast n) = _ by
    induction n <;> simp [โ Nat.unaryCast, โ zero_val, โ one_val, *]

@[simp]
theorem int_cast_val (n : โค) : (n : HomogeneousLocalization ๐ x).val = n :=
  show val (Int.castDef n) = _ by
    cases n <;> simp [โ Int.castDef, โ zero_val, โ one_val, *]

instance : CommRingโ (HomogeneousLocalization ๐ x) :=
  (HomogeneousLocalization.val_injective x).CommRing _ zero_val one_val add_val mul_val neg_val sub_val
    (fun z n => smul_val x z n) (fun z n => smul_val x z n) pow_val nat_cast_val int_cast_val

end HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenomSameDeg

variable {๐} {x}

/-- numerator of an element in `homogeneous_localization x`-/
def num (f : HomogeneousLocalization ๐ x) : A :=
  (Quotientโ.out' f).num

/-- denominator of an element in `homogeneous_localization x`-/
def denom (f : HomogeneousLocalization ๐ x) : A :=
  (Quotientโ.out' f).denom

/-- For an element in `homogeneous_localization x`, degree is the natural number `i` such that
  `๐ i` contains both numerator and denominator. -/
def deg (f : HomogeneousLocalization ๐ x) : ฮน :=
  (Quotientโ.out' f).deg

theorem denom_not_mem (f : HomogeneousLocalization ๐ x) : f.denom โ x :=
  (Quotientโ.out' f).denom_not_mem

theorem num_mem (f : HomogeneousLocalization ๐ x) : f.num โ ๐ f.deg :=
  (Quotientโ.out' f).num.2

theorem denom_mem (f : HomogeneousLocalization ๐ x) : f.denom โ ๐ f.deg :=
  (Quotientโ.out' f).denom.2

theorem eq_num_div_denom (f : HomogeneousLocalization ๐ x) : f.val = Localization.mk f.num โจf.denom, f.denom_not_memโฉ :=
  by
  have := Quotientโ.out_eq' f
  apply_fun HomogeneousLocalization.val  at this
  rw [โ this]
  unfold HomogeneousLocalization.val
  simp only [โ Quotientโ.lift_on'_mk']
  rfl

theorem ext_iff_val (f g : HomogeneousLocalization ๐ x) : f = g โ f.val = g.val :=
  { mp := fun h => h โธ rfl,
    mpr := fun h => by
      induction f using Quotientโ.induction_on
      induction g using Quotientโ.induction_on
      rw [Quotientโ.eq]
      unfold HomogeneousLocalization.val  at h
      simpa only [โ Quotientโ.lift_on'_mk] using h }

theorem is_unit_iff_is_unit_val (f : HomogeneousLocalization ๐ x) : IsUnit f.val โ IsUnit f :=
  โจfun h1 => by
    rcases h1 with โจโจa, b, eq0, eq1โฉ, eq2 : a = f.valโฉ
    rw [eq2] at eq0 eq1
    clear a eq2
    induction' b using Localization.induction_on with data
    rcases data with โจa, โจb, hbโฉโฉ
    dsimp' only  at eq0 eq1
    have b_f_denom_not_mem : b * f.denom โ x.prime_compl := fun r =>
      Or.elim (Ideal.IsPrime.mem_or_mem inferInstance r) (fun r2 => hb r2) fun r2 => f.denom_not_mem r2
    rw [f.eq_num_div_denom, Localization.mk_mul,
      show (โจb, hbโฉ : x.prime_compl) * โจf.denom, _โฉ = โจb * f.denom, _โฉ from rfl,
      show (1 : at x) = Localization.mk 1 1 by
        erw [Localization.mk_self 1],
      Localization.mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with โจโจc, hcโฉ, eq1โฉ
    simp only [Subtype.val_eq_coe] at eq1
    change a * f.num * 1 * c = _ at eq1
    simp only [โ one_mulโ, โ mul_oneโ] at eq1
    have mem1 : a * f.num * c โ x.prime_compl :=
      eq1.symm โธ fun r =>
        Or.elim (Ideal.IsPrime.mem_or_mem inferInstance r)
          (by
            tauto)
          (by
            tauto)
    have mem2 : f.num โ x := by
      contrapose! mem1
      erw [not_not]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ mem1)
    refine' โจโจf, Quotientโ.mk' โจf.deg, โจf.denom, f.denom_memโฉ, โจf.num, f.num_memโฉ, mem2โฉ, _, _โฉ, rflโฉ <;>
      simp only [โ ext_iff_val, โ mul_val, โ val_mk', Subtype.val_eq_coe, โ f.eq_num_div_denom, โ Localization.mk_mul, โ
          one_val] <;>
        convert Localization.mk_self _ <;> simpa only [โ mul_comm] ,
    fun โจโจ_, b, eq1, eq2โฉ, rflโฉ => by
    simp only [โ ext_iff_val, โ mul_val, โ one_val] at eq1 eq2
    exact โจโจf.val, b.val, eq1, eq2โฉ, rflโฉโฉ

instance : Nontrivial (HomogeneousLocalization ๐ x) :=
  โจโจ0, 1, fun r => by
      simpa [โ ext_iff_val, โ zero_val, โ one_val, โ zero_ne_one] using rโฉโฉ

instance : LocalRing (HomogeneousLocalization ๐ x) :=
  LocalRing.of_is_unit_or_is_unit_one_sub_self fun a => by
    simp only [is_unit_iff_is_unit_val, โ sub_val, โ one_val]
    induction a using Quotientโ.induction_on'
    simp only [โ HomogeneousLocalization.val_mk', Subtype.val_eq_coe]
    by_cases' mem1 : a.num.1 โ x
    ยท right
      have : a.denom.1 - a.num.1 โ x.prime_compl := fun h =>
        a.denom_not_mem (sub_add_cancel a.denom.val a.num.val โธ Ideal.add_mem _ h mem1 : a.denom.1 โ x)
      apply is_unit_of_mul_eq_one _ (Localization.mk a.denom.1 โจa.denom.1 - a.num.1, thisโฉ)
      simp only [โ sub_mul, โ Localization.mk_mul, โ one_mulโ, โ Localization.sub_mk, Subtype.val_eq_coe, โ
        Submonoid.coe_mul]
      convert Localization.mk_self _
      simp only [Subtype.val_eq_coe, โ Submonoid.coe_mul]
      ring
      
    ยท left
      change _ โ x.prime_compl at mem1
      apply is_unit_of_mul_eq_one _ (Localization.mk a.denom.1 โจa.num.1, mem1โฉ)
      rw [Localization.mk_mul]
      convert Localization.mk_self _
      simpa only [โ mul_comm]
      

end HomogeneousLocalization

