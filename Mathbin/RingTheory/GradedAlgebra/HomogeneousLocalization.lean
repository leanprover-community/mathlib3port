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
- `ι` is a commutative monoid;
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ι → submodule R A` is the grading of `A`;
- `x : submonoid A` is a submonoid

## Main definitions and results

This file constructs the subring of `Aₓ` where the numerator and denominator have the same grading,
i.e. `{a/b ∈ Aₓ | ∃ (i : ι), a ∈ 𝒜ᵢ ∧ b ∈ 𝒜ᵢ}`.

* `homogeneous_localization.num_denom_same_deg`: a structure with a numerator and denominator field
  where they are required to have the same grading.

However `num_denom_same_deg 𝒜 x` cannot have a ring structure for many reasons, for example if `c`
is a `num_denom_same_deg`, then generally, `c + (-c)` is not necessarily `0` for degree reasons ---
`0` is considered to have grade zero (see `deg_zero`) but `c + (-c)` has the same degree as `c`. To
circumvent this, we quotient `num_denom_same_deg 𝒜 x` by the kernel of `c ↦ c.num / c.denom`.

* `homogeneous_localization.num_denom_same_deg.embedding` : for `x : submonoid A` and any
  `c : num_denom_same_deg 𝒜 x`, or equivalent a numerator and a denominator of the same degree,
  we get an element `c.num / c.denom` of `Aₓ`.
* `homogeneous_localization`: `num_denom_same_deg 𝒜 x` quotiented by kernel of `embedding 𝒜 x`.
* `homogeneous_localization.val`: if `f : homogeneous_localization 𝒜 x`, then `f.val` is an element
  of `Aₓ`. In another word, one can view `homogeneous_localization 𝒜 x` as a subring of `Aₓ`
  through `homogeneous_localization.val`.
* `homogeneous_localization.num`: if `f : homogeneous_localization 𝒜 x`, then `f.num : A` is the
  numerator of `f`.
* `homogeneous_localization.denom`: if `f : homogeneous_localization 𝒜 x`, then `f.denom : A` is the
  denominator of `f`.
* `homogeneous_localization.deg`: if `f : homogeneous_localization 𝒜 x`, then `f.deg : ι` is the
  degree of `f` such that `f.num ∈ 𝒜 f.deg` and `f.denom ∈ 𝒜 f.deg`
  (see `homogeneous_localization.num_mem_deg` and `homogeneous_localization.denom_mem_deg`).
* `homogeneous_localization.num_mem_deg`: if `f : homogeneous_localization 𝒜 x`, then
  `f.num_mem_deg` is a proof that `f.num ∈ 𝒜 f.deg`.
* `homogeneous_localization.denom_mem_deg`: if `f : homogeneous_localization 𝒜 x`, then
  `f.denom_mem_deg` is a proof that `f.denom ∈ 𝒜 f.deg`.
* `homogeneous_localization.eq_num_div_denom`: if `f : homogeneous_localization 𝒜 x`, then
  `f.val : Aₓ` is equal to `f.num / f.denom`.

* `homogeneous_localization.local_ring`: `homogeneous_localization 𝒜 x` is a local ring when `x` is
  the complement of some prime ideals.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


noncomputable section

open DirectSum BigOperators Pointwise

open DirectSum SetLike

variable {ι R A : Type _}

variable [AddCommMonoid ι] [DecidableEq ι]

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

variable (x : Submonoid A)

-- mathport name: «exprat »
local notation "at " x => Localization x

namespace HomogeneousLocalization

section

/-- Let `x` be a submonoid of `A`, then `num_denom_same_deg 𝒜 x` is a structure with a numerator and a
denominator with same grading such that the denominator is contained in `x`.
-/
@[nolint has_nonempty_instance]
structure NumDenomSameDeg where
  deg : ι
  (num denom : 𝒜 deg)
  denom_mem : (denom : A) ∈ x

end

namespace NumDenomSameDeg

open SetLike.GradedMonoid Submodule

variable {𝒜}

@[ext]
theorem ext {c1 c2 : NumDenomSameDeg 𝒜 x} (hdeg : c1.deg = c2.deg) (hnum : (c1.num : A) = c2.num)
    (hdenom : (c1.denom : A) = c2.denom) : c1 = c2 := by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  simp only
  exact ⟨hdeg, by subst hdeg <;> subst hnum, by subst hdeg <;> subst hdenom⟩

instance :
    One
      (NumDenomSameDeg 𝒜
        x) where one := { deg := 0, num := ⟨1, one_mem⟩, denom := ⟨1, one_mem⟩, denom_mem := Submonoid.one_mem _ }

@[simp]
theorem deg_one : (1 : NumDenomSameDeg 𝒜 x).deg = 0 :=
  rfl

@[simp]
theorem num_one : ((1 : NumDenomSameDeg 𝒜 x).num : A) = 1 :=
  rfl

@[simp]
theorem denom_one : ((1 : NumDenomSameDeg 𝒜 x).denom : A) = 1 :=
  rfl

instance : Zero (NumDenomSameDeg 𝒜 x) where zero := ⟨0, 0, ⟨1, one_mem⟩, Submonoid.one_mem _⟩

@[simp]
theorem deg_zero : (0 : NumDenomSameDeg 𝒜 x).deg = 0 :=
  rfl

@[simp]
theorem num_zero : (0 : NumDenomSameDeg 𝒜 x).num = 0 :=
  rfl

@[simp]
theorem denom_zero : ((0 : NumDenomSameDeg 𝒜 x).denom : A) = 1 :=
  rfl

instance :
    Mul
      (NumDenomSameDeg 𝒜
        x) where mul p q :=
    { deg := p.deg + q.deg, num := ⟨p.num * q.num, mul_mem p.num.Prop q.num.Prop⟩,
      denom := ⟨p.denom * q.denom, mul_mem p.denom.Prop q.denom.Prop⟩,
      denom_mem := Submonoid.mul_mem _ p.denom_mem q.denom_mem }

@[simp]
theorem deg_mul (c1 c2 : NumDenomSameDeg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
theorem num_mul (c1 c2 : NumDenomSameDeg 𝒜 x) : ((c1 * c2).num : A) = c1.num * c2.num :=
  rfl

@[simp]
theorem denom_mul (c1 c2 : NumDenomSameDeg 𝒜 x) : ((c1 * c2).denom : A) = c1.denom * c2.denom :=
  rfl

instance :
    Add
      (NumDenomSameDeg 𝒜
        x) where add c1 c2 :=
    { deg := c1.deg + c2.deg,
      num :=
        ⟨c1.denom * c2.num + c2.denom * c1.num,
          add_mem (mul_mem c1.denom.2 c2.num.2) (add_comm c2.deg c1.deg ▸ mul_mem c2.denom.2 c1.num.2)⟩,
      denom := ⟨c1.denom * c2.denom, mul_mem c1.denom.2 c2.denom.2⟩,
      denom_mem := Submonoid.mul_mem _ c1.denom_mem c2.denom_mem }

@[simp]
theorem deg_add (c1 c2 : NumDenomSameDeg 𝒜 x) : (c1 + c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
theorem num_add (c1 c2 : NumDenomSameDeg 𝒜 x) : ((c1 + c2).num : A) = c1.denom * c2.num + c2.denom * c1.num :=
  rfl

@[simp]
theorem denom_add (c1 c2 : NumDenomSameDeg 𝒜 x) : ((c1 + c2).denom : A) = c1.denom * c2.denom :=
  rfl

instance : Neg (NumDenomSameDeg 𝒜 x) where neg c := ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.denom, c.denom_mem⟩

@[simp]
theorem deg_neg (c : NumDenomSameDeg 𝒜 x) : (-c).deg = c.deg :=
  rfl

@[simp]
theorem num_neg (c : NumDenomSameDeg 𝒜 x) : ((-c).num : A) = -c.num :=
  rfl

@[simp]
theorem denom_neg (c : NumDenomSameDeg 𝒜 x) : ((-c).denom : A) = c.denom :=
  rfl

instance : CommMonoid (NumDenomSameDeg 𝒜 x) where
  one := 1
  mul := (· * ·)
  mul_assoc c1 c2 c3 := ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul c := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one c := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm c1 c2 := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)

instance :
    Pow (NumDenomSameDeg 𝒜 x)
      ℕ where pow c n :=
    ⟨n • c.deg, @GradedMonoid.Gmonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.Gmonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.denom, by
      induction' n with n ih
      · simpa only [coe_gnpow, pow_zero] using Submonoid.one_mem _
        
      · simpa only [pow_succ', coe_gnpow] using x.mul_mem ih c.denom_mem
        ⟩

@[simp]
theorem deg_pow (c : NumDenomSameDeg 𝒜 x) (n : ℕ) : (c ^ n).deg = n • c.deg :=
  rfl

@[simp]
theorem num_pow (c : NumDenomSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).num : A) = c.num ^ n :=
  rfl

@[simp]
theorem denom_pow (c : NumDenomSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).denom : A) = c.denom ^ n :=
  rfl

section HasSmul

variable {α : Type _} [HasSmul α R] [HasSmul α A] [IsScalarTower α R A]

instance : HasSmul α (NumDenomSameDeg 𝒜 x) where smul m c := ⟨c.deg, m • c.num, c.denom, c.denom_mem⟩

@[simp]
theorem deg_smul (c : NumDenomSameDeg 𝒜 x) (m : α) : (m • c).deg = c.deg :=
  rfl

@[simp]
theorem num_smul (c : NumDenomSameDeg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num :=
  rfl

@[simp]
theorem denom_smul (c : NumDenomSameDeg 𝒜 x) (m : α) : ((m • c).denom : A) = c.denom :=
  rfl

end HasSmul

variable (𝒜)

/-- For `x : prime ideal of A` and any `p : num_denom_same_deg 𝒜 x`, or equivalent a numerator and a
denominator of the same degree, we get an element `p.num / p.denom` of `Aₓ`.
-/
def embedding (p : NumDenomSameDeg 𝒜 x) : at x :=
  Localization.mk p.num ⟨p.denom, p.denom_mem⟩

end NumDenomSameDeg

end HomogeneousLocalization

/-- For `x : prime ideal of A`, `homogeneous_localization 𝒜 x` is `num_denom_same_deg 𝒜 x` modulo the
kernel of `embedding 𝒜 x`. This is essentially the subring of `Aₓ` where the numerator and
denominator share the same grading.
-/
@[nolint has_nonempty_instance]
def HomogeneousLocalization : Type _ :=
  Quotient (Setoid.ker <| HomogeneousLocalization.NumDenomSameDeg.embedding 𝒜 x)

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenomSameDeg

variable {𝒜} {x}

/-- View an element of `homogeneous_localization 𝒜 x` as an element of `Aₓ` by forgetting that the
numerator and denominator are of the same grading.
-/
def val (y : HomogeneousLocalization 𝒜 x) : at x :=
  (Quotient.liftOn' y (NumDenomSameDeg.embedding 𝒜 x)) fun _ _ => id

@[simp]
theorem val_mk' (i : NumDenomSameDeg 𝒜 x) : val (Quotient.mk' i) = Localization.mk i.num ⟨i.denom, i.denom_mem⟩ :=
  rfl

variable (x)

theorem val_injective : Function.Injective (@HomogeneousLocalization.val _ _ _ _ _ _ _ _ 𝒜 _ x) := fun a b =>
  (Quotient.recOnSubsingleton₂' a b) fun a b h => Quotient.sound' h

instance hasPow :
    Pow (HomogeneousLocalization 𝒜 x)
      ℕ where pow z n :=
    (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
        change Localization.mk _ _ = Localization.mk _ _
        simp only [num_pow, denom_pow]
        convert congr_arg (fun z => z ^ n) h <;> erw [Localization.mk_pow] <;> rfl :
        HomogeneousLocalization 𝒜 x → HomogeneousLocalization 𝒜 x)
      z

section HasSmul

variable {α : Type _} [HasSmul α R] [HasSmul α A] [IsScalarTower α R A]

variable [IsScalarTower α A A]

instance :
    HasSmul α
      (HomogeneousLocalization 𝒜
        x) where smul m :=
    Quotient.map' ((· • ·) m) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_smul, denom_smul]
      convert congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk] <;> rfl

@[simp]
theorem smul_val (y : HomogeneousLocalization 𝒜 x) (n : α) : (n • y).val = n • y.val := by
  induction y using Quotient.induction_on
  unfold HomogeneousLocalization.val HasSmul.smul
  simp only [Quotient.lift_on₂'_mk, Quotient.lift_on'_mk]
  change Localization.mk _ _ = n • Localization.mk _ _
  dsimp only
  rw [Localization.smul_mk]
  congr 1

end HasSmul

instance :
    Neg
      (HomogeneousLocalization 𝒜
        x) where neg :=
    Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_neg, denom_neg, ← Localization.neg_mk]
      exact congr_arg (fun c => -c) h

instance :
    Add
      (HomogeneousLocalization 𝒜
        x) where add :=
    Quotient.map₂' (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) =>
      by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_add, denom_add, ← Localization.add_mk]
      convert congr_arg₂ (· + ·) h h' <;> erw [Localization.add_mk] <;> rfl

instance : Sub (HomogeneousLocalization 𝒜 x) where sub z1 z2 := z1 + -z2

instance :
    Mul
      (HomogeneousLocalization 𝒜
        x) where mul :=
    Quotient.map₂' (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) =>
      by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_mul, denom_mul]
      convert congr_arg₂ (· * ·) h h' <;> erw [Localization.mk_mul] <;> rfl

instance : One (HomogeneousLocalization 𝒜 x) where one := Quotient.mk' 1

instance : Zero (HomogeneousLocalization 𝒜 x) where zero := Quotient.mk' 0

theorem zero_eq : (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk' 0 :=
  rfl

theorem one_eq : (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk' 1 :=
  rfl

variable {x}

theorem zero_val : (0 : HomogeneousLocalization 𝒜 x).val = 0 :=
  Localization.mk_zero _

theorem one_val : (1 : HomogeneousLocalization 𝒜 x).val = 1 :=
  Localization.mk_one

@[simp]
theorem add_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 + y2).val = y1.val + y2.val := by
  induction y1 using Quotient.induction_on
  induction y2 using Quotient.induction_on
  unfold HomogeneousLocalization.val Add.add
  simp only [Quotient.lift_on₂'_mk, Quotient.lift_on'_mk]
  change Localization.mk _ _ = Localization.mk _ _ + Localization.mk _ _
  dsimp only
  rw [Localization.add_mk]
  rfl

@[simp]
theorem mul_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 * y2).val = y1.val * y2.val := by
  induction y1 using Quotient.induction_on
  induction y2 using Quotient.induction_on
  unfold HomogeneousLocalization.val Mul.mul
  simp only [Quotient.lift_on₂'_mk, Quotient.lift_on'_mk]
  change Localization.mk _ _ = Localization.mk _ _ * Localization.mk _ _
  dsimp only
  rw [Localization.mk_mul]
  rfl

@[simp]
theorem neg_val (y : HomogeneousLocalization 𝒜 x) : (-y).val = -y.val := by
  induction y using Quotient.induction_on
  unfold HomogeneousLocalization.val Neg.neg
  simp only [Quotient.lift_on₂'_mk, Quotient.lift_on'_mk]
  change Localization.mk _ _ = -Localization.mk _ _
  dsimp only
  rw [Localization.neg_mk]
  rfl

@[simp]
theorem sub_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 - y2).val = y1.val - y2.val := by
  rw [show y1 - y2 = y1 + -y2 from rfl, add_val, neg_val] <;> rfl

@[simp]
theorem pow_val (y : HomogeneousLocalization 𝒜 x) (n : ℕ) : (y ^ n).val = y.val ^ n := by
  induction y using Quotient.induction_on
  unfold HomogeneousLocalization.val Pow.pow
  simp only [Quotient.lift_on₂'_mk, Quotient.lift_on'_mk]
  change Localization.mk _ _ = Localization.mk _ _ ^ n
  rw [Localization.mk_pow]
  dsimp only
  congr 1

instance : HasNatCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Nat.unaryCast⟩

instance : HasIntCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Int.castDef⟩

@[simp]
theorem nat_cast_val (n : ℕ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, zero_val, one_val, *]

@[simp]
theorem int_cast_val (n : ℤ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, zero_val, one_val, *]

instance homogenousLocalizationCommRing : CommRing (HomogeneousLocalization 𝒜 x) :=
  (HomogeneousLocalization.val_injective x).CommRing _ zero_val one_val add_val mul_val neg_val sub_val
    (fun z n => smul_val x z n) (fun z n => smul_val x z n) pow_val nat_cast_val int_cast_val

instance homogeneousLocalizationAlgebra : Algebra (HomogeneousLocalization 𝒜 x) (Localization x) where
  smul p q := p.val * q
  toFun := val
  map_one' := one_val
  map_mul' := mul_val
  map_zero' := zero_val
  map_add' := add_val
  commutes' p q := mul_comm _ _
  smul_def' p q := rfl

end HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenomSameDeg

variable {𝒜} {x}

/-- numerator of an element in `homogeneous_localization x`-/
def num (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out' f).num

/-- denominator of an element in `homogeneous_localization x`-/
def denom (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out' f).denom

/-- For an element in `homogeneous_localization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : HomogeneousLocalization 𝒜 x) : ι :=
  (Quotient.out' f).deg

theorem denom_mem (f : HomogeneousLocalization 𝒜 x) : f.denom ∈ x :=
  (Quotient.out' f).denom_mem

theorem num_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.num ∈ 𝒜 f.deg :=
  (Quotient.out' f).num.2

theorem denom_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.denom ∈ 𝒜 f.deg :=
  (Quotient.out' f).denom.2

theorem eq_num_div_denom (f : HomogeneousLocalization 𝒜 x) : f.val = Localization.mk f.num ⟨f.denom, f.denom_mem⟩ := by
  have := Quotient.out_eq' f
  apply_fun HomogeneousLocalization.val  at this
  rw [← this]
  unfold HomogeneousLocalization.val
  simp only [Quotient.lift_on'_mk']
  rfl

theorem ext_iff_val (f g : HomogeneousLocalization 𝒜 x) : f = g ↔ f.val = g.val :=
  { mp := fun h => h ▸ rfl,
    mpr := fun h => by
      induction f using Quotient.induction_on
      induction g using Quotient.induction_on
      rw [Quotient.eq]
      unfold HomogeneousLocalization.val at h
      simpa only [Quotient.lift_on'_mk] using h }

section

variable (𝒜) (𝔭 : Ideal A) [Ideal.IsPrime 𝔭]

/-- Localizing a ring homogeneously at a prime ideal-/
abbrev AtPrime :=
  HomogeneousLocalization 𝒜 𝔭.primeCompl

theorem is_unit_iff_is_unit_val (f : HomogeneousLocalization.AtPrime 𝒜 𝔭) : IsUnit f.val ↔ IsUnit f :=
  ⟨fun h1 => by
    rcases h1 with ⟨⟨a, b, eq0, eq1⟩, eq2 : a = f.val⟩
    rw [eq2] at eq0 eq1
    clear a eq2
    induction' b using Localization.induction_on with data
    rcases data with ⟨a, ⟨b, hb⟩⟩
    dsimp only at eq0 eq1
    have b_f_denom_not_mem : b * f.denom ∈ 𝔭.prime_compl := fun r =>
      Or.elim (Ideal.IsPrime.mem_or_mem inferInstance r) (fun r2 => hb r2) fun r2 => f.denom_mem r2
    rw [f.eq_num_div_denom, Localization.mk_mul,
      show (⟨b, hb⟩ : 𝔭.prime_compl) * ⟨f.denom, _⟩ = ⟨b * f.denom, _⟩ from rfl,
      show (1 : Localization.AtPrime 𝔭) = Localization.mk 1 1 by erw [Localization.mk_self 1], Localization.mk_eq_mk',
      IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨c, hc⟩, eq1⟩
    simp only [← Subtype.val_eq_coe] at eq1
    change a * f.num * 1 * c = _ at eq1
    simp only [one_mul, mul_one] at eq1
    have mem1 : a * f.num * c ∈ 𝔭.prime_compl :=
      eq1.symm ▸ fun r => Or.elim (Ideal.IsPrime.mem_or_mem inferInstance r) (by tauto) (by tauto)
    have mem2 : f.num ∉ 𝔭 := by
      contrapose! mem1
      erw [not_not]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ mem1)
    refine' ⟨⟨f, Quotient.mk' ⟨f.deg, ⟨f.denom, f.denom_mem_deg⟩, ⟨f.num, f.num_mem_deg⟩, mem2⟩, _, _⟩, rfl⟩ <;>
      simp only [ext_iff_val, mul_val, val_mk', ← Subtype.val_eq_coe, f.eq_num_div_denom, Localization.mk_mul,
          one_val] <;>
        convert Localization.mk_self _ <;> simpa only [mul_comm] ,
    fun ⟨⟨_, b, eq1, eq2⟩, rfl⟩ => by
    simp only [ext_iff_val, mul_val, one_val] at eq1 eq2
    exact ⟨⟨f.val, b.val, eq1, eq2⟩, rfl⟩⟩

instance : Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  ⟨⟨0, 1, fun r => by simpa [ext_iff_val, zero_val, one_val, zero_ne_one] using r⟩⟩

instance : LocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  LocalRing.ofIsUnitOrIsUnitOneSubSelf fun a => by
    simp only [← is_unit_iff_is_unit_val, sub_val, one_val]
    induction a using Quotient.induction_on'
    simp only [HomogeneousLocalization.val_mk', ← Subtype.val_eq_coe]
    by_cases mem1:a.num.1 ∈ 𝔭
    · right
      have : a.denom.1 - a.num.1 ∈ 𝔭.prime_compl := fun h =>
        a.denom_mem (sub_add_cancel a.denom.val a.num.val ▸ Ideal.add_mem _ h mem1 : a.denom.1 ∈ 𝔭)
      apply is_unit_of_mul_eq_one _ (Localization.mk a.denom.1 ⟨a.denom.1 - a.num.1, this⟩)
      simp only [sub_mul, Localization.mk_mul, one_mul, Localization.sub_mk, ← Subtype.val_eq_coe, Submonoid.coe_mul]
      convert Localization.mk_self _
      simp only [← Subtype.val_eq_coe, Submonoid.coe_mul]
      ring
      
    · left
      change _ ∈ 𝔭.prime_compl at mem1
      apply is_unit_of_mul_eq_one _ (Localization.mk a.denom.1 ⟨a.num.1, mem1⟩)
      rw [Localization.mk_mul]
      convert Localization.mk_self _
      simpa only [mul_comm]
      

end

section

variable (𝒜) (f : A)

/-- Localising away from powers of `f` homogeneously.-/
abbrev Away :=
  HomogeneousLocalization 𝒜 (Submonoid.powers f)

end

end HomogeneousLocalization

