/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Algebra.Hom.Iterate
import Analysis.SpecificLimits.Basic
import Order.Iterate
import Order.SemiconjSup
import Topology.Algebra.Order.MonotoneContinuity

#align_import dynamics.circle.rotation_number.translation_number from "leanprover-community/mathlib"@"ce38d86c0b2d427ce208c3cee3159cb421d2b3c4"

/-!
# Translation number of a monotone real map that commutes with `x ↦ x + 1`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `f : ℝ → ℝ` be a monotone map such that `f (x + 1) = f x + 1` for all `x`. Then the limit
$$
  \tau(f)=\lim_{n\to\infty}{f^n(x)-x}{n}
$$
exists and does not depend on `x`. This number is called the *translation number* of `f`.
Different authors use different notation for this number: `τ`, `ρ`, `rot`, etc

In this file we define a structure `circle_deg1_lift` for bundled maps with these properties, define
translation number of `f : circle_deg1_lift`, prove some estimates relating `f^n(x)-x` to `τ(f)`. In
case of a continuous map `f` we also prove that `f` admits a point `x` such that `f^n(x)=x+m` if and
only if `τ(f)=m/n`.

Maps of this type naturally appear as lifts of orientation preserving circle homeomorphisms. More
precisely, let `f` be an orientation preserving homeomorphism of the circle $S^1=ℝ/ℤ$, and
consider a real number `a` such that
`⟦a⟧ = f 0`, where `⟦⟧` means the natural projection `ℝ → ℝ/ℤ`. Then there exists a unique
continuous function `F : ℝ → ℝ` such that `F 0 = a` and `⟦F x⟧ = f ⟦x⟧` for all `x` (this fact is
not formalized yet). This function is strictly monotone, continuous, and satisfies
`F (x + 1) = F x + 1`. The number `⟦τ F⟧ : ℝ / ℤ` is called the *rotation number* of `f`.
It does not depend on the choice of `a`.

## Main definitions

* `circle_deg1_lift`: a monotone map `f : ℝ → ℝ` such that `f (x + 1) = f x + 1` for all `x`;
  the type `circle_deg1_lift` is equipped with `lattice` and `monoid` structures; the
  multiplication is given by composition: `(f * g) x = f (g x)`.
* `circle_deg1_lift.translation_number`: translation number of `f : circle_deg1_lift`.

## Main statements

We prove the following properties of `circle_deg1_lift.translation_number`.

* `circle_deg1_lift.translation_number_eq_of_dist_bounded`: if the distance between `(f^n) 0`
  and `(g^n) 0` is bounded from above uniformly in `n : ℕ`, then `f` and `g` have equal
  translation numbers.

* `circle_deg1_lift.translation_number_eq_of_semiconj_by`: if two `circle_deg1_lift` maps `f`, `g`
  are semiconjugate by a `circle_deg1_lift` map, then `τ f = τ g`.

* `circle_deg1_lift.translation_number_units_inv`: if `f` is an invertible `circle_deg1_lift` map
  (equivalently, `f` is a lift of an orientation-preserving circle homeomorphism), then
  the translation number of `f⁻¹` is the negative of the translation number of `f`.

* `circle_deg1_lift.translation_number_mul_of_commute`: if `f` and `g` commute, then
  `τ (f * g) = τ f + τ g`.

* `circle_deg1_lift.translation_number_eq_rat_iff`: the translation number of `f` is equal to
  a rational number `m / n` if and only if `(f^n) x = x + m` for some `x`.

* `circle_deg1_lift.semiconj_of_bijective_of_translation_number_eq`: if `f` and `g` are two
  bijective `circle_deg1_lift` maps and their translation numbers are equal, then these
  maps are semiconjugate to each other.

* `circle_deg1_lift.semiconj_of_group_action_of_forall_translation_number_eq`: let `f₁` and `f₂` be
  two actions of a group `G` on the circle by degree 1 maps (formally, `f₁` and `f₂` are two
  homomorphisms from `G →* circle_deg1_lift`). If the translation numbers of `f₁ g` and `f₂ g` are
  equal to each other for all `g : G`, then these two actions are semiconjugate by some `F :
  circle_deg1_lift`. This is a version of Proposition 5.4 from [Étienne Ghys, Groupes
  d'homeomorphismes du cercle et cohomologie bornee][ghys87:groupes].

## Notation

We use a local notation `τ` for the translation number of `f : circle_deg1_lift`.

## Implementation notes

We define the translation number of `f : circle_deg1_lift` to be the limit of the sequence
`(f ^ (2 ^ n)) 0 / (2 ^ n)`, then prove that `((f ^ n) x - x) / n` tends to this number for any `x`.
This way it is much easier to prove that the limit exists and basic properties of the limit.

We define translation number for a wider class of maps `f : ℝ → ℝ` instead of lifts of orientation
preserving circle homeomorphisms for two reasons:

* non-strictly monotone circle self-maps with discontinuities naturally appear as Poincaré maps
  for some flows on the two-torus (e.g., one can take a constant flow and glue in a few Cherry
  cells);
* definition and some basic properties still work for this class.

## References

* [Étienne Ghys, Groupes d'homeomorphismes du cercle et cohomologie bornee][ghys87:groupes]

## TODO

Here are some short-term goals.

* Introduce a structure or a typeclass for lifts of circle homeomorphisms. We use `units
  circle_deg1_lift` for now, but it's better to have a dedicated type (or a typeclass?).

* Prove that the `semiconj_by` relation on circle homeomorphisms is an equivalence relation.

* Introduce `conditionally_complete_lattice` structure, use it in the proof of
  `circle_deg1_lift.semiconj_of_group_action_of_forall_translation_number_eq`.

* Prove that the orbits of the irrational rotation are dense in the circle. Deduce that a
  homeomorphism with an irrational rotation is semiconjugate to the corresponding irrational
  translation by a continuous `circle_deg1_lift`.

## Tags

circle homeomorphism, rotation number
-/


open Filter Set

open Function hiding Commute

open Int

open scoped Topology Classical

/-!
### Definition and monoid structure
-/


#print CircleDeg1Lift /-
/-- A lift of a monotone degree one map `S¹ → S¹`. -/
structure CircleDeg1Lift : Type where
  toFun : ℝ → ℝ
  monotone' : Monotone to_fun
  map_add_one' : ∀ x, to_fun (x + 1) = to_fun x + 1
#align circle_deg1_lift CircleDeg1Lift
-/

namespace CircleDeg1Lift

instance : CoeFun CircleDeg1Lift fun _ => ℝ → ℝ :=
  ⟨CircleDeg1Lift.toFun⟩

#print CircleDeg1Lift.coe_mk /-
@[simp]
theorem coe_mk (f h₁ h₂) : ⇑(mk f h₁ h₂) = f :=
  rfl
#align circle_deg1_lift.coe_mk CircleDeg1Lift.coe_mk
-/

variable (f g : CircleDeg1Lift)

#print CircleDeg1Lift.monotone /-
protected theorem monotone : Monotone f :=
  f.monotone'
#align circle_deg1_lift.monotone CircleDeg1Lift.monotone
-/

#print CircleDeg1Lift.mono /-
@[mono]
theorem mono {x y} (h : x ≤ y) : f x ≤ f y :=
  f.Monotone h
#align circle_deg1_lift.mono CircleDeg1Lift.mono
-/

#print CircleDeg1Lift.strictMono_iff_injective /-
theorem strictMono_iff_injective : StrictMono f ↔ Injective f :=
  f.Monotone.strictMono_iff_injective
#align circle_deg1_lift.strict_mono_iff_injective CircleDeg1Lift.strictMono_iff_injective
-/

#print CircleDeg1Lift.map_add_one /-
@[simp]
theorem map_add_one : ∀ x, f (x + 1) = f x + 1 :=
  f.map_add_one'
#align circle_deg1_lift.map_add_one CircleDeg1Lift.map_add_one
-/

#print CircleDeg1Lift.map_one_add /-
@[simp]
theorem map_one_add (x : ℝ) : f (1 + x) = 1 + f x := by rw [add_comm, map_add_one, add_comm]
#align circle_deg1_lift.map_one_add CircleDeg1Lift.map_one_add
-/

theorem coe_inj : ∀ ⦃f g : CircleDeg1Lift⦄, (f : ℝ → ℝ) = g → f = g :=
  fun ⟨f, fm, fd⟩ ⟨g, gm, gd⟩ h => by congr <;> exact h
#align circle_deg1_lift.coe_inj CircleDeg1Lift.coe_inj

#print CircleDeg1Lift.ext /-
@[ext]
theorem ext ⦃f g : CircleDeg1Lift⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_inj <| funext h
#align circle_deg1_lift.ext CircleDeg1Lift.ext
-/

#print CircleDeg1Lift.ext_iff /-
theorem ext_iff {f g : CircleDeg1Lift} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩
#align circle_deg1_lift.ext_iff CircleDeg1Lift.ext_iff
-/

instance : Monoid CircleDeg1Lift
    where
  mul f g :=
    { toFun := f ∘ g
      monotone' := f.Monotone.comp g.Monotone
      map_add_one' := fun x => by simp [map_add_one] }
  one := ⟨id, monotone_id, fun _ => rfl⟩
  mul_one f := coe_inj <| Function.comp_id f
  one_mul f := coe_inj <| Function.id_comp f
  mul_assoc f₁ f₂ f₃ := coe_inj rfl

instance : Inhabited CircleDeg1Lift :=
  ⟨1⟩

#print CircleDeg1Lift.coe_mul /-
@[simp]
theorem coe_mul : ⇑(f * g) = f ∘ g :=
  rfl
#align circle_deg1_lift.coe_mul CircleDeg1Lift.coe_mul
-/

#print CircleDeg1Lift.mul_apply /-
theorem mul_apply (x) : (f * g) x = f (g x) :=
  rfl
#align circle_deg1_lift.mul_apply CircleDeg1Lift.mul_apply
-/

#print CircleDeg1Lift.coe_one /-
@[simp]
theorem coe_one : ⇑(1 : CircleDeg1Lift) = id :=
  rfl
#align circle_deg1_lift.coe_one CircleDeg1Lift.coe_one
-/

#print CircleDeg1Lift.unitsHasCoeToFun /-
instance unitsHasCoeToFun : CoeFun CircleDeg1Liftˣ fun _ => ℝ → ℝ :=
  ⟨fun f => ⇑(f : CircleDeg1Lift)⟩
#align circle_deg1_lift.units_has_coe_to_fun CircleDeg1Lift.unitsHasCoeToFun
-/

@[simp, norm_cast]
theorem units_coe (f : CircleDeg1Liftˣ) : ⇑(f : CircleDeg1Lift) = f :=
  rfl
#align circle_deg1_lift.units_coe CircleDeg1Lift.units_coe

#print CircleDeg1Lift.units_inv_apply_apply /-
@[simp]
theorem units_inv_apply_apply (f : CircleDeg1Liftˣ) (x : ℝ) : (f⁻¹ : CircleDeg1Liftˣ) (f x) = x :=
  by simp only [← units_coe, ← mul_apply, f.inv_mul, coe_one, id]
#align circle_deg1_lift.units_inv_apply_apply CircleDeg1Lift.units_inv_apply_apply
-/

#print CircleDeg1Lift.units_apply_inv_apply /-
@[simp]
theorem units_apply_inv_apply (f : CircleDeg1Liftˣ) (x : ℝ) : f ((f⁻¹ : CircleDeg1Liftˣ) x) = x :=
  by simp only [← units_coe, ← mul_apply, f.mul_inv, coe_one, id]
#align circle_deg1_lift.units_apply_inv_apply CircleDeg1Lift.units_apply_inv_apply
-/

#print CircleDeg1Lift.toOrderIso /-
/-- If a lift of a circle map is bijective, then it is an order automorphism of the line. -/
def toOrderIso : CircleDeg1Liftˣ →* ℝ ≃o ℝ
    where
  toFun f :=
    { toFun := f
      invFun := ⇑f⁻¹
      left_inv := units_inv_apply_apply f
      right_inv := units_apply_inv_apply f
      map_rel_iff' := fun x y => ⟨fun h => by simpa using mono (↑f⁻¹) h, mono f⟩ }
  map_one' := rfl
  map_mul' f g := rfl
#align circle_deg1_lift.to_order_iso CircleDeg1Lift.toOrderIso
-/

#print CircleDeg1Lift.coe_toOrderIso /-
@[simp]
theorem coe_toOrderIso (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f) = f :=
  rfl
#align circle_deg1_lift.coe_to_order_iso CircleDeg1Lift.coe_toOrderIso
-/

#print CircleDeg1Lift.coe_toOrderIso_symm /-
@[simp]
theorem coe_toOrderIso_symm (f : CircleDeg1Liftˣ) :
    ⇑(toOrderIso f).symm = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl
#align circle_deg1_lift.coe_to_order_iso_symm CircleDeg1Lift.coe_toOrderIso_symm
-/

#print CircleDeg1Lift.coe_toOrderIso_inv /-
@[simp]
theorem coe_toOrderIso_inv (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f)⁻¹ = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl
#align circle_deg1_lift.coe_to_order_iso_inv CircleDeg1Lift.coe_toOrderIso_inv
-/

#print CircleDeg1Lift.isUnit_iff_bijective /-
theorem isUnit_iff_bijective {f : CircleDeg1Lift} : IsUnit f ↔ Bijective f :=
  ⟨fun ⟨u, h⟩ => h ▸ (toOrderIso u).Bijective, fun h =>
    Units.isUnit
      { val := f
        inv :=
          { toFun := (Equiv.ofBijective f h).symm
            monotone' := fun x y hxy =>
              (f.strictMono_iff_injective.2 h.1).le_iff_le.1
                (by simp only [Equiv.ofBijective_apply_symm_apply f h, hxy])
            map_add_one' := fun x =>
              h.1 <| by simp only [Equiv.ofBijective_apply_symm_apply f, f.map_add_one] }
        val_inv := ext <| Equiv.ofBijective_apply_symm_apply f h
        inv_val := ext <| Equiv.ofBijective_symm_apply_apply f h }⟩
#align circle_deg1_lift.is_unit_iff_bijective CircleDeg1Lift.isUnit_iff_bijective
-/

#print CircleDeg1Lift.coe_pow /-
theorem coe_pow : ∀ n : ℕ, ⇑(f ^ n) = f^[n]
  | 0 => rfl
  | n + 1 => by ext x; simp [coe_pow n, pow_succ']
#align circle_deg1_lift.coe_pow CircleDeg1Lift.coe_pow
-/

#print CircleDeg1Lift.semiconjBy_iff_semiconj /-
theorem semiconjBy_iff_semiconj {f g₁ g₂ : CircleDeg1Lift} :
    SemiconjBy f g₁ g₂ ↔ Semiconj f g₁ g₂ :=
  ext_iff
#align circle_deg1_lift.semiconj_by_iff_semiconj CircleDeg1Lift.semiconjBy_iff_semiconj
-/

#print CircleDeg1Lift.commute_iff_commute /-
theorem commute_iff_commute {f g : CircleDeg1Lift} : Commute f g ↔ Function.Commute f g :=
  ext_iff
#align circle_deg1_lift.commute_iff_commute CircleDeg1Lift.commute_iff_commute
-/

/-!
### Translate by a constant
-/


#print CircleDeg1Lift.translate /-
/-- The map `y ↦ x + y` as a `circle_deg1_lift`. More precisely, we define a homomorphism from
`multiplicative ℝ` to `circle_deg1_liftˣ`, so the translation by `x` is
`translation (multiplicative.of_add x)`. -/
def translate : Multiplicative ℝ →* CircleDeg1Liftˣ := by
  refine' (Units.map _).comp to_units.to_monoid_hom <;>
    exact
      { toFun := fun x =>
          ⟨fun y => x.toAdd + y, fun y₁ y₂ h => add_le_add_left h _, fun y =>
            (add_assoc _ _ _).symm⟩
        map_one' := ext <| zero_add
        map_mul' := fun x y => ext <| add_assoc _ _ }
#align circle_deg1_lift.translate CircleDeg1Lift.translate
-/

#print CircleDeg1Lift.translate_apply /-
@[simp]
theorem translate_apply (x y : ℝ) : translate (Multiplicative.ofAdd x) y = x + y :=
  rfl
#align circle_deg1_lift.translate_apply CircleDeg1Lift.translate_apply
-/

#print CircleDeg1Lift.translate_inv_apply /-
@[simp]
theorem translate_inv_apply (x y : ℝ) : (translate <| Multiplicative.ofAdd x)⁻¹ y = -x + y :=
  rfl
#align circle_deg1_lift.translate_inv_apply CircleDeg1Lift.translate_inv_apply
-/

#print CircleDeg1Lift.translate_zpow /-
@[simp]
theorem translate_zpow (x : ℝ) (n : ℤ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) := by
  simp only [← zsmul_eq_mul, ofAdd_zsmul, MonoidHom.map_zpow]
#align circle_deg1_lift.translate_zpow CircleDeg1Lift.translate_zpow
-/

#print CircleDeg1Lift.translate_pow /-
@[simp]
theorem translate_pow (x : ℝ) (n : ℕ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) :=
  translate_zpow x n
#align circle_deg1_lift.translate_pow CircleDeg1Lift.translate_pow
-/

#print CircleDeg1Lift.translate_iterate /-
@[simp]
theorem translate_iterate (x : ℝ) (n : ℕ) :
    translate (Multiplicative.ofAdd x)^[n] = translate (Multiplicative.ofAdd <| ↑n * x) := by
  rw [← units_coe, ← coe_pow, ← Units.val_pow_eq_pow_val, translate_pow, units_coe]
#align circle_deg1_lift.translate_iterate CircleDeg1Lift.translate_iterate
-/

/-!
### Commutativity with integer translations

In this section we prove that `f` commutes with translations by an integer number.
First we formulate these statements (for a natural or an integer number,
addition on the left or on the right, addition or subtraction) using `function.commute`,
then reformulate as `simp` lemmas `map_int_add` etc.
-/


#print CircleDeg1Lift.commute_nat_add /-
theorem commute_nat_add (n : ℕ) : Function.Commute f ((· + ·) n) := by
  simpa only [nsmul_one, add_left_iterate] using Function.Commute.iterate_right f.map_one_add n
#align circle_deg1_lift.commute_nat_add CircleDeg1Lift.commute_nat_add
-/

#print CircleDeg1Lift.commute_add_nat /-
theorem commute_add_nat (n : ℕ) : Function.Commute f fun x => x + n := by
  simp only [add_comm _ (n : ℝ), f.commute_nat_add n]
#align circle_deg1_lift.commute_add_nat CircleDeg1Lift.commute_add_nat
-/

#print CircleDeg1Lift.commute_sub_nat /-
theorem commute_sub_nat (n : ℕ) : Function.Commute f fun x => x - n := by
  simpa only [sub_eq_add_neg] using
    (f.commute_add_nat n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv
#align circle_deg1_lift.commute_sub_nat CircleDeg1Lift.commute_sub_nat
-/

#print CircleDeg1Lift.commute_add_int /-
theorem commute_add_int : ∀ n : ℤ, Function.Commute f fun x => x + n
  | (n : ℕ) => f.commute_add_nat n
  | -[n+1] => by simpa [sub_eq_add_neg] using f.commute_sub_nat (n + 1)
#align circle_deg1_lift.commute_add_int CircleDeg1Lift.commute_add_int
-/

#print CircleDeg1Lift.commute_int_add /-
theorem commute_int_add (n : ℤ) : Function.Commute f ((· + ·) n) := by
  simpa only [add_comm _ (n : ℝ)] using f.commute_add_int n
#align circle_deg1_lift.commute_int_add CircleDeg1Lift.commute_int_add
-/

#print CircleDeg1Lift.commute_sub_int /-
theorem commute_sub_int (n : ℤ) : Function.Commute f fun x => x - n := by
  simpa only [sub_eq_add_neg] using
    (f.commute_add_int n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv
#align circle_deg1_lift.commute_sub_int CircleDeg1Lift.commute_sub_int
-/

#print CircleDeg1Lift.map_int_add /-
@[simp]
theorem map_int_add (m : ℤ) (x : ℝ) : f (m + x) = m + f x :=
  f.commute_int_add m x
#align circle_deg1_lift.map_int_add CircleDeg1Lift.map_int_add
-/

#print CircleDeg1Lift.map_add_int /-
@[simp]
theorem map_add_int (x : ℝ) (m : ℤ) : f (x + m) = f x + m :=
  f.commute_add_int m x
#align circle_deg1_lift.map_add_int CircleDeg1Lift.map_add_int
-/

#print CircleDeg1Lift.map_sub_int /-
@[simp]
theorem map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
  f.commute_sub_int n x
#align circle_deg1_lift.map_sub_int CircleDeg1Lift.map_sub_int
-/

#print CircleDeg1Lift.map_add_nat /-
@[simp]
theorem map_add_nat (x : ℝ) (n : ℕ) : f (x + n) = f x + n :=
  f.map_add_int x n
#align circle_deg1_lift.map_add_nat CircleDeg1Lift.map_add_nat
-/

#print CircleDeg1Lift.map_nat_add /-
@[simp]
theorem map_nat_add (n : ℕ) (x : ℝ) : f (n + x) = n + f x :=
  f.map_int_add n x
#align circle_deg1_lift.map_nat_add CircleDeg1Lift.map_nat_add
-/

#print CircleDeg1Lift.map_sub_nat /-
@[simp]
theorem map_sub_nat (x : ℝ) (n : ℕ) : f (x - n) = f x - n :=
  f.map_sub_int x n
#align circle_deg1_lift.map_sub_nat CircleDeg1Lift.map_sub_nat
-/

#print CircleDeg1Lift.map_int_of_map_zero /-
theorem map_int_of_map_zero (n : ℤ) : f n = f 0 + n := by rw [← f.map_add_int, zero_add]
#align circle_deg1_lift.map_int_of_map_zero CircleDeg1Lift.map_int_of_map_zero
-/

#print CircleDeg1Lift.map_fract_sub_fract_eq /-
@[simp]
theorem map_fract_sub_fract_eq (x : ℝ) : f (fract x) - fract x = f x - x := by
  rw [Int.fract, f.map_sub_int, sub_sub_sub_cancel_right]
#align circle_deg1_lift.map_fract_sub_fract_eq CircleDeg1Lift.map_fract_sub_fract_eq
-/

/-!
### Pointwise order on circle maps
-/


/-- Monotone circle maps form a lattice with respect to the pointwise order -/
noncomputable instance : Lattice CircleDeg1Lift
    where
  sup f g :=
    { toFun := fun x => max (f x) (g x)
      monotone' := fun x y h => max_le_max (f.mono h) (g.mono h)
      -- TODO: generalize to `monotone.max`
      map_add_one' := fun x => by simp [max_add_add_right] }
  le f g := ∀ x, f x ≤ g x
  le_refl f x := le_refl (f x)
  le_trans f₁ f₂ f₃ h₁₂ h₂₃ x := le_trans (h₁₂ x) (h₂₃ x)
  le_antisymm f₁ f₂ h₁₂ h₂₁ := ext fun x => le_antisymm (h₁₂ x) (h₂₁ x)
  le_sup_left f g x := le_max_left (f x) (g x)
  le_sup_right f g x := le_max_right (f x) (g x)
  sup_le f₁ f₂ f₃ h₁ h₂ x := max_le (h₁ x) (h₂ x)
  inf f g :=
    { toFun := fun x => min (f x) (g x)
      monotone' := fun x y h => min_le_min (f.mono h) (g.mono h)
      map_add_one' := fun x => by simp [min_add_add_right] }
  inf_le_left f g x := min_le_left (f x) (g x)
  inf_le_right f g x := min_le_right (f x) (g x)
  le_inf f₁ f₂ f₃ h₂ h₃ x := le_min (h₂ x) (h₃ x)

#print CircleDeg1Lift.sup_apply /-
@[simp]
theorem sup_apply (x : ℝ) : (f ⊔ g) x = max (f x) (g x) :=
  rfl
#align circle_deg1_lift.sup_apply CircleDeg1Lift.sup_apply
-/

#print CircleDeg1Lift.inf_apply /-
@[simp]
theorem inf_apply (x : ℝ) : (f ⊓ g) x = min (f x) (g x) :=
  rfl
#align circle_deg1_lift.inf_apply CircleDeg1Lift.inf_apply
-/

#print CircleDeg1Lift.iterate_monotone /-
theorem iterate_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f^[n] := fun f g h =>
  f.Monotone.iterate_le_of_le h _
#align circle_deg1_lift.iterate_monotone CircleDeg1Lift.iterate_monotone
-/

#print CircleDeg1Lift.iterate_mono /-
theorem iterate_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  iterate_monotone n h
#align circle_deg1_lift.iterate_mono CircleDeg1Lift.iterate_mono
-/

#print CircleDeg1Lift.pow_mono /-
theorem pow_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f ^ n ≤ g ^ n := fun x => by
  simp only [coe_pow, iterate_mono h n x]
#align circle_deg1_lift.pow_mono CircleDeg1Lift.pow_mono
-/

#print CircleDeg1Lift.pow_monotone /-
theorem pow_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f ^ n := fun f g h => pow_mono h n
#align circle_deg1_lift.pow_monotone CircleDeg1Lift.pow_monotone
-/

/-!
### Estimates on `(f * g) 0`

We prove the estimates `f 0 + ⌊g 0⌋ ≤ f (g 0) ≤ f 0 + ⌈g 0⌉` and some corollaries with added/removed
floors and ceils.

We also prove that for two semiconjugate maps `g₁`, `g₂`, the distance between `g₁ 0` and `g₂ 0`
is less than two.
-/


#print CircleDeg1Lift.map_le_of_map_zero /-
theorem map_le_of_map_zero (x : ℝ) : f x ≤ f 0 + ⌈x⌉ :=
  calc
    f x ≤ f ⌈x⌉ := f.Monotone <| le_ceil _
    _ = f 0 + ⌈x⌉ := f.map_int_of_map_zero _
#align circle_deg1_lift.map_le_of_map_zero CircleDeg1Lift.map_le_of_map_zero
-/

#print CircleDeg1Lift.map_map_zero_le /-
theorem map_map_zero_le : f (g 0) ≤ f 0 + ⌈g 0⌉ :=
  f.map_le_of_map_zero (g 0)
#align circle_deg1_lift.map_map_zero_le CircleDeg1Lift.map_map_zero_le
-/

#print CircleDeg1Lift.floor_map_map_zero_le /-
theorem floor_map_map_zero_le : ⌊f (g 0)⌋ ≤ ⌊f 0⌋ + ⌈g 0⌉ :=
  calc
    ⌊f (g 0)⌋ ≤ ⌊f 0 + ⌈g 0⌉⌋ := floor_mono <| f.map_map_zero_le g
    _ = ⌊f 0⌋ + ⌈g 0⌉ := floor_add_int _ _
#align circle_deg1_lift.floor_map_map_zero_le CircleDeg1Lift.floor_map_map_zero_le
-/

#print CircleDeg1Lift.ceil_map_map_zero_le /-
theorem ceil_map_map_zero_le : ⌈f (g 0)⌉ ≤ ⌈f 0⌉ + ⌈g 0⌉ :=
  calc
    ⌈f (g 0)⌉ ≤ ⌈f 0 + ⌈g 0⌉⌉ := ceil_mono <| f.map_map_zero_le g
    _ = ⌈f 0⌉ + ⌈g 0⌉ := ceil_add_int _ _
#align circle_deg1_lift.ceil_map_map_zero_le CircleDeg1Lift.ceil_map_map_zero_le
-/

#print CircleDeg1Lift.map_map_zero_lt /-
theorem map_map_zero_lt : f (g 0) < f 0 + g 0 + 1 :=
  calc
    f (g 0) ≤ f 0 + ⌈g 0⌉ := f.map_map_zero_le g
    _ < f 0 + (g 0 + 1) := (add_lt_add_left (ceil_lt_add_one _) _)
    _ = f 0 + g 0 + 1 := (add_assoc _ _ _).symm
#align circle_deg1_lift.map_map_zero_lt CircleDeg1Lift.map_map_zero_lt
-/

#print CircleDeg1Lift.le_map_of_map_zero /-
theorem le_map_of_map_zero (x : ℝ) : f 0 + ⌊x⌋ ≤ f x :=
  calc
    f 0 + ⌊x⌋ = f ⌊x⌋ := (f.map_int_of_map_zero _).symm
    _ ≤ f x := f.Monotone <| floor_le _
#align circle_deg1_lift.le_map_of_map_zero CircleDeg1Lift.le_map_of_map_zero
-/

#print CircleDeg1Lift.le_map_map_zero /-
theorem le_map_map_zero : f 0 + ⌊g 0⌋ ≤ f (g 0) :=
  f.le_map_of_map_zero (g 0)
#align circle_deg1_lift.le_map_map_zero CircleDeg1Lift.le_map_map_zero
-/

#print CircleDeg1Lift.le_floor_map_map_zero /-
theorem le_floor_map_map_zero : ⌊f 0⌋ + ⌊g 0⌋ ≤ ⌊f (g 0)⌋ :=
  calc
    ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ := (floor_add_int _ _).symm
    _ ≤ ⌊f (g 0)⌋ := floor_mono <| f.le_map_map_zero g
#align circle_deg1_lift.le_floor_map_map_zero CircleDeg1Lift.le_floor_map_map_zero
-/

#print CircleDeg1Lift.le_ceil_map_map_zero /-
theorem le_ceil_map_map_zero : ⌈f 0⌉ + ⌊g 0⌋ ≤ ⌈(f * g) 0⌉ :=
  calc
    ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ := (ceil_add_int _ _).symm
    _ ≤ ⌈f (g 0)⌉ := ceil_mono <| f.le_map_map_zero g
#align circle_deg1_lift.le_ceil_map_map_zero CircleDeg1Lift.le_ceil_map_map_zero
-/

#print CircleDeg1Lift.lt_map_map_zero /-
theorem lt_map_map_zero : f 0 + g 0 - 1 < f (g 0) :=
  calc
    f 0 + g 0 - 1 = f 0 + (g 0 - 1) := add_sub_assoc _ _ _
    _ < f 0 + ⌊g 0⌋ := (add_lt_add_left (sub_one_lt_floor _) _)
    _ ≤ f (g 0) := f.le_map_map_zero g
#align circle_deg1_lift.lt_map_map_zero CircleDeg1Lift.lt_map_map_zero
-/

#print CircleDeg1Lift.dist_map_map_zero_lt /-
theorem dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1 :=
  by
  rw [dist_comm, Real.dist_eq, abs_lt, lt_sub_iff_add_lt', sub_lt_iff_lt_add', ← sub_eq_add_neg]
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩
#align circle_deg1_lift.dist_map_map_zero_lt CircleDeg1Lift.dist_map_map_zero_lt
-/

#print CircleDeg1Lift.dist_map_zero_lt_of_semiconj /-
theorem dist_map_zero_lt_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semiconj f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  calc
    dist (g₁ 0) (g₂ 0) ≤ dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) := dist_triangle _ _ _
    _ = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) := by
      simp only [h.eq, Real.dist_eq, sub_sub, add_comm (f 0), sub_sub_eq_add_sub,
        abs_sub_comm (g₂ (f 0))]
    _ < 2 := add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)
#align circle_deg1_lift.dist_map_zero_lt_of_semiconj CircleDeg1Lift.dist_map_zero_lt_of_semiconj
-/

#print CircleDeg1Lift.dist_map_zero_lt_of_semiconjBy /-
theorem dist_map_zero_lt_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  dist_map_zero_lt_of_semiconj <| semiconjBy_iff_semiconj.1 h
#align circle_deg1_lift.dist_map_zero_lt_of_semiconj_by CircleDeg1Lift.dist_map_zero_lt_of_semiconjBy
-/

/-!
### Limits at infinities and continuity
-/


#print CircleDeg1Lift.tendsto_atBot /-
protected theorem tendsto_atBot : Tendsto f atBot atBot :=
  tendsto_atBot_mono f.map_le_of_map_zero <|
    tendsto_atBot_add_const_left _ _ <|
      (tendsto_atBot_mono fun x => (ceil_lt_add_one x).le) <|
        tendsto_atBot_add_const_right _ _ tendsto_id
#align circle_deg1_lift.tendsto_at_bot CircleDeg1Lift.tendsto_atBot
-/

#print CircleDeg1Lift.tendsto_atTop /-
protected theorem tendsto_atTop : Tendsto f atTop atTop :=
  tendsto_atTop_mono f.le_map_of_map_zero <|
    tendsto_atTop_add_const_left _ _ <|
      (tendsto_atTop_mono fun x => (sub_one_lt_floor x).le) <| by
        simpa [sub_eq_add_neg] using tendsto_at_top_add_const_right _ _ tendsto_id
#align circle_deg1_lift.tendsto_at_top CircleDeg1Lift.tendsto_atTop
-/

#print CircleDeg1Lift.continuous_iff_surjective /-
theorem continuous_iff_surjective : Continuous f ↔ Function.Surjective f :=
  ⟨fun h => h.Surjective f.tendsto_atTop f.tendsto_atBot, f.Monotone.continuous_of_surjective⟩
#align circle_deg1_lift.continuous_iff_surjective CircleDeg1Lift.continuous_iff_surjective
-/

/-!
### Estimates on `(f^n) x`

If we know that `f x` is `≤`/`<`/`≥`/`>`/`=` to `x + m`, then we have a similar estimate on
`f^[n] x` and `x + n * m`.

For `≤`, `≥`, and `=` we formulate both `of` (implication) and `iff` versions because implications
work for `n = 0`. For `<` and `>` we formulate only `iff` versions.
-/


#print CircleDeg1Lift.iterate_le_of_map_le_add_int /-
theorem iterate_le_of_map_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) (n : ℕ) :
    (f^[n]) x ≤ x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const m) h n
#align circle_deg1_lift.iterate_le_of_map_le_add_int CircleDeg1Lift.iterate_le_of_map_le_add_int
-/

#print CircleDeg1Lift.le_iterate_of_add_int_le_map /-
theorem le_iterate_of_add_int_le_map {x : ℝ} {m : ℤ} (h : x + m ≤ f x) (n : ℕ) :
    x + n * m ≤ (f^[n]) x := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const m) f.monotone h n
#align circle_deg1_lift.le_iterate_of_add_int_le_map CircleDeg1Lift.le_iterate_of_add_int_le_map
-/

#print CircleDeg1Lift.iterate_eq_of_map_eq_add_int /-
theorem iterate_eq_of_map_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) (n : ℕ) :
    (f^[n]) x = x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using (f.commute_add_int m).iterate_eq_of_map_eq n h
#align circle_deg1_lift.iterate_eq_of_map_eq_add_int CircleDeg1Lift.iterate_eq_of_map_eq_add_int
-/

#print CircleDeg1Lift.iterate_pos_le_iff /-
theorem iterate_pos_le_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    (f^[n]) x ≤ x + n * m ↔ f x ≤ x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strict_mono_id.add_const m) hn
#align circle_deg1_lift.iterate_pos_le_iff CircleDeg1Lift.iterate_pos_le_iff
-/

#print CircleDeg1Lift.iterate_pos_lt_iff /-
theorem iterate_pos_lt_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    (f^[n]) x < x + n * m ↔ f x < x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strict_mono_id.add_const m) hn
#align circle_deg1_lift.iterate_pos_lt_iff CircleDeg1Lift.iterate_pos_lt_iff
-/

#print CircleDeg1Lift.iterate_pos_eq_iff /-
theorem iterate_pos_eq_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    (f^[n]) x = x + n * m ↔ f x = x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strict_mono_id.add_const m) hn
#align circle_deg1_lift.iterate_pos_eq_iff CircleDeg1Lift.iterate_pos_eq_iff
-/

#print CircleDeg1Lift.le_iterate_pos_iff /-
theorem le_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    x + n * m ≤ (f^[n]) x ↔ x + m ≤ f x := by
  simpa only [not_lt] using not_congr (f.iterate_pos_lt_iff hn)
#align circle_deg1_lift.le_iterate_pos_iff CircleDeg1Lift.le_iterate_pos_iff
-/

#print CircleDeg1Lift.lt_iterate_pos_iff /-
theorem lt_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    x + n * m < (f^[n]) x ↔ x + m < f x := by
  simpa only [not_le] using not_congr (f.iterate_pos_le_iff hn)
#align circle_deg1_lift.lt_iterate_pos_iff CircleDeg1Lift.lt_iterate_pos_iff
-/

#print CircleDeg1Lift.mul_floor_map_zero_le_floor_iterate_zero /-
theorem mul_floor_map_zero_le_floor_iterate_zero (n : ℕ) : ↑n * ⌊f 0⌋ ≤ ⌊(f^[n]) 0⌋ :=
  by
  rw [le_floor, Int.cast_mul, Int.cast_ofNat, ← zero_add ((n : ℝ) * _)]
  apply le_iterate_of_add_int_le_map
  simp [floor_le]
#align circle_deg1_lift.mul_floor_map_zero_le_floor_iterate_zero CircleDeg1Lift.mul_floor_map_zero_le_floor_iterate_zero
-/

/-!
### Definition of translation number
-/


noncomputable section

#print CircleDeg1Lift.transnumAuxSeq /-
/-- An auxiliary sequence used to define the translation number. -/
def transnumAuxSeq (n : ℕ) : ℝ :=
  (f ^ 2 ^ n) 0 / 2 ^ n
#align circle_deg1_lift.transnum_aux_seq CircleDeg1Lift.transnumAuxSeq
-/

#print CircleDeg1Lift.translationNumber /-
/-- The translation number of a `circle_deg1_lift`, $τ(f)=\lim_{n→∞}\frac{f^n(x)-x}{n}$. We use
an auxiliary sequence `\frac{f^{2^n}(0)}{2^n}` to define `τ(f)` because some proofs are simpler
this way. -/
def translationNumber : ℝ :=
  limUnder atTop f.transnumAuxSeq
#align circle_deg1_lift.translation_number CircleDeg1Lift.translationNumber
-/

-- TODO: choose two different symbols for `circle_deg1_lift.translation_number` and the future
-- `circle_mono_homeo.rotation_number`, then make them `localized notation`s
local notation "τ" => translationNumber

#print CircleDeg1Lift.transnumAuxSeq_def /-
theorem transnumAuxSeq_def : f.transnumAuxSeq = fun n : ℕ => (f ^ 2 ^ n) 0 / 2 ^ n :=
  rfl
#align circle_deg1_lift.transnum_aux_seq_def CircleDeg1Lift.transnumAuxSeq_def
-/

#print CircleDeg1Lift.translationNumber_eq_of_tendsto_aux /-
theorem translationNumber_eq_of_tendsto_aux {τ' : ℝ} (h : Tendsto f.transnumAuxSeq atTop (𝓝 τ')) :
    τ f = τ' :=
  h.limUnder_eq
#align circle_deg1_lift.translation_number_eq_of_tendsto_aux CircleDeg1Lift.translationNumber_eq_of_tendsto_aux
-/

#print CircleDeg1Lift.translationNumber_eq_of_tendsto₀ /-
theorem translationNumber_eq_of_tendsto₀ {τ' : ℝ}
    (h : Tendsto (fun n : ℕ => (f^[n]) 0 / n) atTop (𝓝 τ')) : τ f = τ' :=
  f.translationNumber_eq_of_tendsto_aux <| by
    simpa [(· ∘ ·), transnum_aux_seq_def, coe_pow] using
      h.comp (Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
#align circle_deg1_lift.translation_number_eq_of_tendsto₀ CircleDeg1Lift.translationNumber_eq_of_tendsto₀
-/

#print CircleDeg1Lift.translationNumber_eq_of_tendsto₀' /-
theorem translationNumber_eq_of_tendsto₀' {τ' : ℝ}
    (h : Tendsto (fun n : ℕ => (f^[n + 1]) 0 / (n + 1)) atTop (𝓝 τ')) : τ f = τ' :=
  f.translationNumber_eq_of_tendsto₀ <| (tendsto_add_atTop_iff_nat 1).1 (by exact_mod_cast h)
#align circle_deg1_lift.translation_number_eq_of_tendsto₀' CircleDeg1Lift.translationNumber_eq_of_tendsto₀'
-/

#print CircleDeg1Lift.transnumAuxSeq_zero /-
theorem transnumAuxSeq_zero : f.transnumAuxSeq 0 = f 0 := by simp [transnum_aux_seq]
#align circle_deg1_lift.transnum_aux_seq_zero CircleDeg1Lift.transnumAuxSeq_zero
-/

#print CircleDeg1Lift.transnumAuxSeq_dist_lt /-
theorem transnumAuxSeq_dist_lt (n : ℕ) :
    dist (f.transnumAuxSeq n) (f.transnumAuxSeq (n + 1)) < 1 / 2 / 2 ^ n :=
  by
  have : 0 < (2 ^ (n + 1) : ℝ) := pow_pos zero_lt_two _
  rw [div_div, ← pow_succ, ← abs_of_pos this]
  replace := abs_pos.2 (ne_of_gt this)
  convert (div_lt_div_right this).2 ((f ^ 2 ^ n).dist_map_map_zero_lt (f ^ 2 ^ n))
  simp_rw [transnum_aux_seq, Real.dist_eq]
  rw [← abs_div, sub_div, pow_succ', pow_succ, ← two_mul, mul_div_mul_left _ _ (two_ne_zero' ℝ),
    pow_mul, sq, mul_apply]
#align circle_deg1_lift.transnum_aux_seq_dist_lt CircleDeg1Lift.transnumAuxSeq_dist_lt
-/

#print CircleDeg1Lift.tendsto_translationNumber_aux /-
theorem tendsto_translationNumber_aux : Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f) :=
  (cauchySeq_of_le_geometric_two 1 fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n).tendsto_limUnder
#align circle_deg1_lift.tendsto_translation_number_aux CircleDeg1Lift.tendsto_translationNumber_aux
-/

#print CircleDeg1Lift.dist_map_zero_translationNumber_le /-
theorem dist_map_zero_translationNumber_le : dist (f 0) (τ f) ≤ 1 :=
  f.transnumAuxSeq_zero ▸
    dist_le_of_le_geometric_two_of_tendsto₀ 1 (fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n)
      f.tendsto_translationNumber_aux
#align circle_deg1_lift.dist_map_zero_translation_number_le CircleDeg1Lift.dist_map_zero_translationNumber_le
-/

#print CircleDeg1Lift.tendsto_translationNumber_of_dist_bounded_aux /-
theorem tendsto_translationNumber_of_dist_bounded_aux (x : ℕ → ℝ) (C : ℝ)
    (H : ∀ n : ℕ, dist ((f ^ n) 0) (x n) ≤ C) :
    Tendsto (fun n : ℕ => x (2 ^ n) / 2 ^ n) atTop (𝓝 <| τ f) :=
  by
  refine' f.tendsto_translation_number_aux.congr_dist (squeeze_zero (fun _ => dist_nonneg) _ _)
  · exact fun n => C / 2 ^ n
  · intro n
    have : 0 < (2 ^ n : ℝ) := pow_pos zero_lt_two _
    convert (div_le_div_right this).2 (H (2 ^ n))
    rw [transnum_aux_seq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos this, Real.dist_eq]
  ·
    exact
      MulZeroClass.mul_zero C ▸
        tendsto_const_nhds.mul
          (tendsto_inv_at_top_zero.comp <| tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
#align circle_deg1_lift.tendsto_translation_number_of_dist_bounded_aux CircleDeg1Lift.tendsto_translationNumber_of_dist_bounded_aux
-/

#print CircleDeg1Lift.translationNumber_eq_of_dist_bounded /-
theorem translationNumber_eq_of_dist_bounded {f g : CircleDeg1Lift} (C : ℝ)
    (H : ∀ n : ℕ, dist ((f ^ n) 0) ((g ^ n) 0) ≤ C) : τ f = τ g :=
  Eq.symm <|
    g.translationNumber_eq_of_tendsto_aux <| f.tendsto_translationNumber_of_dist_bounded_aux _ C H
#align circle_deg1_lift.translation_number_eq_of_dist_bounded CircleDeg1Lift.translationNumber_eq_of_dist_bounded
-/

#print CircleDeg1Lift.translationNumber_one /-
@[simp]
theorem translationNumber_one : τ 1 = 0 :=
  translationNumber_eq_of_tendsto₀ _ <| by simp [tendsto_const_nhds]
#align circle_deg1_lift.translation_number_one CircleDeg1Lift.translationNumber_one
-/

#print CircleDeg1Lift.translationNumber_eq_of_semiconjBy /-
theorem translationNumber_eq_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂) :
    τ g₁ = τ g₂ :=
  translationNumber_eq_of_dist_bounded 2 fun n =>
    le_of_lt <| dist_map_zero_lt_of_semiconjBy <| H.pow_right n
#align circle_deg1_lift.translation_number_eq_of_semiconj_by CircleDeg1Lift.translationNumber_eq_of_semiconjBy
-/

#print CircleDeg1Lift.translationNumber_eq_of_semiconj /-
theorem translationNumber_eq_of_semiconj {f g₁ g₂ : CircleDeg1Lift}
    (H : Function.Semiconj f g₁ g₂) : τ g₁ = τ g₂ :=
  translationNumber_eq_of_semiconjBy <| semiconjBy_iff_semiconj.2 H
#align circle_deg1_lift.translation_number_eq_of_semiconj CircleDeg1Lift.translationNumber_eq_of_semiconj
-/

#print CircleDeg1Lift.translationNumber_mul_of_commute /-
theorem translationNumber_mul_of_commute {f g : CircleDeg1Lift} (h : Commute f g) :
    τ (f * g) = τ f + τ g :=
  by
  have :
    tendsto (fun n : ℕ => (fun k => (f ^ k) 0 + (g ^ k) 0) (2 ^ n) / 2 ^ n) at_top
      (𝓝 <| τ f + τ g) :=
    (f.tendsto_translation_number_aux.add g.tendsto_translation_number_aux).congr fun n =>
      (add_div ((f ^ 2 ^ n) 0) ((g ^ 2 ^ n) 0) ((2 : ℝ) ^ n)).symm
  refine'
    tendsto_nhds_unique ((f * g).tendsto_translationNumber_of_dist_bounded_aux _ 1 fun n => _) this
  rw [h.mul_pow, dist_comm]
  exact le_of_lt ((f ^ n).dist_map_map_zero_lt (g ^ n))
#align circle_deg1_lift.translation_number_mul_of_commute CircleDeg1Lift.translationNumber_mul_of_commute
-/

#print CircleDeg1Lift.translationNumber_units_inv /-
@[simp]
theorem translationNumber_units_inv (f : CircleDeg1Liftˣ) : τ ↑f⁻¹ = -τ f :=
  eq_neg_iff_add_eq_zero.2 <| by
    simp [← translation_number_mul_of_commute (Commute.refl _).units_inv_left]
#align circle_deg1_lift.translation_number_units_inv CircleDeg1Lift.translationNumber_units_inv
-/

#print CircleDeg1Lift.translationNumber_pow /-
@[simp]
theorem translationNumber_pow : ∀ n : ℕ, τ (f ^ n) = n * τ f
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ', translation_number_mul_of_commute (Commute.pow_self f n),
      translation_number_pow n, Nat.cast_add_one, add_mul, one_mul]
#align circle_deg1_lift.translation_number_pow CircleDeg1Lift.translationNumber_pow
-/

#print CircleDeg1Lift.translationNumber_zpow /-
@[simp]
theorem translationNumber_zpow (f : CircleDeg1Liftˣ) : ∀ n : ℤ, τ (f ^ n : Units _) = n * τ f
  | (n : ℕ) => by simp [translation_number_pow f n]
  | -[n+1] => by simp; ring
#align circle_deg1_lift.translation_number_zpow CircleDeg1Lift.translationNumber_zpow
-/

#print CircleDeg1Lift.translationNumber_conj_eq /-
@[simp]
theorem translationNumber_conj_eq (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) :
    τ (↑f * g * ↑f⁻¹) = τ g :=
  (translationNumber_eq_of_semiconjBy (f.mk_semiconjBy g)).symm
#align circle_deg1_lift.translation_number_conj_eq CircleDeg1Lift.translationNumber_conj_eq
-/

#print CircleDeg1Lift.translationNumber_conj_eq' /-
@[simp]
theorem translationNumber_conj_eq' (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) :
    τ (↑f⁻¹ * g * f) = τ g :=
  translationNumber_conj_eq f⁻¹ g
#align circle_deg1_lift.translation_number_conj_eq' CircleDeg1Lift.translationNumber_conj_eq'
-/

#print CircleDeg1Lift.dist_pow_map_zero_mul_translationNumber_le /-
theorem dist_pow_map_zero_mul_translationNumber_le (n : ℕ) :
    dist ((f ^ n) 0) (n * f.translationNumber) ≤ 1 :=
  f.translationNumber_pow n ▸ (f ^ n).dist_map_zero_translationNumber_le
#align circle_deg1_lift.dist_pow_map_zero_mul_translation_number_le CircleDeg1Lift.dist_pow_map_zero_mul_translationNumber_le
-/

#print CircleDeg1Lift.tendsto_translation_number₀' /-
theorem tendsto_translation_number₀' :
    Tendsto (fun n : ℕ => (f ^ (n + 1)) 0 / (n + 1)) atTop (𝓝 <| τ f) :=
  by
  refine'
    tendsto_iff_dist_tendsto_zero.2 <|
      squeeze_zero (fun _ => dist_nonneg) (fun n => _)
        ((tendsto_const_div_atTop_nhds_0_nat 1).comp (tendsto_add_at_top_nat 1))
  dsimp
  have : (0 : ℝ) < n + 1 := n.cast_add_one_pos
  rw [Real.dist_eq, div_sub' _ _ _ (ne_of_gt this), abs_div, ← Real.dist_eq, abs_of_pos this,
    Nat.cast_add_one, div_le_div_right this, ← Nat.cast_add_one]
  apply dist_pow_map_zero_mul_translation_number_le
#align circle_deg1_lift.tendsto_translation_number₀' CircleDeg1Lift.tendsto_translation_number₀'
-/

#print CircleDeg1Lift.tendsto_translation_number₀ /-
theorem tendsto_translation_number₀ : Tendsto (fun n : ℕ => (f ^ n) 0 / n) atTop (𝓝 <| τ f) :=
  (tendsto_add_atTop_iff_nat 1).1 (by exact_mod_cast f.tendsto_translation_number₀')
#align circle_deg1_lift.tendsto_translation_number₀ CircleDeg1Lift.tendsto_translation_number₀
-/

#print CircleDeg1Lift.tendsto_translationNumber /-
/-- For any `x : ℝ` the sequence $\frac{f^n(x)-x}{n}$ tends to the translation number of `f`.
In particular, this limit does not depend on `x`. -/
theorem tendsto_translationNumber (x : ℝ) :
    Tendsto (fun n : ℕ => ((f ^ n) x - x) / n) atTop (𝓝 <| τ f) :=
  by
  rw [← translation_number_conj_eq' (translate <| Multiplicative.ofAdd x)]
  convert tendsto_translation_number₀ _
  ext n
  simp [sub_eq_neg_add, Units.conj_pow']
#align circle_deg1_lift.tendsto_translation_number CircleDeg1Lift.tendsto_translationNumber
-/

#print CircleDeg1Lift.tendsto_translation_number' /-
theorem tendsto_translation_number' (x : ℝ) :
    Tendsto (fun n : ℕ => ((f ^ (n + 1)) x - x) / (n + 1)) atTop (𝓝 <| τ f) := by
  exact_mod_cast (tendsto_add_at_top_iff_nat 1).2 (f.tendsto_translation_number x)
#align circle_deg1_lift.tendsto_translation_number' CircleDeg1Lift.tendsto_translation_number'
-/

#print CircleDeg1Lift.translationNumber_mono /-
theorem translationNumber_mono : Monotone τ := fun f g h =>
  le_of_tendsto_of_tendsto' f.tendsto_translation_number₀ g.tendsto_translation_number₀ fun n =>
    div_le_div_of_le_of_nonneg (pow_mono h n 0) n.cast_nonneg
#align circle_deg1_lift.translation_number_mono CircleDeg1Lift.translationNumber_mono
-/

#print CircleDeg1Lift.translationNumber_translate /-
theorem translationNumber_translate (x : ℝ) : τ (translate <| Multiplicative.ofAdd x) = x :=
  translationNumber_eq_of_tendsto₀' _ <| by
    simp [Nat.cast_add_one_ne_zero, mul_div_cancel_left, tendsto_const_nhds]
#align circle_deg1_lift.translation_number_translate CircleDeg1Lift.translationNumber_translate
-/

#print CircleDeg1Lift.translationNumber_le_of_le_add /-
theorem translationNumber_le_of_le_add {z : ℝ} (hz : ∀ x, f x ≤ x + z) : τ f ≤ z :=
  translationNumber_translate z ▸
    translationNumber_mono fun x => trans_rel_left _ (hz x) (add_comm _ _)
#align circle_deg1_lift.translation_number_le_of_le_add CircleDeg1Lift.translationNumber_le_of_le_add
-/

#print CircleDeg1Lift.le_translationNumber_of_add_le /-
theorem le_translationNumber_of_add_le {z : ℝ} (hz : ∀ x, x + z ≤ f x) : z ≤ τ f :=
  translationNumber_translate z ▸
    translationNumber_mono fun x => trans_rel_right _ (add_comm _ _) (hz x)
#align circle_deg1_lift.le_translation_number_of_add_le CircleDeg1Lift.le_translationNumber_of_add_le
-/

#print CircleDeg1Lift.translationNumber_le_of_le_add_int /-
theorem translationNumber_le_of_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) : τ f ≤ m :=
  le_of_tendsto' (f.tendsto_translation_number' x) fun n =>
    (div_le_iff' (n.cast_add_one_pos : (0 : ℝ) < _)).mpr <|
      sub_le_iff_le_add'.2 <|
        (coe_pow f (n + 1)).symm ▸
          @Nat.cast_add_one ℝ _ n ▸ f.iterate_le_of_map_le_add_int h (n + 1)
#align circle_deg1_lift.translation_number_le_of_le_add_int CircleDeg1Lift.translationNumber_le_of_le_add_int
-/

#print CircleDeg1Lift.translationNumber_le_of_le_add_nat /-
theorem translationNumber_le_of_le_add_nat {x : ℝ} {m : ℕ} (h : f x ≤ x + m) : τ f ≤ m :=
  @translationNumber_le_of_le_add_int f x m h
#align circle_deg1_lift.translation_number_le_of_le_add_nat CircleDeg1Lift.translationNumber_le_of_le_add_nat
-/

#print CircleDeg1Lift.le_translationNumber_of_add_int_le /-
theorem le_translationNumber_of_add_int_le {x : ℝ} {m : ℤ} (h : x + m ≤ f x) : ↑m ≤ τ f :=
  ge_of_tendsto' (f.tendsto_translation_number' x) fun n =>
    (le_div_iff (n.cast_add_one_pos : (0 : ℝ) < _)).mpr <|
      le_sub_iff_add_le'.2 <| by
        simp only [coe_pow, mul_comm (m : ℝ), ← Nat.cast_add_one, f.le_iterate_of_add_int_le_map h]
#align circle_deg1_lift.le_translation_number_of_add_int_le CircleDeg1Lift.le_translationNumber_of_add_int_le
-/

#print CircleDeg1Lift.le_translationNumber_of_add_nat_le /-
theorem le_translationNumber_of_add_nat_le {x : ℝ} {m : ℕ} (h : x + m ≤ f x) : ↑m ≤ τ f :=
  @le_translationNumber_of_add_int_le f x m h
#align circle_deg1_lift.le_translation_number_of_add_nat_le CircleDeg1Lift.le_translationNumber_of_add_nat_le
-/

#print CircleDeg1Lift.translationNumber_of_eq_add_int /-
/-- If `f x - x` is an integer number `m` for some point `x`, then `τ f = m`.
On the circle this means that a map with a fixed point has rotation number zero. -/
theorem translationNumber_of_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) : τ f = m :=
  le_antisymm (translationNumber_le_of_le_add_int f <| le_of_eq h)
    (le_translationNumber_of_add_int_le f <| le_of_eq h.symm)
#align circle_deg1_lift.translation_number_of_eq_add_int CircleDeg1Lift.translationNumber_of_eq_add_int
-/

#print CircleDeg1Lift.floor_sub_le_translationNumber /-
theorem floor_sub_le_translationNumber (x : ℝ) : ↑⌊f x - x⌋ ≤ τ f :=
  le_translationNumber_of_add_int_le f <| le_sub_iff_add_le'.1 (floor_le <| f x - x)
#align circle_deg1_lift.floor_sub_le_translation_number CircleDeg1Lift.floor_sub_le_translationNumber
-/

#print CircleDeg1Lift.translationNumber_le_ceil_sub /-
theorem translationNumber_le_ceil_sub (x : ℝ) : τ f ≤ ⌈f x - x⌉ :=
  translationNumber_le_of_le_add_int f <| sub_le_iff_le_add'.1 (le_ceil <| f x - x)
#align circle_deg1_lift.translation_number_le_ceil_sub CircleDeg1Lift.translationNumber_le_ceil_sub
-/

#print CircleDeg1Lift.map_lt_of_translationNumber_lt_int /-
theorem map_lt_of_translationNumber_lt_int {n : ℤ} (h : τ f < n) (x : ℝ) : f x < x + n :=
  not_le.1 <| mt f.le_translationNumber_of_add_int_le <| not_le.2 h
#align circle_deg1_lift.map_lt_of_translation_number_lt_int CircleDeg1Lift.map_lt_of_translationNumber_lt_int
-/

#print CircleDeg1Lift.map_lt_of_translationNumber_lt_nat /-
theorem map_lt_of_translationNumber_lt_nat {n : ℕ} (h : τ f < n) (x : ℝ) : f x < x + n :=
  @map_lt_of_translationNumber_lt_int f n h x
#align circle_deg1_lift.map_lt_of_translation_number_lt_nat CircleDeg1Lift.map_lt_of_translationNumber_lt_nat
-/

#print CircleDeg1Lift.map_lt_add_floor_translationNumber_add_one /-
theorem map_lt_add_floor_translationNumber_add_one (x : ℝ) : f x < x + ⌊τ f⌋ + 1 :=
  by
  rw [add_assoc]
  norm_cast
  refine' map_lt_of_translation_number_lt_int _ _ _
  push_cast
  exact lt_floor_add_one _
#align circle_deg1_lift.map_lt_add_floor_translation_number_add_one CircleDeg1Lift.map_lt_add_floor_translationNumber_add_one
-/

#print CircleDeg1Lift.map_lt_add_translationNumber_add_one /-
theorem map_lt_add_translationNumber_add_one (x : ℝ) : f x < x + τ f + 1 :=
  calc
    f x < x + ⌊τ f⌋ + 1 := f.map_lt_add_floor_translationNumber_add_one x
    _ ≤ x + τ f + 1 := by mono*; exact floor_le (τ f)
#align circle_deg1_lift.map_lt_add_translation_number_add_one CircleDeg1Lift.map_lt_add_translationNumber_add_one
-/

#print CircleDeg1Lift.lt_map_of_int_lt_translationNumber /-
theorem lt_map_of_int_lt_translationNumber {n : ℤ} (h : ↑n < τ f) (x : ℝ) : x + n < f x :=
  not_le.1 <| mt f.translationNumber_le_of_le_add_int <| not_le.2 h
#align circle_deg1_lift.lt_map_of_int_lt_translation_number CircleDeg1Lift.lt_map_of_int_lt_translationNumber
-/

#print CircleDeg1Lift.lt_map_of_nat_lt_translationNumber /-
theorem lt_map_of_nat_lt_translationNumber {n : ℕ} (h : ↑n < τ f) (x : ℝ) : x + n < f x :=
  @lt_map_of_int_lt_translationNumber f n h x
#align circle_deg1_lift.lt_map_of_nat_lt_translation_number CircleDeg1Lift.lt_map_of_nat_lt_translationNumber
-/

#print CircleDeg1Lift.translationNumber_of_map_pow_eq_add_int /-
/-- If `f^n x - x`, `n > 0`, is an integer number `m` for some point `x`, then
`τ f = m / n`. On the circle this means that a map with a periodic orbit has
a rational rotation number. -/
theorem translationNumber_of_map_pow_eq_add_int {x : ℝ} {n : ℕ} {m : ℤ} (h : (f ^ n) x = x + m)
    (hn : 0 < n) : τ f = m / n :=
  by
  have := (f ^ n).translationNumber_of_eq_add_int h
  rwa [translation_number_pow, mul_comm, ← eq_div_iff] at this 
  exact Nat.cast_ne_zero.2 (ne_of_gt hn)
#align circle_deg1_lift.translation_number_of_map_pow_eq_add_int CircleDeg1Lift.translationNumber_of_map_pow_eq_add_int
-/

#print CircleDeg1Lift.forall_map_sub_of_Icc /-
/-- If a predicate depends only on `f x - x` and holds for all `0 ≤ x ≤ 1`,
then it holds for all `x`. -/
theorem forall_map_sub_of_Icc (P : ℝ → Prop) (h : ∀ x ∈ Icc (0 : ℝ) 1, P (f x - x)) (x : ℝ) :
    P (f x - x) :=
  f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩
#align circle_deg1_lift.forall_map_sub_of_Icc CircleDeg1Lift.forall_map_sub_of_Icc
-/

#print CircleDeg1Lift.translationNumber_lt_of_forall_lt_add /-
theorem translationNumber_lt_of_forall_lt_add (hf : Continuous f) {z : ℝ} (hz : ∀ x, f x < x + z) :
    τ f < z :=
  by
  obtain ⟨x, xmem, hx⟩ : ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f y - y ≤ f x - x
  exact
    is_compact_Icc.exists_forall_ge (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).ContinuousOn
  refine' lt_of_le_of_lt _ (sub_lt_iff_lt_add'.2 <| hz x)
  apply translation_number_le_of_le_add
  simp only [← sub_le_iff_le_add']
  exact f.forall_map_sub_of_Icc (fun a => a ≤ f x - x) hx
#align circle_deg1_lift.translation_number_lt_of_forall_lt_add CircleDeg1Lift.translationNumber_lt_of_forall_lt_add
-/

#print CircleDeg1Lift.lt_translationNumber_of_forall_add_lt /-
theorem lt_translationNumber_of_forall_add_lt (hf : Continuous f) {z : ℝ} (hz : ∀ x, x + z < f x) :
    z < τ f :=
  by
  obtain ⟨x, xmem, hx⟩ : ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x - x ≤ f y - y
  exact
    is_compact_Icc.exists_forall_le (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).ContinuousOn
  refine' lt_of_lt_of_le (lt_sub_iff_add_lt'.2 <| hz x) _
  apply le_translation_number_of_add_le
  simp only [← le_sub_iff_add_le']
  exact f.forall_map_sub_of_Icc _ hx
#align circle_deg1_lift.lt_translation_number_of_forall_add_lt CircleDeg1Lift.lt_translationNumber_of_forall_add_lt
-/

#print CircleDeg1Lift.exists_eq_add_translationNumber /-
/-- If `f` is a continuous monotone map `ℝ → ℝ`, `f (x + 1) = f x + 1`, then there exists `x`
such that `f x = x + τ f`. -/
theorem exists_eq_add_translationNumber (hf : Continuous f) : ∃ x, f x = x + τ f :=
  by
  obtain ⟨a, ha⟩ : ∃ x, f x ≤ x + f.translation_number :=
    by
    by_contra! H
    exact lt_irrefl _ (f.lt_translation_number_of_forall_add_lt hf H)
  obtain ⟨b, hb⟩ : ∃ x, x + τ f ≤ f x := by
    by_contra! H
    exact lt_irrefl _ (f.translation_number_lt_of_forall_lt_add hf H)
  exact intermediate_value_univ₂ hf (continuous_id.add continuous_const) ha hb
#align circle_deg1_lift.exists_eq_add_translation_number CircleDeg1Lift.exists_eq_add_translationNumber
-/

#print CircleDeg1Lift.translationNumber_eq_int_iff /-
theorem translationNumber_eq_int_iff (hf : Continuous f) {m : ℤ} : τ f = m ↔ ∃ x, f x = x + m :=
  by
  refine' ⟨fun h => h ▸ f.exists_eq_add_translation_number hf, _⟩
  rintro ⟨x, hx⟩
  exact f.translation_number_of_eq_add_int hx
#align circle_deg1_lift.translation_number_eq_int_iff CircleDeg1Lift.translationNumber_eq_int_iff
-/

#print CircleDeg1Lift.continuous_pow /-
theorem continuous_pow (hf : Continuous f) (n : ℕ) : Continuous ⇑(f ^ n : CircleDeg1Lift) := by
  rw [coe_pow]; exact hf.iterate n
#align circle_deg1_lift.continuous_pow CircleDeg1Lift.continuous_pow
-/

#print CircleDeg1Lift.translationNumber_eq_rat_iff /-
theorem translationNumber_eq_rat_iff (hf : Continuous f) {m : ℤ} {n : ℕ} (hn : 0 < n) :
    τ f = m / n ↔ ∃ x, (f ^ n) x = x + m :=
  by
  rw [eq_div_iff, mul_comm, ← translation_number_pow] <;> [skip; exact ne_of_gt (Nat.cast_pos.2 hn)]
  exact (f ^ n).translationNumber_eq_int_iff (f.continuous_pow hf n)
#align circle_deg1_lift.translation_number_eq_rat_iff CircleDeg1Lift.translationNumber_eq_rat_iff
-/

#print CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq /-
/-- Consider two actions `f₁ f₂ : G →* circle_deg1_lift` of a group on the real line by lifts of
orientation preserving circle homeomorphisms. Suppose that for each `g : G` the homeomorphisms
`f₁ g` and `f₂ g` have equal rotation numbers. Then there exists `F : circle_deg1_lift`  such that
`F * f₁ g = f₂ g * F` for all `g : G`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
theorem semiconj_of_group_action_of_forall_translationNumber_eq {G : Type _} [Group G]
    (f₁ f₂ : G →* CircleDeg1Lift) (h : ∀ g, τ (f₁ g) = τ (f₂ g)) :
    ∃ F : CircleDeg1Lift, ∀ g, Semiconj F (f₁ g) (f₂ g) :=
  by
  -- Equality of translation number guarantees that for each `x`
  -- the set `{f₂ g⁻¹ (f₁ g x) | g : G}` is bounded above.
  have : ∀ x, BddAbove (range fun g => f₂ g⁻¹ (f₁ g x)) :=
    by
    refine' fun x => ⟨x + 2, _⟩
    rintro _ ⟨g, rfl⟩
    have : τ (f₂ g⁻¹) = -τ (f₂ g) := by
      rw [← MonoidHom.coe_toHomUnits, MonoidHom.map_inv, translation_number_units_inv,
        MonoidHom.coe_toHomUnits]
    calc
      f₂ g⁻¹ (f₁ g x) ≤ f₂ g⁻¹ (x + τ (f₁ g) + 1) :=
        mono _ (map_lt_add_translation_number_add_one _ _).le
      _ = f₂ g⁻¹ (x + τ (f₂ g)) + 1 := by rw [h, map_add_one]
      _ ≤ x + τ (f₂ g) + τ (f₂ g⁻¹) + 1 + 1 := by mono;
        exact (map_lt_add_translation_number_add_one _ _).le
      _ = x + 2 := by simp [this, bit0, add_assoc]
  -- We have a theorem about actions by `order_iso`, so we introduce auxiliary maps
  -- to `ℝ ≃o ℝ`.
  set F₁ := to_order_iso.comp f₁.to_hom_units
  set F₂ := to_order_iso.comp f₂.to_hom_units
  have hF₁ : ∀ g, ⇑(F₁ g) = f₁ g := fun _ => rfl
  have hF₂ : ∀ g, ⇑(F₂ g) = f₂ g := fun _ => rfl
  simp only [← hF₁, ← hF₂]
  -- Now we apply `cSup_div_semiconj` and go back to `f₁` and `f₂`.
    refine' ⟨⟨_, fun x y hxy => _, fun x => _⟩, cSup_div_semiconj F₂ F₁ fun x => _⟩ <;>
    simp only [hF₁, hF₂, ← MonoidHom.map_inv, coe_mk]
  · refine' ciSup_mono (this y) fun g => _
    exact mono _ (mono _ hxy)
  · simp only [map_add_one]
    exact
      (Monotone.map_ciSup_of_continuousAt (continuous_at_id.add continuousAt_const)
          (monotone_id.add_const (1 : ℝ)) (this x)).symm
  · exact this x
#align circle_deg1_lift.semiconj_of_group_action_of_forall_translation_number_eq CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq
-/

#print CircleDeg1Lift.units_semiconj_of_translationNumber_eq /-
/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses arguments `f₁ f₂ : circle_deg1_liftˣ`
to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem units_semiconj_of_translationNumber_eq {f₁ f₂ : CircleDeg1Liftˣ} (h : τ f₁ = τ f₂) :
    ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ :=
  haveI :
    ∀ n : Multiplicative ℤ,
      τ ((Units.coeHom _).comp (zpowersHom _ f₁) n) =
        τ ((Units.coeHom _).comp (zpowersHom _ f₂) n) :=
    by intro n; simp [h]
  (semiconj_of_group_action_of_forall_translation_number_eq _ _ this).imp fun F hF =>
    hF (Multiplicative.ofAdd 1)
#align circle_deg1_lift.units_semiconj_of_translation_number_eq CircleDeg1Lift.units_semiconj_of_translationNumber_eq
-/

#print CircleDeg1Lift.semiconj_of_isUnit_of_translationNumber_eq /-
/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses assumptions `is_unit f₁` and `is_unit f₂`
to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem semiconj_of_isUnit_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : IsUnit f₁)
    (h₂ : IsUnit f₂) (h : τ f₁ = τ f₂) : ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ := by
  rcases h₁, h₂ with ⟨⟨f₁, rfl⟩, ⟨f₂, rfl⟩⟩; exact units_semiconj_of_translation_number_eq h
#align circle_deg1_lift.semiconj_of_is_unit_of_translation_number_eq CircleDeg1Lift.semiconj_of_isUnit_of_translationNumber_eq
-/

#print CircleDeg1Lift.semiconj_of_bijective_of_translationNumber_eq /-
/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses assumptions `bijective f₁` and
`bijective f₂` to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem semiconj_of_bijective_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : Bijective f₁)
    (h₂ : Bijective f₂) (h : τ f₁ = τ f₂) : ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ :=
  semiconj_of_isUnit_of_translationNumber_eq (isUnit_iff_bijective.2 h₁) (isUnit_iff_bijective.2 h₂)
    h
#align circle_deg1_lift.semiconj_of_bijective_of_translation_number_eq CircleDeg1Lift.semiconj_of_bijective_of_translationNumber_eq
-/

end CircleDeg1Lift

