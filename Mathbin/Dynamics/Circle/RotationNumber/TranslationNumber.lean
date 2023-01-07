/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module dynamics.circle.rotation_number.translation_number
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Analysis.SpecificLimits.Basic
import Mathbin.Order.Iterate
import Mathbin.Order.SemiconjSup
import Mathbin.Topology.Algebra.Order.MonotoneContinuity

/-!
# Translation number of a monotone real map that commutes with `x ↦ x + 1`

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

open TopologicalSpace Classical

/-!
### Definition and monoid structure
-/


/-- A lift of a monotone degree one map `S¹ → S¹`. -/
structure CircleDeg1Lift : Type where
  toFun : ℝ → ℝ
  monotone' : Monotone to_fun
  map_add_one' : ∀ x, to_fun (x + 1) = to_fun x + 1
#align circle_deg1_lift CircleDeg1Lift

namespace CircleDeg1Lift

instance : CoeFun CircleDeg1Lift fun _ => ℝ → ℝ :=
  ⟨CircleDeg1Lift.toFun⟩

@[simp]
theorem coe_mk (f h₁ h₂) : ⇑(mk f h₁ h₂) = f :=
  rfl
#align circle_deg1_lift.coe_mk CircleDeg1Lift.coe_mk

variable (f g : CircleDeg1Lift)

protected theorem monotone : Monotone f :=
  f.monotone'
#align circle_deg1_lift.monotone CircleDeg1Lift.monotone

@[mono]
theorem mono {x y} (h : x ≤ y) : f x ≤ f y :=
  f.Monotone h
#align circle_deg1_lift.mono CircleDeg1Lift.mono

theorem strict_mono_iff_injective : StrictMono f ↔ Injective f :=
  f.Monotone.strict_mono_iff_injective
#align circle_deg1_lift.strict_mono_iff_injective CircleDeg1Lift.strict_mono_iff_injective

@[simp]
theorem map_add_one : ∀ x, f (x + 1) = f x + 1 :=
  f.map_add_one'
#align circle_deg1_lift.map_add_one CircleDeg1Lift.map_add_one

@[simp]
theorem map_one_add (x : ℝ) : f (1 + x) = 1 + f x := by rw [add_comm, map_add_one, add_comm]
#align circle_deg1_lift.map_one_add CircleDeg1Lift.map_one_add

theorem coe_inj : ∀ ⦃f g : CircleDeg1Lift⦄, (f : ℝ → ℝ) = g → f = g :=
  fun ⟨f, fm, fd⟩ ⟨g, gm, gd⟩ h => by congr <;> exact h
#align circle_deg1_lift.coe_inj CircleDeg1Lift.coe_inj

@[ext]
theorem ext ⦃f g : CircleDeg1Lift⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_inj <| funext h
#align circle_deg1_lift.ext CircleDeg1Lift.ext

theorem ext_iff {f g : CircleDeg1Lift} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩
#align circle_deg1_lift.ext_iff CircleDeg1Lift.ext_iff

instance : Monoid CircleDeg1Lift
    where
  mul f g :=
    { toFun := f ∘ g
      monotone' := f.Monotone.comp g.Monotone
      map_add_one' := fun x => by simp [map_add_one] }
  one := ⟨id, monotone_id, fun _ => rfl⟩
  mul_one f := coe_inj <| Function.comp.right_id f
  one_mul f := coe_inj <| Function.comp.left_id f
  mul_assoc f₁ f₂ f₃ := coe_inj rfl

instance : Inhabited CircleDeg1Lift :=
  ⟨1⟩

@[simp]
theorem coe_mul : ⇑(f * g) = f ∘ g :=
  rfl
#align circle_deg1_lift.coe_mul CircleDeg1Lift.coe_mul

theorem mul_apply (x) : (f * g) x = f (g x) :=
  rfl
#align circle_deg1_lift.mul_apply CircleDeg1Lift.mul_apply

@[simp]
theorem coe_one : ⇑(1 : CircleDeg1Lift) = id :=
  rfl
#align circle_deg1_lift.coe_one CircleDeg1Lift.coe_one

instance unitsHasCoeToFun : CoeFun CircleDeg1Liftˣ fun _ => ℝ → ℝ :=
  ⟨fun f => ⇑(f : CircleDeg1Lift)⟩
#align circle_deg1_lift.units_has_coe_to_fun CircleDeg1Lift.unitsHasCoeToFun

@[simp, norm_cast]
theorem units_coe (f : CircleDeg1Liftˣ) : ⇑(f : CircleDeg1Lift) = f :=
  rfl
#align circle_deg1_lift.units_coe CircleDeg1Lift.units_coe

@[simp]
theorem units_inv_apply_apply (f : CircleDeg1Liftˣ) (x : ℝ) : (f⁻¹ : CircleDeg1Liftˣ) (f x) = x :=
  by simp only [← units_coe, ← mul_apply, f.inv_mul, coe_one, id]
#align circle_deg1_lift.units_inv_apply_apply CircleDeg1Lift.units_inv_apply_apply

@[simp]
theorem units_apply_inv_apply (f : CircleDeg1Liftˣ) (x : ℝ) : f ((f⁻¹ : CircleDeg1Liftˣ) x) = x :=
  by simp only [← units_coe, ← mul_apply, f.mul_inv, coe_one, id]
#align circle_deg1_lift.units_apply_inv_apply CircleDeg1Lift.units_apply_inv_apply

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

@[simp]
theorem coe_to_order_iso (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f) = f :=
  rfl
#align circle_deg1_lift.coe_to_order_iso CircleDeg1Lift.coe_to_order_iso

@[simp]
theorem coe_to_order_iso_symm (f : CircleDeg1Liftˣ) :
    ⇑(toOrderIso f).symm = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl
#align circle_deg1_lift.coe_to_order_iso_symm CircleDeg1Lift.coe_to_order_iso_symm

@[simp]
theorem coe_to_order_iso_inv (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f)⁻¹ = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl
#align circle_deg1_lift.coe_to_order_iso_inv CircleDeg1Lift.coe_to_order_iso_inv

theorem is_unit_iff_bijective {f : CircleDeg1Lift} : IsUnit f ↔ Bijective f :=
  ⟨fun ⟨u, h⟩ => h ▸ (toOrderIso u).Bijective, fun h =>
    Units.isUnit
      { val := f
        inv :=
          { toFun := (Equiv.ofBijective f h).symm
            monotone' := fun x y hxy =>
              (f.strict_mono_iff_injective.2 h.1).le_iff_le.1
                (by simp only [Equiv.ofBijective_apply_symm_apply f h, hxy])
            map_add_one' := fun x =>
              h.1 <| by simp only [Equiv.ofBijective_apply_symm_apply f, f.map_add_one] }
        val_inv := ext <| Equiv.ofBijective_apply_symm_apply f h
        inv_val := ext <| Equiv.ofBijective_symm_apply_apply f h }⟩
#align circle_deg1_lift.is_unit_iff_bijective CircleDeg1Lift.is_unit_iff_bijective

theorem coe_pow : ∀ n : ℕ, ⇑(f ^ n) = f^[n]
  | 0 => rfl
  | n + 1 => by
    ext x
    simp [coe_pow n, pow_succ']
#align circle_deg1_lift.coe_pow CircleDeg1Lift.coe_pow

theorem semiconj_by_iff_semiconj {f g₁ g₂ : CircleDeg1Lift} :
    SemiconjBy f g₁ g₂ ↔ Semiconj f g₁ g₂ :=
  ext_iff
#align circle_deg1_lift.semiconj_by_iff_semiconj CircleDeg1Lift.semiconj_by_iff_semiconj

theorem commute_iff_commute {f g : CircleDeg1Lift} : Commute f g ↔ Function.Commute f g :=
  ext_iff
#align circle_deg1_lift.commute_iff_commute CircleDeg1Lift.commute_iff_commute

/-!
### Translate by a constant
-/


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

@[simp]
theorem translate_apply (x y : ℝ) : translate (Multiplicative.ofAdd x) y = x + y :=
  rfl
#align circle_deg1_lift.translate_apply CircleDeg1Lift.translate_apply

@[simp]
theorem translate_inv_apply (x y : ℝ) : (translate <| Multiplicative.ofAdd x)⁻¹ y = -x + y :=
  rfl
#align circle_deg1_lift.translate_inv_apply CircleDeg1Lift.translate_inv_apply

@[simp]
theorem translate_zpow (x : ℝ) (n : ℤ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) := by
  simp only [← zsmul_eq_mul, ofAdd_zsmul, MonoidHom.map_zpow]
#align circle_deg1_lift.translate_zpow CircleDeg1Lift.translate_zpow

@[simp]
theorem translate_pow (x : ℝ) (n : ℕ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) :=
  translate_zpow x n
#align circle_deg1_lift.translate_pow CircleDeg1Lift.translate_pow

@[simp]
theorem translate_iterate (x : ℝ) (n : ℕ) :
    translate (Multiplicative.ofAdd x)^[n] = translate (Multiplicative.ofAdd <| ↑n * x) := by
  rw [← units_coe, ← coe_pow, ← Units.val_pow_eq_pow_val, translate_pow, units_coe]
#align circle_deg1_lift.translate_iterate CircleDeg1Lift.translate_iterate

/-!
### Commutativity with integer translations

In this section we prove that `f` commutes with translations by an integer number.
First we formulate these statements (for a natural or an integer number,
addition on the left or on the right, addition or subtraction) using `function.commute`,
then reformulate as `simp` lemmas `map_int_add` etc.
-/


theorem commute_nat_add (n : ℕ) : Function.Commute f ((· + ·) n) := by
  simpa only [nsmul_one, add_left_iterate] using Function.Commute.iterate_right f.map_one_add n
#align circle_deg1_lift.commute_nat_add CircleDeg1Lift.commute_nat_add

theorem commute_add_nat (n : ℕ) : Function.Commute f fun x => x + n := by
  simp only [add_comm _ (n : ℝ), f.commute_nat_add n]
#align circle_deg1_lift.commute_add_nat CircleDeg1Lift.commute_add_nat

theorem commute_sub_nat (n : ℕ) : Function.Commute f fun x => x - n := by
  simpa only [sub_eq_add_neg] using
    (f.commute_add_nat n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv
#align circle_deg1_lift.commute_sub_nat CircleDeg1Lift.commute_sub_nat

theorem commute_add_int : ∀ n : ℤ, Function.Commute f fun x => x + n
  | (n : ℕ) => f.commute_add_nat n
  | -[n+1] => by simpa [sub_eq_add_neg] using f.commute_sub_nat (n + 1)
#align circle_deg1_lift.commute_add_int CircleDeg1Lift.commute_add_int

theorem commute_int_add (n : ℤ) : Function.Commute f ((· + ·) n) := by
  simpa only [add_comm _ (n : ℝ)] using f.commute_add_int n
#align circle_deg1_lift.commute_int_add CircleDeg1Lift.commute_int_add

theorem commute_sub_int (n : ℤ) : Function.Commute f fun x => x - n := by
  simpa only [sub_eq_add_neg] using
    (f.commute_add_int n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv
#align circle_deg1_lift.commute_sub_int CircleDeg1Lift.commute_sub_int

@[simp]
theorem map_int_add (m : ℤ) (x : ℝ) : f (m + x) = m + f x :=
  f.commute_int_add m x
#align circle_deg1_lift.map_int_add CircleDeg1Lift.map_int_add

@[simp]
theorem map_add_int (x : ℝ) (m : ℤ) : f (x + m) = f x + m :=
  f.commute_add_int m x
#align circle_deg1_lift.map_add_int CircleDeg1Lift.map_add_int

@[simp]
theorem map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
  f.commute_sub_int n x
#align circle_deg1_lift.map_sub_int CircleDeg1Lift.map_sub_int

@[simp]
theorem map_add_nat (x : ℝ) (n : ℕ) : f (x + n) = f x + n :=
  f.map_add_int x n
#align circle_deg1_lift.map_add_nat CircleDeg1Lift.map_add_nat

@[simp]
theorem map_nat_add (n : ℕ) (x : ℝ) : f (n + x) = n + f x :=
  f.map_int_add n x
#align circle_deg1_lift.map_nat_add CircleDeg1Lift.map_nat_add

@[simp]
theorem map_sub_nat (x : ℝ) (n : ℕ) : f (x - n) = f x - n :=
  f.map_sub_int x n
#align circle_deg1_lift.map_sub_nat CircleDeg1Lift.map_sub_nat

theorem map_int_of_map_zero (n : ℤ) : f n = f 0 + n := by rw [← f.map_add_int, zero_add]
#align circle_deg1_lift.map_int_of_map_zero CircleDeg1Lift.map_int_of_map_zero

@[simp]
theorem map_fract_sub_fract_eq (x : ℝ) : f (fract x) - fract x = f x - x := by
  rw [Int.fract, f.map_sub_int, sub_sub_sub_cancel_right]
#align circle_deg1_lift.map_fract_sub_fract_eq CircleDeg1Lift.map_fract_sub_fract_eq

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

@[simp]
theorem sup_apply (x : ℝ) : (f ⊔ g) x = max (f x) (g x) :=
  rfl
#align circle_deg1_lift.sup_apply CircleDeg1Lift.sup_apply

@[simp]
theorem inf_apply (x : ℝ) : (f ⊓ g) x = min (f x) (g x) :=
  rfl
#align circle_deg1_lift.inf_apply CircleDeg1Lift.inf_apply

theorem iterate_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f^[n] := fun f g h =>
  f.Monotone.iterate_le_of_le h _
#align circle_deg1_lift.iterate_monotone CircleDeg1Lift.iterate_monotone

theorem iterate_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  iterate_monotone n h
#align circle_deg1_lift.iterate_mono CircleDeg1Lift.iterate_mono

theorem pow_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f ^ n ≤ g ^ n := fun x => by
  simp only [coe_pow, iterate_mono h n x]
#align circle_deg1_lift.pow_mono CircleDeg1Lift.pow_mono

theorem pow_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f ^ n := fun f g h => pow_mono h n
#align circle_deg1_lift.pow_monotone CircleDeg1Lift.pow_monotone

/-!
### Estimates on `(f * g) 0`

We prove the estimates `f 0 + ⌊g 0⌋ ≤ f (g 0) ≤ f 0 + ⌈g 0⌉` and some corollaries with added/removed
floors and ceils.

We also prove that for two semiconjugate maps `g₁`, `g₂`, the distance between `g₁ 0` and `g₂ 0`
is less than two.
-/


theorem map_le_of_map_zero (x : ℝ) : f x ≤ f 0 + ⌈x⌉ :=
  calc
    f x ≤ f ⌈x⌉ := f.Monotone <| le_ceil _
    _ = f 0 + ⌈x⌉ := f.map_int_of_map_zero _
    
#align circle_deg1_lift.map_le_of_map_zero CircleDeg1Lift.map_le_of_map_zero

theorem map_map_zero_le : f (g 0) ≤ f 0 + ⌈g 0⌉ :=
  f.map_le_of_map_zero (g 0)
#align circle_deg1_lift.map_map_zero_le CircleDeg1Lift.map_map_zero_le

theorem floor_map_map_zero_le : ⌊f (g 0)⌋ ≤ ⌊f 0⌋ + ⌈g 0⌉ :=
  calc
    ⌊f (g 0)⌋ ≤ ⌊f 0 + ⌈g 0⌉⌋ := floor_mono <| f.map_map_zero_le g
    _ = ⌊f 0⌋ + ⌈g 0⌉ := floor_add_int _ _
    
#align circle_deg1_lift.floor_map_map_zero_le CircleDeg1Lift.floor_map_map_zero_le

theorem ceil_map_map_zero_le : ⌈f (g 0)⌉ ≤ ⌈f 0⌉ + ⌈g 0⌉ :=
  calc
    ⌈f (g 0)⌉ ≤ ⌈f 0 + ⌈g 0⌉⌉ := ceil_mono <| f.map_map_zero_le g
    _ = ⌈f 0⌉ + ⌈g 0⌉ := ceil_add_int _ _
    
#align circle_deg1_lift.ceil_map_map_zero_le CircleDeg1Lift.ceil_map_map_zero_le

theorem map_map_zero_lt : f (g 0) < f 0 + g 0 + 1 :=
  calc
    f (g 0) ≤ f 0 + ⌈g 0⌉ := f.map_map_zero_le g
    _ < f 0 + (g 0 + 1) := add_lt_add_left (ceil_lt_add_one _) _
    _ = f 0 + g 0 + 1 := (add_assoc _ _ _).symm
    
#align circle_deg1_lift.map_map_zero_lt CircleDeg1Lift.map_map_zero_lt

theorem le_map_of_map_zero (x : ℝ) : f 0 + ⌊x⌋ ≤ f x :=
  calc
    f 0 + ⌊x⌋ = f ⌊x⌋ := (f.map_int_of_map_zero _).symm
    _ ≤ f x := f.Monotone <| floor_le _
    
#align circle_deg1_lift.le_map_of_map_zero CircleDeg1Lift.le_map_of_map_zero

theorem le_map_map_zero : f 0 + ⌊g 0⌋ ≤ f (g 0) :=
  f.le_map_of_map_zero (g 0)
#align circle_deg1_lift.le_map_map_zero CircleDeg1Lift.le_map_map_zero

theorem le_floor_map_map_zero : ⌊f 0⌋ + ⌊g 0⌋ ≤ ⌊f (g 0)⌋ :=
  calc
    ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ := (floor_add_int _ _).symm
    _ ≤ ⌊f (g 0)⌋ := floor_mono <| f.le_map_map_zero g
    
#align circle_deg1_lift.le_floor_map_map_zero CircleDeg1Lift.le_floor_map_map_zero

theorem le_ceil_map_map_zero : ⌈f 0⌉ + ⌊g 0⌋ ≤ ⌈(f * g) 0⌉ :=
  calc
    ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ := (ceil_add_int _ _).symm
    _ ≤ ⌈f (g 0)⌉ := ceil_mono <| f.le_map_map_zero g
    
#align circle_deg1_lift.le_ceil_map_map_zero CircleDeg1Lift.le_ceil_map_map_zero

theorem lt_map_map_zero : f 0 + g 0 - 1 < f (g 0) :=
  calc
    f 0 + g 0 - 1 = f 0 + (g 0 - 1) := add_sub_assoc _ _ _
    _ < f 0 + ⌊g 0⌋ := add_lt_add_left (sub_one_lt_floor _) _
    _ ≤ f (g 0) := f.le_map_map_zero g
    
#align circle_deg1_lift.lt_map_map_zero CircleDeg1Lift.lt_map_map_zero

theorem dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1 :=
  by
  rw [dist_comm, Real.dist_eq, abs_lt, lt_sub_iff_add_lt', sub_lt_iff_lt_add', ← sub_eq_add_neg]
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩
#align circle_deg1_lift.dist_map_map_zero_lt CircleDeg1Lift.dist_map_map_zero_lt

theorem dist_map_zero_lt_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semiconj f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  calc
    dist (g₁ 0) (g₂ 0) ≤ dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) := dist_triangle _ _ _
    _ = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) := by
      simp only [h.eq, Real.dist_eq, sub_sub, add_comm (f 0), sub_sub_eq_add_sub,
        abs_sub_comm (g₂ (f 0))]
    _ < 2 := add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)
    
#align circle_deg1_lift.dist_map_zero_lt_of_semiconj CircleDeg1Lift.dist_map_zero_lt_of_semiconj

theorem dist_map_zero_lt_of_semiconj_by {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  dist_map_zero_lt_of_semiconj <| semiconj_by_iff_semiconj.1 h
#align
  circle_deg1_lift.dist_map_zero_lt_of_semiconj_by CircleDeg1Lift.dist_map_zero_lt_of_semiconj_by

/-!
### Limits at infinities and continuity
-/


protected theorem tendsto_at_bot : Tendsto f atBot atBot :=
  tendsto_at_bot_mono f.map_le_of_map_zero <|
    tendsto_at_bot_add_const_left _ _ <|
      (tendsto_at_bot_mono fun x => (ceil_lt_add_one x).le) <|
        tendsto_at_bot_add_const_right _ _ tendsto_id
#align circle_deg1_lift.tendsto_at_bot CircleDeg1Lift.tendsto_at_bot

protected theorem tendsto_at_top : Tendsto f atTop atTop :=
  tendsto_at_top_mono f.le_map_of_map_zero <|
    tendsto_at_top_add_const_left _ _ <|
      (tendsto_at_top_mono fun x => (sub_one_lt_floor x).le) <| by
        simpa [sub_eq_add_neg] using tendsto_at_top_add_const_right _ _ tendsto_id
#align circle_deg1_lift.tendsto_at_top CircleDeg1Lift.tendsto_at_top

theorem continuous_iff_surjective : Continuous f ↔ Function.Surjective f :=
  ⟨fun h => h.Surjective f.tendsto_at_top f.tendsto_at_bot, f.Monotone.continuous_of_surjective⟩
#align circle_deg1_lift.continuous_iff_surjective CircleDeg1Lift.continuous_iff_surjective

/-!
### Estimates on `(f^n) x`

If we know that `f x` is `≤`/`<`/`≥`/`>`/`=` to `x + m`, then we have a similar estimate on
`f^[n] x` and `x + n * m`.

For `≤`, `≥`, and `=` we formulate both `of` (implication) and `iff` versions because implications
work for `n = 0`. For `<` and `>` we formulate only `iff` versions.
-/


theorem iterate_le_of_map_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) (n : ℕ) :
    (f^[n]) x ≤ x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const m) h n
#align circle_deg1_lift.iterate_le_of_map_le_add_int CircleDeg1Lift.iterate_le_of_map_le_add_int

theorem le_iterate_of_add_int_le_map {x : ℝ} {m : ℤ} (h : x + m ≤ f x) (n : ℕ) :
    x + n * m ≤ (f^[n]) x := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const m) f.monotone h n
#align circle_deg1_lift.le_iterate_of_add_int_le_map CircleDeg1Lift.le_iterate_of_add_int_le_map

theorem iterate_eq_of_map_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) (n : ℕ) :
    (f^[n]) x = x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using (f.commute_add_int m).iterate_eq_of_map_eq n h
#align circle_deg1_lift.iterate_eq_of_map_eq_add_int CircleDeg1Lift.iterate_eq_of_map_eq_add_int

theorem iterate_pos_le_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    (f^[n]) x ≤ x + n * m ↔ f x ≤ x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strict_mono_id.add_const m) hn
#align circle_deg1_lift.iterate_pos_le_iff CircleDeg1Lift.iterate_pos_le_iff

theorem iterate_pos_lt_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    (f^[n]) x < x + n * m ↔ f x < x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strict_mono_id.add_const m) hn
#align circle_deg1_lift.iterate_pos_lt_iff CircleDeg1Lift.iterate_pos_lt_iff

theorem iterate_pos_eq_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    (f^[n]) x = x + n * m ↔ f x = x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strict_mono_id.add_const m) hn
#align circle_deg1_lift.iterate_pos_eq_iff CircleDeg1Lift.iterate_pos_eq_iff

theorem le_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    x + n * m ≤ (f^[n]) x ↔ x + m ≤ f x := by
  simpa only [not_lt] using not_congr (f.iterate_pos_lt_iff hn)
#align circle_deg1_lift.le_iterate_pos_iff CircleDeg1Lift.le_iterate_pos_iff

theorem lt_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    x + n * m < (f^[n]) x ↔ x + m < f x := by
  simpa only [not_le] using not_congr (f.iterate_pos_le_iff hn)
#align circle_deg1_lift.lt_iterate_pos_iff CircleDeg1Lift.lt_iterate_pos_iff

theorem mul_floor_map_zero_le_floor_iterate_zero (n : ℕ) : ↑n * ⌊f 0⌋ ≤ ⌊(f^[n]) 0⌋ :=
  by
  rw [le_floor, Int.cast_mul, Int.cast_ofNat, ← zero_add ((n : ℝ) * _)]
  apply le_iterate_of_add_int_le_map
  simp [floor_le]
#align
  circle_deg1_lift.mul_floor_map_zero_le_floor_iterate_zero CircleDeg1Lift.mul_floor_map_zero_le_floor_iterate_zero

/-!
### Definition of translation number
-/


noncomputable section

/-- An auxiliary sequence used to define the translation number. -/
def transnumAuxSeq (n : ℕ) : ℝ :=
  (f ^ 2 ^ n) 0 / 2 ^ n
#align circle_deg1_lift.transnum_aux_seq CircleDeg1Lift.transnumAuxSeq

/-- The translation number of a `circle_deg1_lift`, $τ(f)=\lim_{n→∞}\frac{f^n(x)-x}{n}$. We use
an auxiliary sequence `\frac{f^{2^n}(0)}{2^n}` to define `τ(f)` because some proofs are simpler
this way. -/
def translationNumber : ℝ :=
  lim atTop f.transnumAuxSeq
#align circle_deg1_lift.translation_number CircleDeg1Lift.translationNumber

-- mathport name: exprτ
-- TODO: choose two different symbols for `circle_deg1_lift.translation_number` and the future
-- `circle_mono_homeo.rotation_number`, then make them `localized notation`s
local notation "τ" => translationNumber

theorem transnum_aux_seq_def : f.transnumAuxSeq = fun n : ℕ => (f ^ 2 ^ n) 0 / 2 ^ n :=
  rfl
#align circle_deg1_lift.transnum_aux_seq_def CircleDeg1Lift.transnum_aux_seq_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_eq_of_tendsto_aux [])
      (Command.declSig
       [(Term.implicitBinder "{" [`τ'] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.app
           `Tendsto
           [(Term.proj `f "." `transnumAuxSeq)
            `atTop
            (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`τ'])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "="
         `τ')))
      (Command.declValSimple ":=" (Term.proj `h "." `lim_eq) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h "." `lim_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "="
       `τ')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `τ'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_eq_of_tendsto_aux
  { τ' : ℝ } ( h : Tendsto f . transnumAuxSeq atTop 𝓝 τ' ) : τ f = τ'
  := h . lim_eq
#align
  circle_deg1_lift.translation_number_eq_of_tendsto_aux CircleDeg1Lift.translation_number_eq_of_tendsto_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_eq_of_tendsto₀ [])
      (Command.declSig
       [(Term.implicitBinder "{" [`τ'] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.app
           `Tendsto
           [(Term.fun
             "fun"
             (Term.basicFun
              [`n]
              [(Term.typeSpec ":" (termℕ "ℕ"))]
              "=>"
              («term_/_»
               (Term.app (Nat.Init.Data.Nat.Lemmas.«term_^[_]» `f "^[" `n "]") [(num "0")])
               "/"
               `n)))
            `atTop
            (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`τ'])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "="
         `τ')))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `f "." `translation_number_eq_of_tendsto_aux)
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma
                  []
                  []
                  (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
                 ","
                 (Tactic.simpLemma [] [] `transnum_aux_seq_def)
                 ","
                 (Tactic.simpLemma [] [] `coe_pow)]
                "]")]
              ["using"
               (Term.app
                `h.comp
                [(Term.app `Nat.tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two])])]))]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `f "." `translation_number_eq_of_tendsto_aux)
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma
                 []
                 []
                 (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
                ","
                (Tactic.simpLemma [] [] `transnum_aux_seq_def)
                ","
                (Tactic.simpLemma [] [] `coe_pow)]
               "]")]
             ["using"
              (Term.app
               `h.comp
               [(Term.app `Nat.tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two])])]))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma
                []
                []
                (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
               ","
               (Tactic.simpLemma [] [] `transnum_aux_seq_def)
               ","
               (Tactic.simpLemma [] [] `coe_pow)]
              "]")]
            ["using"
             (Term.app
              `h.comp
              [(Term.app `Nat.tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma
            []
            []
            (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
           ","
           (Tactic.simpLemma [] [] `transnum_aux_seq_def)
           ","
           (Tactic.simpLemma [] [] `coe_pow)]
          "]")]
        ["using"
         (Term.app `h.comp [(Term.app `Nat.tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h.comp [(Term.app `Nat.tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_lt_two
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.tendsto_pow_at_top_at_top_of_one_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Nat.tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `transnum_aux_seq_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `f "." `translation_number_eq_of_tendsto_aux)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "="
       `τ')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `τ'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_eq_of_tendsto₀
  { τ' : ℝ } ( h : Tendsto fun n : ℕ => f ^[ n ] 0 / n atTop 𝓝 τ' ) : τ f = τ'
  :=
    f . translation_number_eq_of_tendsto_aux
      <|
      by
        simpa
          [ ( · ∘ · ) , transnum_aux_seq_def , coe_pow ]
            using h.comp Nat.tendsto_pow_at_top_at_top_of_one_lt one_lt_two
#align
  circle_deg1_lift.translation_number_eq_of_tendsto₀ CircleDeg1Lift.translation_number_eq_of_tendsto₀

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_eq_of_tendsto₀' [])
      (Command.declSig
       [(Term.implicitBinder "{" [`τ'] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.app
           `Tendsto
           [(Term.fun
             "fun"
             (Term.basicFun
              [`n]
              [(Term.typeSpec ":" (termℕ "ℕ"))]
              "=>"
              («term_/_»
               (Term.app
                (Nat.Init.Data.Nat.Lemmas.«term_^[_]» `f "^[" («term_+_» `n "+" (num "1")) "]")
                [(num "0")])
               "/"
               («term_+_» `n "+" (num "1")))))
            `atTop
            (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`τ'])])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "="
         `τ')))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `f "." `translation_number_eq_of_tendsto₀)
        "<|"
        (Term.app
         (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "1"))
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)])))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `f "." `translation_number_eq_of_tendsto₀)
       "<|"
       (Term.app
        (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "1"))
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "1"))
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tendsto_add_at_top_iff_nat [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_add_at_top_iff_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tendsto_add_at_top_iff_nat [(num "1")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `f "." `translation_number_eq_of_tendsto₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "="
       `τ')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `τ'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_eq_of_tendsto₀'
  { τ' : ℝ } ( h : Tendsto fun n : ℕ => f ^[ n + 1 ] 0 / n + 1 atTop 𝓝 τ' ) : τ f = τ'
  := f . translation_number_eq_of_tendsto₀ <| tendsto_add_at_top_iff_nat 1 . 1 by exact_mod_cast h
#align
  circle_deg1_lift.translation_number_eq_of_tendsto₀' CircleDeg1Lift.translation_number_eq_of_tendsto₀'

theorem transnum_aux_seq_zero : f.transnumAuxSeq 0 = f 0 := by simp [transnum_aux_seq]
#align circle_deg1_lift.transnum_aux_seq_zero CircleDeg1Lift.transnum_aux_seq_zero

theorem transnum_aux_seq_dist_lt (n : ℕ) :
    dist (f.transnumAuxSeq n) (f.transnumAuxSeq (n + 1)) < 1 / 2 / 2 ^ n :=
  by
  have : 0 < (2 ^ (n + 1) : ℝ) := pow_pos zero_lt_two _
  rw [div_div, ← pow_succ, ← abs_of_pos this]
  replace := abs_pos.2 (ne_of_gt this)
  convert (div_lt_div_right this).2 ((f ^ 2 ^ n).dist_map_map_zero_lt (f ^ 2 ^ n))
  simp_rw [transnum_aux_seq, Real.dist_eq]
  rw [← abs_div, sub_div, pow_succ', pow_succ, ← two_mul, mul_div_mul_left _ _ (two_ne_zero' ℝ),
    pow_mul, sq, mul_apply]
#align circle_deg1_lift.transnum_aux_seq_dist_lt CircleDeg1Lift.transnum_aux_seq_dist_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_translation_number_aux [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.proj `f "." `transnumAuxSeq)
          `atTop
          («term_<|_»
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           "<|"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))])))
      (Command.declValSimple
       ":="
       (Term.proj
        (Term.app
         `cauchy_seq_of_le_geometric_two
         [(num "1")
          (Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            («term_<|_»
             `le_of_lt
             "<|"
             (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))])
        "."
        `tendsto_lim)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `cauchy_seq_of_le_geometric_two
        [(num "1")
         (Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           («term_<|_»
            `le_of_lt
            "<|"
            (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))])
       "."
       `tendsto_lim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `cauchy_seq_of_le_geometric_two
       [(num "1")
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          («term_<|_»
           `le_of_lt
           "<|"
           (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        («term_<|_» `le_of_lt "<|" (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `le_of_lt "<|" (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f "." `transnum_aux_seq_dist_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cauchy_seq_of_le_geometric_two
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `cauchy_seq_of_le_geometric_two
      [(num "1")
       (Term.fun
        "fun"
        (Term.basicFun
         [`n]
         []
         "=>"
         («term_<|_»
          `le_of_lt
          "<|"
          (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Tendsto
       [(Term.proj `f "." `transnumAuxSeq)
        `atTop
        («term_<|_»
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         "<|"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       "<|"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  tendsto_translation_number_aux
  : Tendsto f . transnumAuxSeq atTop 𝓝 <| τ f
  :=
    cauchy_seq_of_le_geometric_two 1 fun n => le_of_lt <| f . transnum_aux_seq_dist_lt n
      .
      tendsto_lim
#align circle_deg1_lift.tendsto_translation_number_aux CircleDeg1Lift.tendsto_translation_number_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `dist_map_zero_translation_number_le [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app
          `dist
          [(Term.app `f [(num "0")])
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f])])
         "≤"
         (num "1"))))
      (Command.declValSimple
       ":="
       (Term.subst
        (Term.proj `f "." `transnum_aux_seq_zero)
        "▸"
        [(Term.app
          `dist_le_of_le_geometric_two_of_tendsto₀
          [(num "1")
           (Term.fun
            "fun"
            (Term.basicFun
             [`n]
             []
             "=>"
             («term_<|_»
              `le_of_lt
              "<|"
              (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))
           (Term.proj `f "." `tendsto_translation_number_aux)])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.proj `f "." `transnum_aux_seq_zero)
       "▸"
       [(Term.app
         `dist_le_of_le_geometric_two_of_tendsto₀
         [(num "1")
          (Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            («term_<|_»
             `le_of_lt
             "<|"
             (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))
          (Term.proj `f "." `tendsto_translation_number_aux)])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `dist_le_of_le_geometric_two_of_tendsto₀
       [(num "1")
        (Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          («term_<|_» `le_of_lt "<|" (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))
        (Term.proj `f "." `tendsto_translation_number_aux)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `tendsto_translation_number_aux)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        («term_<|_» `le_of_lt "<|" (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `le_of_lt "<|" (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f "." `transnum_aux_seq_dist_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`n]
       []
       "=>"
       («term_<|_» `le_of_lt "<|" (Term.app (Term.proj `f "." `transnum_aux_seq_dist_lt) [`n]))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist_le_of_le_geometric_two_of_tendsto₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.proj `f "." `transnum_aux_seq_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app
        `dist
        [(Term.app `f [(num "0")])
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f])])
       "≤"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `dist
       [(Term.app `f [(num "0")])
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  dist_map_zero_translation_number_le
  : dist f 0 τ f ≤ 1
  :=
    f . transnum_aux_seq_zero
      ▸
      dist_le_of_le_geometric_two_of_tendsto₀
        1 fun n => le_of_lt <| f . transnum_aux_seq_dist_lt n f . tendsto_translation_number_aux
#align
  circle_deg1_lift.dist_map_zero_translation_number_le CircleDeg1Lift.dist_map_zero_translation_number_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_translation_number_of_dist_bounded_aux [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":" (Term.arrow (termℕ "ℕ") "→" (Data.Real.Basic.termℝ "ℝ"))]
         []
         ")")
        (Term.explicitBinder "(" [`C] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")
        (Term.explicitBinder
         "("
         [`H]
         [":"
          (Term.forall
           "∀"
           [`n]
           [(Term.typeSpec ":" (termℕ "ℕ"))]
           ","
           («term_≤_»
            (Term.app `dist [(Term.app («term_^_» `f "^" `n) [(num "0")]) (Term.app `x [`n])])
            "≤"
            `C))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`n]
            [(Term.typeSpec ":" (termℕ "ℕ"))]
            "=>"
            («term_/_»
             (Term.app `x [(«term_^_» (num "2") "^" `n)])
             "/"
             («term_^_» (num "2") "^" `n))))
          `atTop
          («term_<|_»
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           "<|"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `f.tendsto_translation_number_aux.congr_dist
             [(Term.app
               `squeeze_zero
               [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
                (Term.hole "_")
                (Term.hole "_")])]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun [`n] [] "=>" («term_/_» `C "/" («term_^_» (num "2") "^" `n)))))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`n])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_<_»
                   (num "0")
                   "<"
                   (Term.typeAscription
                    "("
                    («term_^_» (num "2") "^" `n)
                    ":"
                    [(Data.Real.Basic.termℝ "ℝ")]
                    ")")))]
                ":="
                (Term.app `pow_pos [`zero_lt_two (Term.hole "_")]))))
             []
             (convert
              "convert"
              []
              (Term.app
               (Term.proj (Term.app `div_le_div_right [`this]) "." (fieldIdx "2"))
               [(Term.app `H [(«term_^_» (num "2") "^" `n)])])
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `transnum_aux_seq)
                ","
                (Tactic.rwRule [] `Real.dist_eq)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_div)
                ","
                (Tactic.rwRule [] `abs_div)
                ","
                (Tactic.rwRule [] (Term.app `abs_of_pos [`this]))
                ","
                (Tactic.rwRule [] `Real.dist_eq)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.subst
               (Term.app `mul_zero [`C])
               "▸"
               [(Term.app
                 `tendsto_const_nhds.mul
                 [(«term_<|_»
                   `tendsto_inv_at_top_zero.comp
                   "<|"
                   (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two]))])]))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            `f.tendsto_translation_number_aux.congr_dist
            [(Term.app
              `squeeze_zero
              [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
               (Term.hole "_")
               (Term.hole "_")])]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun [`n] [] "=>" («term_/_» `C "/" («term_^_» (num "2") "^" `n)))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`n])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_<_»
                  (num "0")
                  "<"
                  (Term.typeAscription
                   "("
                   («term_^_» (num "2") "^" `n)
                   ":"
                   [(Data.Real.Basic.termℝ "ℝ")]
                   ")")))]
               ":="
               (Term.app `pow_pos [`zero_lt_two (Term.hole "_")]))))
            []
            (convert
             "convert"
             []
             (Term.app
              (Term.proj (Term.app `div_le_div_right [`this]) "." (fieldIdx "2"))
              [(Term.app `H [(«term_^_» (num "2") "^" `n)])])
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `transnum_aux_seq)
               ","
               (Tactic.rwRule [] `Real.dist_eq)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_div)
               ","
               (Tactic.rwRule [] `abs_div)
               ","
               (Tactic.rwRule [] (Term.app `abs_of_pos [`this]))
               ","
               (Tactic.rwRule [] `Real.dist_eq)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.subst
              (Term.app `mul_zero [`C])
              "▸"
              [(Term.app
                `tendsto_const_nhds.mul
                [(«term_<|_»
                  `tendsto_inv_at_top_zero.comp
                  "<|"
                  (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two]))])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.subst
          (Term.app `mul_zero [`C])
          "▸"
          [(Term.app
            `tendsto_const_nhds.mul
            [(«term_<|_»
              `tendsto_inv_at_top_zero.comp
              "<|"
              (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two]))])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.subst
        (Term.app `mul_zero [`C])
        "▸"
        [(Term.app
          `tendsto_const_nhds.mul
          [(«term_<|_»
            `tendsto_inv_at_top_zero.comp
            "<|"
            (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two]))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.app `mul_zero [`C])
       "▸"
       [(Term.app
         `tendsto_const_nhds.mul
         [(«term_<|_»
           `tendsto_inv_at_top_zero.comp
           "<|"
           (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto_const_nhds.mul
       [(«term_<|_»
         `tendsto_inv_at_top_zero.comp
         "<|"
         (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `tendsto_inv_at_top_zero.comp
       "<|"
       (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_lt_two
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_pow_at_top_at_top_of_one_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `tendsto_inv_at_top_zero.comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      `tendsto_inv_at_top_zero.comp
      "<|"
      (Term.app `tendsto_pow_at_top_at_top_of_one_lt [`one_lt_two]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_const_nhds.mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.app `mul_zero [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`n])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_<_»
              (num "0")
              "<"
              (Term.typeAscription
               "("
               («term_^_» (num "2") "^" `n)
               ":"
               [(Data.Real.Basic.termℝ "ℝ")]
               ")")))]
           ":="
           (Term.app `pow_pos [`zero_lt_two (Term.hole "_")]))))
        []
        (convert
         "convert"
         []
         (Term.app
          (Term.proj (Term.app `div_le_div_right [`this]) "." (fieldIdx "2"))
          [(Term.app `H [(«term_^_» (num "2") "^" `n)])])
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `transnum_aux_seq)
           ","
           (Tactic.rwRule [] `Real.dist_eq)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_div)
           ","
           (Tactic.rwRule [] `abs_div)
           ","
           (Tactic.rwRule [] (Term.app `abs_of_pos [`this]))
           ","
           (Tactic.rwRule [] `Real.dist_eq)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `transnum_aux_seq)
         ","
         (Tactic.rwRule [] `Real.dist_eq)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_div)
         ","
         (Tactic.rwRule [] `abs_div)
         ","
         (Tactic.rwRule [] (Term.app `abs_of_pos [`this]))
         ","
         (Tactic.rwRule [] `Real.dist_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.dist_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_of_pos [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_of_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_div
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_div
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.dist_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `transnum_aux_seq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        (Term.proj (Term.app `div_le_div_right [`this]) "." (fieldIdx "2"))
        [(Term.app `H [(«term_^_» (num "2") "^" `n)])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `div_le_div_right [`this]) "." (fieldIdx "2"))
       [(Term.app `H [(«term_^_» (num "2") "^" `n)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [(«term_^_» (num "2") "^" `n)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "2") "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» (num "2") "^" `n) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `H [(Term.paren "(" («term_^_» (num "2") "^" `n) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `div_le_div_right [`this]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `div_le_div_right [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_div_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `div_le_div_right [`this])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_<_»
            (num "0")
            "<"
            (Term.typeAscription
             "("
             («term_^_» (num "2") "^" `n)
             ":"
             [(Data.Real.Basic.termℝ "ℝ")]
             ")")))]
         ":="
         (Term.app `pow_pos [`zero_lt_two (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_pos [`zero_lt_two (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `zero_lt_two
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (num "0")
       "<"
       (Term.typeAscription "(" («term_^_» (num "2") "^" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" («term_^_» (num "2") "^" `n) ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "2") "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`n])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun [`n] [] "=>" («term_/_» `C "/" («term_^_» (num "2") "^" `n)))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun [`n] [] "=>" («term_/_» `C "/" («term_^_» (num "2") "^" `n)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`n] [] "=>" («term_/_» `C "/" («term_^_» (num "2") "^" `n))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `C "/" («term_^_» (num "2") "^" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "2") "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `f.tendsto_translation_number_aux.congr_dist
        [(Term.app
          `squeeze_zero
          [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
           (Term.hole "_")
           (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `f.tendsto_translation_number_aux.congr_dist
       [(Term.app
         `squeeze_zero
         [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
          (Term.hole "_")
          (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `squeeze_zero
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
        (Term.hole "_")
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_nonneg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `squeeze_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `squeeze_zero
      [(Term.paren "(" (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg)) ")")
       (Term.hole "_")
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.tendsto_translation_number_aux.congr_dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Tendsto
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          [(Term.typeSpec ":" (termℕ "ℕ"))]
          "=>"
          («term_/_»
           (Term.app `x [(«term_^_» (num "2") "^" `n)])
           "/"
           («term_^_» (num "2") "^" `n))))
        `atTop
        («term_<|_»
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         "<|"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       "<|"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  tendsto_translation_number_of_dist_bounded_aux
  ( x : ℕ → ℝ ) ( C : ℝ ) ( H : ∀ n : ℕ , dist f ^ n 0 x n ≤ C )
    : Tendsto fun n : ℕ => x 2 ^ n / 2 ^ n atTop 𝓝 <| τ f
  :=
    by
      refine' f.tendsto_translation_number_aux.congr_dist squeeze_zero fun _ => dist_nonneg _ _
        · exact fun n => C / 2 ^ n
        ·
          intro n
            have : 0 < ( 2 ^ n : ℝ ) := pow_pos zero_lt_two _
            convert div_le_div_right this . 2 H 2 ^ n
            rw
              [
                transnum_aux_seq
                  ,
                  Real.dist_eq
                  ,
                  ← sub_div
                  ,
                  abs_div
                  ,
                  abs_of_pos this
                  ,
                  Real.dist_eq
                ]
        ·
          exact
            mul_zero C
              ▸
              tendsto_const_nhds.mul
                tendsto_inv_at_top_zero.comp <| tendsto_pow_at_top_at_top_of_one_lt one_lt_two
#align
  circle_deg1_lift.tendsto_translation_number_of_dist_bounded_aux CircleDeg1Lift.tendsto_translation_number_of_dist_bounded_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_eq_of_dist_bounded [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [":" `CircleDeg1Lift] "}")
        (Term.explicitBinder "(" [`C] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")
        (Term.explicitBinder
         "("
         [`H]
         [":"
          (Term.forall
           "∀"
           [`n]
           [(Term.typeSpec ":" (termℕ "ℕ"))]
           ","
           («term_≤_»
            (Term.app
             `dist
             [(Term.app («term_^_» `f "^" `n) [(num "0")])
              (Term.app («term_^_» `g "^" `n) [(num "0")])])
            "≤"
            `C))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "="
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`g]))))
      (Command.declValSimple
       ":="
       («term_<|_»
        `Eq.symm
        "<|"
        («term_<|_»
         (Term.proj `g "." `translation_number_eq_of_tendsto_aux)
         "<|"
         (Term.app
          (Term.proj `f "." `tendsto_translation_number_of_dist_bounded_aux)
          [(Term.hole "_") `C `H])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `Eq.symm
       "<|"
       («term_<|_»
        (Term.proj `g "." `translation_number_eq_of_tendsto_aux)
        "<|"
        (Term.app
         (Term.proj `f "." `tendsto_translation_number_of_dist_bounded_aux)
         [(Term.hole "_") `C `H])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `g "." `translation_number_eq_of_tendsto_aux)
       "<|"
       (Term.app
        (Term.proj `f "." `tendsto_translation_number_of_dist_bounded_aux)
        [(Term.hole "_") `C `H]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `f "." `tendsto_translation_number_of_dist_bounded_aux)
       [(Term.hole "_") `C `H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f "." `tendsto_translation_number_of_dist_bounded_aux)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `g "." `translation_number_eq_of_tendsto_aux)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Eq.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "="
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_eq_of_dist_bounded
  { f g : CircleDeg1Lift } ( C : ℝ ) ( H : ∀ n : ℕ , dist f ^ n 0 g ^ n 0 ≤ C ) : τ f = τ g
  :=
    Eq.symm
      <|
      g . translation_number_eq_of_tendsto_aux
        <|
        f . tendsto_translation_number_of_dist_bounded_aux _ C H
#align
  circle_deg1_lift.translation_number_eq_of_dist_bounded CircleDeg1Lift.translation_number_eq_of_dist_bounded

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_one [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [(num "1")])
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app `translation_number_eq_of_tendsto₀ [(Term.hole "_")])
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `tendsto_const_nhds)] "]"]
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `translation_number_eq_of_tendsto₀ [(Term.hole "_")])
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `tendsto_const_nhds)] "]"]
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `tendsto_const_nhds)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `tendsto_const_nhds)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tendsto_const_nhds
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `translation_number_eq_of_tendsto₀ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_eq_of_tendsto₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(num "1")])
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
       [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    translation_number_one
    : τ 1 = 0
    := translation_number_eq_of_tendsto₀ _ <| by simp [ tendsto_const_nhds ]
#align circle_deg1_lift.translation_number_one CircleDeg1Lift.translation_number_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_eq_of_semiconj_by [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g₁ `g₂] [":" `CircleDeg1Lift] "}")
        (Term.explicitBinder "(" [`H] [":" (Term.app `SemiconjBy [`f `g₁ `g₂])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`g₁])
         "="
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`g₂]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `translation_number_eq_of_dist_bounded [(num "2")])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           («term_<|_»
            `le_of_lt
            "<|"
            («term_<|_»
             `dist_map_zero_lt_of_semiconj_by
             "<|"
             (Term.app (Term.proj `H "." `pow_right) [`n])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `translation_number_eq_of_dist_bounded [(num "2")])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          («term_<|_»
           `le_of_lt
           "<|"
           («term_<|_»
            `dist_map_zero_lt_of_semiconj_by
            "<|"
            (Term.app (Term.proj `H "." `pow_right) [`n])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        («term_<|_»
         `le_of_lt
         "<|"
         («term_<|_»
          `dist_map_zero_lt_of_semiconj_by
          "<|"
          (Term.app (Term.proj `H "." `pow_right) [`n])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `le_of_lt
       "<|"
       («term_<|_»
        `dist_map_zero_lt_of_semiconj_by
        "<|"
        (Term.app (Term.proj `H "." `pow_right) [`n])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `dist_map_zero_lt_of_semiconj_by
       "<|"
       (Term.app (Term.proj `H "." `pow_right) [`n]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `H "." `pow_right) [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `H "." `pow_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `dist_map_zero_lt_of_semiconj_by
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `translation_number_eq_of_dist_bounded [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_eq_of_dist_bounded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `translation_number_eq_of_dist_bounded [(num "2")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g₁])
       "="
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_eq_of_semiconj_by
  { f g₁ g₂ : CircleDeg1Lift } ( H : SemiconjBy f g₁ g₂ ) : τ g₁ = τ g₂
  :=
    translation_number_eq_of_dist_bounded 2
      fun n => le_of_lt <| dist_map_zero_lt_of_semiconj_by <| H . pow_right n
#align
  circle_deg1_lift.translation_number_eq_of_semiconj_by CircleDeg1Lift.translation_number_eq_of_semiconj_by

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_eq_of_semiconj [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g₁ `g₂] [":" `CircleDeg1Lift] "}")
        (Term.explicitBinder "(" [`H] [":" (Term.app `Function.Semiconj [`f `g₁ `g₂])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`g₁])
         "="
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`g₂]))))
      (Command.declValSimple
       ":="
       («term_<|_»
        `translation_number_eq_of_semiconj_by
        "<|"
        (Term.app (Term.proj `semiconj_by_iff_semiconj "." (fieldIdx "2")) [`H]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `translation_number_eq_of_semiconj_by
       "<|"
       (Term.app (Term.proj `semiconj_by_iff_semiconj "." (fieldIdx "2")) [`H]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `semiconj_by_iff_semiconj "." (fieldIdx "2")) [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `semiconj_by_iff_semiconj "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `semiconj_by_iff_semiconj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `translation_number_eq_of_semiconj_by
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g₁])
       "="
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_eq_of_semiconj
  { f g₁ g₂ : CircleDeg1Lift } ( H : Function.Semiconj f g₁ g₂ ) : τ g₁ = τ g₂
  := translation_number_eq_of_semiconj_by <| semiconj_by_iff_semiconj . 2 H
#align
  circle_deg1_lift.translation_number_eq_of_semiconj CircleDeg1Lift.translation_number_eq_of_semiconj

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_mul_of_commute [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [":" `CircleDeg1Lift] "}")
        (Term.explicitBinder "(" [`h] [":" (Term.app `Commute [`f `g])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [(«term_*_» `f "*" `g)])
         "="
         («term_+_»
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [`f])
          "+"
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [`g])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `tendsto
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`n]
                    [(Term.typeSpec ":" (termℕ "ℕ"))]
                    "=>"
                    («term_/_»
                     (Term.app
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`k]
                        []
                        "=>"
                        («term_+_»
                         (Term.app («term_^_» `f "^" `k) [(num "0")])
                         "+"
                         (Term.app («term_^_» `g "^" `k) [(num "0")]))))
                      [(«term_^_» (num "2") "^" `n)])
                     "/"
                     («term_^_» (num "2") "^" `n))))
                  `at_top
                  («term_<|_»
                   (TopologicalSpace.Topology.Basic.nhds "𝓝")
                   "<|"
                   («term_+_»
                    (Term.app
                     (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                     [`f])
                    "+"
                    (Term.app
                     (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                     [`g])))]))]
              ":="
              (Term.app
               (Term.proj
                (Term.app `f.tendsto_translation_number_aux.add [`g.tendsto_translation_number_aux])
                "."
                `congr)
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`n]
                  []
                  "=>"
                  (Term.proj
                   (Term.app
                    `add_div
                    [(Term.app («term_^_» `f "^" («term_^_» (num "2") "^" `n)) [(num "0")])
                     (Term.app («term_^_» `g "^" («term_^_» (num "2") "^" `n)) [(num "0")])
                     («term_^_»
                      (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                      "^"
                      `n)])
                   "."
                   `symm)))]))))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `tendsto_nhds_unique
             [(Term.app
               (Term.proj («term_*_» `f "*" `g) "." `tendsto_translation_number_of_dist_bounded_aux)
               [(Term.hole "_")
                (num "1")
                (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))])
              `this]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `h.mul_pow) "," (Tactic.rwRule [] `dist_comm)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `le_of_lt
             [(Term.app
               (Term.proj («term_^_» `f "^" `n) "." `dist_map_map_zero_lt)
               [(«term_^_» `g "^" `n)])]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`n]
                   [(Term.typeSpec ":" (termℕ "ℕ"))]
                   "=>"
                   («term_/_»
                    (Term.app
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [`k]
                       []
                       "=>"
                       («term_+_»
                        (Term.app («term_^_» `f "^" `k) [(num "0")])
                        "+"
                        (Term.app («term_^_» `g "^" `k) [(num "0")]))))
                     [(«term_^_» (num "2") "^" `n)])
                    "/"
                    («term_^_» (num "2") "^" `n))))
                 `at_top
                 («term_<|_»
                  (TopologicalSpace.Topology.Basic.nhds "𝓝")
                  "<|"
                  («term_+_»
                   (Term.app
                    (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                    [`f])
                   "+"
                   (Term.app
                    (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                    [`g])))]))]
             ":="
             (Term.app
              (Term.proj
               (Term.app `f.tendsto_translation_number_aux.add [`g.tendsto_translation_number_aux])
               "."
               `congr)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`n]
                 []
                 "=>"
                 (Term.proj
                  (Term.app
                   `add_div
                   [(Term.app («term_^_» `f "^" («term_^_» (num "2") "^" `n)) [(num "0")])
                    (Term.app («term_^_» `g "^" («term_^_» (num "2") "^" `n)) [(num "0")])
                    («term_^_»
                     (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                     "^"
                     `n)])
                  "."
                  `symm)))]))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `tendsto_nhds_unique
            [(Term.app
              (Term.proj («term_*_» `f "*" `g) "." `tendsto_translation_number_of_dist_bounded_aux)
              [(Term.hole "_")
               (num "1")
               (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))])
             `this]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `h.mul_pow) "," (Tactic.rwRule [] `dist_comm)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `le_of_lt
            [(Term.app
              (Term.proj («term_^_» `f "^" `n) "." `dist_map_map_zero_lt)
              [(«term_^_» `g "^" `n)])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `le_of_lt
        [(Term.app
          (Term.proj («term_^_» `f "^" `n) "." `dist_map_map_zero_lt)
          [(«term_^_» `g "^" `n)])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_lt
       [(Term.app
         (Term.proj («term_^_» `f "^" `n) "." `dist_map_map_zero_lt)
         [(«term_^_» `g "^" `n)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj («term_^_» `f "^" `n) "." `dist_map_map_zero_lt) [(«term_^_» `g "^" `n)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `g "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `g "^" `n) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_^_» `f "^" `n) "." `dist_map_map_zero_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `f "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `f "^" `n) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" («term_^_» `f "^" `n) ")") "." `dist_map_map_zero_lt)
      [(Term.paren "(" («term_^_» `g "^" `n) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h.mul_pow) "," (Tactic.rwRule [] `dist_comm)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.mul_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `tendsto_nhds_unique
        [(Term.app
          (Term.proj («term_*_» `f "*" `g) "." `tendsto_translation_number_of_dist_bounded_aux)
          [(Term.hole "_") (num "1") (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))])
         `this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto_nhds_unique
       [(Term.app
         (Term.proj («term_*_» `f "*" `g) "." `tendsto_translation_number_of_dist_bounded_aux)
         [(Term.hole "_") (num "1") (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))])
        `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj («term_*_» `f "*" `g) "." `tendsto_translation_number_of_dist_bounded_aux)
       [(Term.hole "_") (num "1") (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_*_» `f "*" `g) "." `tendsto_translation_number_of_dist_bounded_aux)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `f "*" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `f "*" `g) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" («term_*_» `f "*" `g) ")")
       "."
       `tendsto_translation_number_of_dist_bounded_aux)
      [(Term.hole "_") (num "1") (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_nhds_unique
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.app
            `tendsto
            [(Term.fun
              "fun"
              (Term.basicFun
               [`n]
               [(Term.typeSpec ":" (termℕ "ℕ"))]
               "=>"
               («term_/_»
                (Term.app
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`k]
                   []
                   "=>"
                   («term_+_»
                    (Term.app («term_^_» `f "^" `k) [(num "0")])
                    "+"
                    (Term.app («term_^_» `g "^" `k) [(num "0")]))))
                 [(«term_^_» (num "2") "^" `n)])
                "/"
                («term_^_» (num "2") "^" `n))))
             `at_top
             («term_<|_»
              (TopologicalSpace.Topology.Basic.nhds "𝓝")
              "<|"
              («term_+_»
               (Term.app
                (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                [`f])
               "+"
               (Term.app
                (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                [`g])))]))]
         ":="
         (Term.app
          (Term.proj
           (Term.app `f.tendsto_translation_number_aux.add [`g.tendsto_translation_number_aux])
           "."
           `congr)
          [(Term.fun
            "fun"
            (Term.basicFun
             [`n]
             []
             "=>"
             (Term.proj
              (Term.app
               `add_div
               [(Term.app («term_^_» `f "^" («term_^_» (num "2") "^" `n)) [(num "0")])
                (Term.app («term_^_» `g "^" («term_^_» (num "2") "^" `n)) [(num "0")])
                («term_^_»
                 (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 "^"
                 `n)])
              "."
              `symm)))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `f.tendsto_translation_number_aux.add [`g.tendsto_translation_number_aux])
        "."
        `congr)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.proj
           (Term.app
            `add_div
            [(Term.app («term_^_» `f "^" («term_^_» (num "2") "^" `n)) [(num "0")])
             (Term.app («term_^_» `g "^" («term_^_» (num "2") "^" `n)) [(num "0")])
             («term_^_»
              (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
              "^"
              `n)])
           "."
           `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.proj
         (Term.app
          `add_div
          [(Term.app («term_^_» `f "^" («term_^_» (num "2") "^" `n)) [(num "0")])
           (Term.app («term_^_» `g "^" («term_^_» (num "2") "^" `n)) [(num "0")])
           («term_^_»
            (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
            "^"
            `n)])
         "."
         `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `add_div
        [(Term.app («term_^_» `f "^" («term_^_» (num "2") "^" `n)) [(num "0")])
         (Term.app («term_^_» `g "^" («term_^_» (num "2") "^" `n)) [(num "0")])
         («term_^_»
          (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
          "^"
          `n)])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `add_div
       [(Term.app («term_^_» `f "^" («term_^_» (num "2") "^" `n)) [(num "0")])
        (Term.app («term_^_» `g "^" («term_^_» (num "2") "^" `n)) [(num "0")])
        («term_^_»
         (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         "^"
         `n)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") "^" `n)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app («term_^_» `g "^" («term_^_» (num "2") "^" `n)) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      («term_^_» `g "^" («term_^_» (num "2") "^" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "2") "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» `g "^" («term_^_» (num "2") "^" `n))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.paren "(" («term_^_» `g "^" («term_^_» (num "2") "^" `n)) ")") [(num "0")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app («term_^_» `f "^" («term_^_» (num "2") "^" `n)) [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      («term_^_» `f "^" («term_^_» (num "2") "^" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "2") "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» `f "^" («term_^_» (num "2") "^" `n))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.paren "(" («term_^_» `f "^" («term_^_» (num "2") "^" `n)) ")") [(num "0")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_div
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `add_div
      [(Term.paren
        "("
        (Term.app (Term.paren "(" («term_^_» `f "^" («term_^_» (num "2") "^" `n)) ")") [(num "0")])
        ")")
       (Term.paren
        "("
        (Term.app (Term.paren "(" («term_^_» `g "^" («term_^_» (num "2") "^" `n)) ")") [(num "0")])
        ")")
       (Term.paren
        "("
        («term_^_» (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") "^" `n)
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `f.tendsto_translation_number_aux.add [`g.tendsto_translation_number_aux])
       "."
       `congr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f.tendsto_translation_number_aux.add [`g.tendsto_translation_number_aux])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g.tendsto_translation_number_aux
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.tendsto_translation_number_aux.add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `f.tendsto_translation_number_aux.add [`g.tendsto_translation_number_aux])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          [(Term.typeSpec ":" (termℕ "ℕ"))]
          "=>"
          («term_/_»
           (Term.app
            (Term.fun
             "fun"
             (Term.basicFun
              [`k]
              []
              "=>"
              («term_+_»
               (Term.app («term_^_» `f "^" `k) [(num "0")])
               "+"
               (Term.app («term_^_» `g "^" `k) [(num "0")]))))
            [(«term_^_» (num "2") "^" `n)])
           "/"
           («term_^_» (num "2") "^" `n))))
        `at_top
        («term_<|_»
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         "<|"
         («term_+_»
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [`f])
          "+"
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [`g])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       "<|"
       («term_+_»
        (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
        "+"
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [`g])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "+"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_mul_of_commute
  { f g : CircleDeg1Lift } ( h : Commute f g ) : τ f * g = τ f + τ g
  :=
    by
      have
          : tendsto fun n : ℕ => fun k => f ^ k 0 + g ^ k 0 2 ^ n / 2 ^ n at_top 𝓝 <| τ f + τ g
            :=
            f.tendsto_translation_number_aux.add g.tendsto_translation_number_aux . congr
              fun n => add_div f ^ 2 ^ n 0 g ^ 2 ^ n 0 ( 2 : ℝ ) ^ n . symm
        refine'
          tendsto_nhds_unique
            f * g . tendsto_translation_number_of_dist_bounded_aux _ 1 fun n => _ this
        rw [ h.mul_pow , dist_comm ]
        exact le_of_lt f ^ n . dist_map_map_zero_lt g ^ n
#align
  circle_deg1_lift.translation_number_mul_of_commute CircleDeg1Lift.translation_number_mul_of_commute

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_units_inv [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Algebra.Group.Units.«term_ˣ» `CircleDeg1Lift "ˣ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [(coeNotation "↑" («term_⁻¹» `f "⁻¹"))])
         "="
         («term-_»
          "-"
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [`f])))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `eq_neg_iff_add_eq_zero "." (fieldIdx "2"))
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 `translation_number_mul_of_commute
                 [(Term.proj (Term.app `Commute.refl [(Term.hole "_")]) "." `units_inv_left)]))]
              "]"]
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `eq_neg_iff_add_eq_zero "." (fieldIdx "2"))
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma
               []
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `translation_number_mul_of_commute
                [(Term.proj (Term.app `Commute.refl [(Term.hole "_")]) "." `units_inv_left)]))]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma
              []
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `translation_number_mul_of_commute
               [(Term.proj (Term.app `Commute.refl [(Term.hole "_")]) "." `units_inv_left)]))]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `translation_number_mul_of_commute
           [(Term.proj (Term.app `Commute.refl [(Term.hole "_")]) "." `units_inv_left)]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `translation_number_mul_of_commute
       [(Term.proj (Term.app `Commute.refl [(Term.hole "_")]) "." `units_inv_left)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Commute.refl [(Term.hole "_")]) "." `units_inv_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Commute.refl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Commute.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Commute.refl [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_mul_of_commute
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `eq_neg_iff_add_eq_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eq_neg_iff_add_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(coeNotation "↑" («term_⁻¹» `f "⁻¹"))])
       "="
       («term-_»
        "-"
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [`f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    translation_number_units_inv
    ( f : CircleDeg1Lift ˣ ) : τ ↑ f ⁻¹ = - τ f
    :=
      eq_neg_iff_add_eq_zero . 2
        <|
        by simp [ ← translation_number_mul_of_commute Commute.refl _ . units_inv_left ]
#align circle_deg1_lift.translation_number_units_inv CircleDeg1Lift.translation_number_units_inv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_pow [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`n]
         [(Term.typeSpec ":" (termℕ "ℕ"))]
         ","
         («term_=_»
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [(«term_^_» `f "^" `n)])
          "="
          («term_*_»
           `n
           "*"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(num "0")]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))
          (Term.matchAlt
           "|"
           [[(«term_+_» `n "+" (num "1"))]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `pow_succ')
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `translation_number_mul_of_commute
                    [(Term.app `Commute.pow_self [`f `n])]))
                  ","
                  (Tactic.rwRule [] (Term.app `translation_number_pow [`n]))
                  ","
                  (Tactic.rwRule [] `Nat.cast_add_one)
                  ","
                  (Tactic.rwRule [] `add_mul)
                  ","
                  (Tactic.rwRule [] `one_mul)]
                 "]")
                [])]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `pow_succ')
             ","
             (Tactic.rwRule
              []
              (Term.app `translation_number_mul_of_commute [(Term.app `Commute.pow_self [`f `n])]))
             ","
             (Tactic.rwRule [] (Term.app `translation_number_pow [`n]))
             ","
             (Tactic.rwRule [] `Nat.cast_add_one)
             ","
             (Tactic.rwRule [] `add_mul)
             ","
             (Tactic.rwRule [] `one_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `pow_succ')
         ","
         (Tactic.rwRule
          []
          (Term.app `translation_number_mul_of_commute [(Term.app `Commute.pow_self [`f `n])]))
         ","
         (Tactic.rwRule [] (Term.app `translation_number_pow [`n]))
         ","
         (Tactic.rwRule [] `Nat.cast_add_one)
         ","
         (Tactic.rwRule [] `add_mul)
         ","
         (Tactic.rwRule [] `one_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_add_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `translation_number_pow [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `translation_number_mul_of_commute [(Term.app `Commute.pow_self [`f `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Commute.pow_self [`f `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Commute.pow_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Commute.pow_self [`f `n])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_mul_of_commute
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_succ'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     tactic) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`n]
       [(Term.typeSpec ":" (termℕ "ℕ"))]
       ","
       («term_=_»
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [(«term_^_» `f "^" `n)])
        "="
        («term_*_»
         `n
         "*"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(«term_^_» `f "^" `n)])
       "="
       («term_*_»
        `n
        "*"
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [`f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `n
       "*"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    translation_number_pow
    : ∀ n : ℕ , τ f ^ n = n * τ f
    | 0 => by simp
      |
        n + 1
        =>
        by
          rw
            [
              pow_succ'
                ,
                translation_number_mul_of_commute Commute.pow_self f n
                ,
                translation_number_pow n
                ,
                Nat.cast_add_one
                ,
                add_mul
                ,
                one_mul
              ]
#align circle_deg1_lift.translation_number_pow CircleDeg1Lift.translation_number_pow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_zpow [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Algebra.Group.Units.«term_ˣ» `CircleDeg1Lift "ˣ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`n]
         [(Term.typeSpec ":" (termℤ "ℤ"))]
         ","
         («term_=_»
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [(Term.typeAscription
             "("
             («term_^_» `f "^" `n)
             ":"
             [(Term.app `Units [(Term.hole "_")])]
             ")")])
          "="
          («term_*_»
           `n
           "*"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[(Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")")]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] (Term.app `translation_number_pow [`f `n]))] "]"]
                [])]))))
          (Term.matchAlt
           "|"
           [[(Int.«term-[_+1]» "-[" `n "+1]")]]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp "simp" [] [] [] [] []) [] (Mathlib.Tactic.RingNF.ring "ring")]))))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] [] []) [] (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Int.«term-[_+1]» "-[" `n "+1]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] (Term.app `translation_number_pow [`f `n]))] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `translation_number_pow [`f `n]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `translation_number_pow [`f `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     tactic) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `n ":" [(termℕ "ℕ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`n]
       [(Term.typeSpec ":" (termℤ "ℤ"))]
       ","
       («term_=_»
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [(Term.typeAscription
           "("
           («term_^_» `f "^" `n)
           ":"
           [(Term.app `Units [(Term.hole "_")])]
           ")")])
        "="
        («term_*_»
         `n
         "*"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(Term.typeAscription
          "("
          («term_^_» `f "^" `n)
          ":"
          [(Term.app `Units [(Term.hole "_")])]
          ")")])
       "="
       («term_*_»
        `n
        "*"
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [`f])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `n
       "*"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    translation_number_zpow
    ( f : CircleDeg1Lift ˣ ) : ∀ n : ℤ , τ ( f ^ n : Units _ ) = n * τ f
    | ( n : ℕ ) => by simp [ translation_number_pow f n ] | -[ n +1] => by simp ring
#align circle_deg1_lift.translation_number_zpow CircleDeg1Lift.translation_number_zpow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_conj_eq [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Algebra.Group.Units.«term_ˣ» `CircleDeg1Lift "ˣ")]
         []
         ")")
        (Term.explicitBinder "(" [`g] [":" `CircleDeg1Lift] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [(«term_*_»
            («term_*_» (coeNotation "↑" `f) "*" `g)
            "*"
            (coeNotation "↑" («term_⁻¹» `f "⁻¹")))])
         "="
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`g]))))
      (Command.declValSimple
       ":="
       (Term.proj
        (Term.app
         `translation_number_eq_of_semiconj_by
         [(Term.app (Term.proj `f "." `mk_semiconj_by) [`g])])
        "."
        `symm)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `translation_number_eq_of_semiconj_by
        [(Term.app (Term.proj `f "." `mk_semiconj_by) [`g])])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `translation_number_eq_of_semiconj_by
       [(Term.app (Term.proj `f "." `mk_semiconj_by) [`g])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f "." `mk_semiconj_by) [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f "." `mk_semiconj_by)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `f "." `mk_semiconj_by) [`g])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_eq_of_semiconj_by
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `translation_number_eq_of_semiconj_by
      [(Term.paren "(" (Term.app (Term.proj `f "." `mk_semiconj_by) [`g]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(«term_*_»
          («term_*_» (coeNotation "↑" `f) "*" `g)
          "*"
          (coeNotation "↑" («term_⁻¹» `f "⁻¹")))])
       "="
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    translation_number_conj_eq
    ( f : CircleDeg1Lift ˣ ) ( g : CircleDeg1Lift ) : τ ↑ f * g * ↑ f ⁻¹ = τ g
    := translation_number_eq_of_semiconj_by f . mk_semiconj_by g . symm
#align circle_deg1_lift.translation_number_conj_eq CircleDeg1Lift.translation_number_conj_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_conj_eq' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":" (Algebra.Group.Units.«term_ˣ» `CircleDeg1Lift "ˣ")]
         []
         ")")
        (Term.explicitBinder "(" [`g] [":" `CircleDeg1Lift] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [(«term_*_» («term_*_» (coeNotation "↑" («term_⁻¹» `f "⁻¹")) "*" `g) "*" `f)])
         "="
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`g]))))
      (Command.declValSimple
       ":="
       (Term.app `translation_number_conj_eq [(«term_⁻¹» `f "⁻¹") `g])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `translation_number_conj_eq [(«term_⁻¹» `f "⁻¹") `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_⁻¹» `f "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_conj_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(«term_*_» («term_*_» (coeNotation "↑" («term_⁻¹» `f "⁻¹")) "*" `g) "*" `f)])
       "="
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    translation_number_conj_eq'
    ( f : CircleDeg1Lift ˣ ) ( g : CircleDeg1Lift ) : τ ↑ f ⁻¹ * g * f = τ g
    := translation_number_conj_eq f ⁻¹ g
#align circle_deg1_lift.translation_number_conj_eq' CircleDeg1Lift.translation_number_conj_eq'

theorem dist_pow_map_zero_mul_translation_number_le (n : ℕ) :
    dist ((f ^ n) 0) (n * f.translationNumber) ≤ 1 :=
  f.translation_number_pow n ▸ (f ^ n).dist_map_zero_translation_number_le
#align
  circle_deg1_lift.dist_pow_map_zero_mul_translation_number_le CircleDeg1Lift.dist_pow_map_zero_mul_translation_number_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_translation_number₀' [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`n]
            [(Term.typeSpec ":" (termℕ "ℕ"))]
            "=>"
            («term_/_»
             (Term.app («term_^_» `f "^" («term_+_» `n "+" (num "1"))) [(num "0")])
             "/"
             («term_+_» `n "+" (num "1")))))
          `atTop
          («term_<|_»
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           "<|"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            («term_<|_»
             (Term.proj `tendsto_iff_dist_tendsto_zero "." (fieldIdx "2"))
             "<|"
             (Term.app
              `squeeze_zero
              [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
               (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
               (Term.app
                (Term.proj (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")]) "." `comp)
                [(Term.app `tendsto_add_at_top_nat [(num "1")])])])))
           []
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_<_»
                 (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 "<"
                 («term_+_» `n "+" (num "1"))))]
              ":="
              `n.cast_add_one_pos)))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Real.dist_eq)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `div_sub'
                [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `ne_of_gt [`this])]))
              ","
              (Tactic.rwRule [] `abs_div)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Real.dist_eq)
              ","
              (Tactic.rwRule [] (Term.app `abs_of_pos [`this]))
              ","
              (Tactic.rwRule [] `Nat.cast_add_one)
              ","
              (Tactic.rwRule [] (Term.app `div_le_div_right [`this]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)]
             "]")
            [])
           []
           (Tactic.apply "apply" `dist_pow_map_zero_mul_translation_number_le)])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           («term_<|_»
            (Term.proj `tendsto_iff_dist_tendsto_zero "." (fieldIdx "2"))
            "<|"
            (Term.app
             `squeeze_zero
             [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
              (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
              (Term.app
               (Term.proj (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")]) "." `comp)
               [(Term.app `tendsto_add_at_top_nat [(num "1")])])])))
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_<_»
                (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                "<"
                («term_+_» `n "+" (num "1"))))]
             ":="
             `n.cast_add_one_pos)))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Real.dist_eq)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `div_sub'
               [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `ne_of_gt [`this])]))
             ","
             (Tactic.rwRule [] `abs_div)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Real.dist_eq)
             ","
             (Tactic.rwRule [] (Term.app `abs_of_pos [`this]))
             ","
             (Tactic.rwRule [] `Nat.cast_add_one)
             ","
             (Tactic.rwRule [] (Term.app `div_le_div_right [`this]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)]
            "]")
           [])
          []
          (Tactic.apply "apply" `dist_pow_map_zero_mul_translation_number_le)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `dist_pow_map_zero_mul_translation_number_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_pow_map_zero_mul_translation_number_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Real.dist_eq)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `div_sub'
           [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `ne_of_gt [`this])]))
         ","
         (Tactic.rwRule [] `abs_div)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Real.dist_eq)
         ","
         (Tactic.rwRule [] (Term.app `abs_of_pos [`this]))
         ","
         (Tactic.rwRule [] `Nat.cast_add_one)
         ","
         (Tactic.rwRule [] (Term.app `div_le_div_right [`this]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_add_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `div_le_div_right [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_div_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_add_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_of_pos [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_of_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.dist_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_div
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `div_sub'
       [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.app `ne_of_gt [`this])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_of_gt [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ne_of_gt [`this]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_sub'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.dist_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_<_»
            (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
            "<"
            («term_+_» `n "+" (num "1"))))]
         ":="
         `n.cast_add_one_pos)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n.cast_add_one_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       "<"
       («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       («term_<|_»
        (Term.proj `tendsto_iff_dist_tendsto_zero "." (fieldIdx "2"))
        "<|"
        (Term.app
         `squeeze_zero
         [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
          (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
          (Term.app
           (Term.proj (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")]) "." `comp)
           [(Term.app `tendsto_add_at_top_nat [(num "1")])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `tendsto_iff_dist_tendsto_zero "." (fieldIdx "2"))
       "<|"
       (Term.app
        `squeeze_zero
        [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
         (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
         (Term.app
          (Term.proj (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")]) "." `comp)
          [(Term.app `tendsto_add_at_top_nat [(num "1")])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `squeeze_zero
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
        (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
        (Term.app
         (Term.proj (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")]) "." `comp)
         [(Term.app `tendsto_add_at_top_nat [(num "1")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")]) "." `comp)
       [(Term.app `tendsto_add_at_top_nat [(num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto_add_at_top_nat [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_add_at_top_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tendsto_add_at_top_nat [(num "1")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_const_div_at_top_nhds_0_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `tendsto_const_div_at_top_nhds_0_nat [(num "1")]) ")")
       "."
       `comp)
      [(Term.paren "(" (Term.app `tendsto_add_at_top_nat [(num "1")]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`n] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_nonneg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `dist_nonneg))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `squeeze_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `tendsto_iff_dist_tendsto_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `tendsto_iff_dist_tendsto_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Tendsto
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          [(Term.typeSpec ":" (termℕ "ℕ"))]
          "=>"
          («term_/_»
           (Term.app («term_^_» `f "^" («term_+_» `n "+" (num "1"))) [(num "0")])
           "/"
           («term_+_» `n "+" (num "1")))))
        `atTop
        («term_<|_»
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         "<|"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       "<|"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  tendsto_translation_number₀'
  : Tendsto fun n : ℕ => f ^ n + 1 0 / n + 1 atTop 𝓝 <| τ f
  :=
    by
      refine'
          tendsto_iff_dist_tendsto_zero . 2
            <|
            squeeze_zero
              fun _ => dist_nonneg
                fun n => _
                tendsto_const_div_at_top_nhds_0_nat 1 . comp tendsto_add_at_top_nat 1
        dsimp
        have : ( 0 : ℝ ) < n + 1 := n.cast_add_one_pos
        rw
          [
            Real.dist_eq
              ,
              div_sub' _ _ _ ne_of_gt this
              ,
              abs_div
              ,
              ← Real.dist_eq
              ,
              abs_of_pos this
              ,
              Nat.cast_add_one
              ,
              div_le_div_right this
              ,
              ← Nat.cast_add_one
            ]
        apply dist_pow_map_zero_mul_translation_number_le
#align circle_deg1_lift.tendsto_translation_number₀' CircleDeg1Lift.tendsto_translation_number₀'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_translation_number₀ [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`n]
            [(Term.typeSpec ":" (termℕ "ℕ"))]
            "=>"
            («term_/_» (Term.app («term_^_» `f "^" `n) [(num "0")]) "/" `n)))
          `atTop
          («term_<|_»
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           "<|"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "1"))
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_
              "exact_mod_cast"
              `f.tendsto_translation_number₀')])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "1"))
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.NormCast.tacticExact_mod_cast_
             "exact_mod_cast"
             `f.tendsto_translation_number₀')])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           `f.tendsto_translation_number₀')])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `f.tendsto_translation_number₀')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.tendsto_translation_number₀'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.NormCast.tacticExact_mod_cast_
          "exact_mod_cast"
          `f.tendsto_translation_number₀')])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tendsto_add_at_top_iff_nat [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_add_at_top_iff_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tendsto_add_at_top_iff_nat [(num "1")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Tendsto
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          [(Term.typeSpec ":" (termℕ "ℕ"))]
          "=>"
          («term_/_» (Term.app («term_^_» `f "^" `n) [(num "0")]) "/" `n)))
        `atTop
        («term_<|_»
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         "<|"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       "<|"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  tendsto_translation_number₀
  : Tendsto fun n : ℕ => f ^ n 0 / n atTop 𝓝 <| τ f
  := tendsto_add_at_top_iff_nat 1 . 1 by exact_mod_cast f.tendsto_translation_number₀'
#align circle_deg1_lift.tendsto_translation_number₀ CircleDeg1Lift.tendsto_translation_number₀

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For any `x : ℝ` the sequence $\\frac{f^n(x)-x}{n}$ tends to the translation number of `f`.\nIn particular, this limit does not depend on `x`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_translation_number [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`n]
            [(Term.typeSpec ":" (termℕ "ℕ"))]
            "=>"
            («term_/_» («term_-_» (Term.app («term_^_» `f "^" `n) [`x]) "-" `x) "/" `n)))
          `atTop
          («term_<|_»
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           "<|"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `translation_number_conj_eq'
                [(«term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))]))]
             "]")
            [])
           []
           (convert "convert" [] (Term.app `tendsto_translation_number₀ [(Term.hole "_")]) [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `sub_eq_neg_add)
              ","
              (Tactic.simpLemma [] [] `Units.conj_pow')]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `translation_number_conj_eq'
               [(«term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))]))]
            "]")
           [])
          []
          (convert "convert" [] (Term.app `tendsto_translation_number₀ [(Term.hole "_")]) [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `sub_eq_neg_add) "," (Tactic.simpLemma [] [] `Units.conj_pow')]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `sub_eq_neg_add) "," (Tactic.simpLemma [] [] `Units.conj_pow')]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.conj_pow'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_neg_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `n))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `tendsto_translation_number₀ [(Term.hole "_")]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tendsto_translation_number₀ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_translation_number₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `translation_number_conj_eq'
           [(«term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `translation_number_conj_eq'
       [(«term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Multiplicative.ofAdd [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiplicative.ofAdd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `translate
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_conj_eq'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Tendsto
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          [(Term.typeSpec ":" (termℕ "ℕ"))]
          "=>"
          («term_/_» («term_-_» (Term.app («term_^_» `f "^" `n) [`x]) "-" `x) "/" `n)))
        `atTop
        («term_<|_»
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         "<|"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       "<|"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    For any `x : ℝ` the sequence $\frac{f^n(x)-x}{n}$ tends to the translation number of `f`.
    In particular, this limit does not depend on `x`. -/
  theorem
    tendsto_translation_number
    ( x : ℝ ) : Tendsto fun n : ℕ => f ^ n x - x / n atTop 𝓝 <| τ f
    :=
      by
        rw [ ← translation_number_conj_eq' translate <| Multiplicative.ofAdd x ]
          convert tendsto_translation_number₀ _
          ext n
          simp [ sub_eq_neg_add , Units.conj_pow' ]
#align circle_deg1_lift.tendsto_translation_number CircleDeg1Lift.tendsto_translation_number

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tendsto_translation_number' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`n]
            [(Term.typeSpec ":" (termℕ "ℕ"))]
            "=>"
            («term_/_»
             («term_-_» (Term.app («term_^_» `f "^" («term_+_» `n "+" (num "1"))) [`x]) "-" `x)
             "/"
             («term_+_» `n "+" (num "1")))))
          `atTop
          («term_<|_»
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           "<|"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.NormCast.tacticExact_mod_cast_
            "exact_mod_cast"
            (Term.app
             (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "2"))
             [(Term.app `f.tendsto_translation_number [`x])]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticExact_mod_cast_
           "exact_mod_cast"
           (Term.app
            (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "2"))
            [(Term.app `f.tendsto_translation_number [`x])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_
       "exact_mod_cast"
       (Term.app
        (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "2"))
        [(Term.app `f.tendsto_translation_number [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "2"))
       [(Term.app `f.tendsto_translation_number [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.tendsto_translation_number [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.tendsto_translation_number
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `f.tendsto_translation_number [`x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tendsto_add_at_top_iff_nat [(num "1")]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tendsto_add_at_top_iff_nat [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_add_at_top_iff_nat
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tendsto_add_at_top_iff_nat [(num "1")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Tendsto
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          [(Term.typeSpec ":" (termℕ "ℕ"))]
          "=>"
          («term_/_»
           («term_-_» (Term.app («term_^_» `f "^" («term_+_» `n "+" (num "1"))) [`x]) "-" `x)
           "/"
           («term_+_» `n "+" (num "1")))))
        `atTop
        («term_<|_»
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         "<|"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       "<|"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  tendsto_translation_number'
  ( x : ℝ ) : Tendsto fun n : ℕ => f ^ n + 1 x - x / n + 1 atTop 𝓝 <| τ f
  := by exact_mod_cast tendsto_add_at_top_iff_nat 1 . 2 f.tendsto_translation_number x
#align circle_deg1_lift.tendsto_translation_number' CircleDeg1Lift.tendsto_translation_number'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_mono [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Monotone
         [(CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`f `g `h]
         []
         "=>"
         (Term.app
          (Term.app
           `le_of_tendsto_of_tendsto'
           [(Term.proj `f "." `tendsto_translation_number₀)
            (Term.proj `g "." `tendsto_translation_number₀)])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`n]
             []
             "=>"
             (Term.app
              `div_le_div_of_le_of_nonneg
              [(Term.app `pow_mono [`h `n (num "0")]) (Term.proj `n "." `cast_nonneg)])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h]
        []
        "=>"
        (Term.app
         (Term.app
          `le_of_tendsto_of_tendsto'
          [(Term.proj `f "." `tendsto_translation_number₀)
           (Term.proj `g "." `tendsto_translation_number₀)])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`n]
            []
            "=>"
            (Term.app
             `div_le_div_of_le_of_nonneg
             [(Term.app `pow_mono [`h `n (num "0")]) (Term.proj `n "." `cast_nonneg)])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app
        `le_of_tendsto_of_tendsto'
        [(Term.proj `f "." `tendsto_translation_number₀)
         (Term.proj `g "." `tendsto_translation_number₀)])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          (Term.app
           `div_le_div_of_le_of_nonneg
           [(Term.app `pow_mono [`h `n (num "0")]) (Term.proj `n "." `cast_nonneg)])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        (Term.app
         `div_le_div_of_le_of_nonneg
         [(Term.app `pow_mono [`h `n (num "0")]) (Term.proj `n "." `cast_nonneg)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `div_le_div_of_le_of_nonneg
       [(Term.app `pow_mono [`h `n (num "0")]) (Term.proj `n "." `cast_nonneg)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `n "." `cast_nonneg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `pow_mono [`h `n (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pow_mono [`h `n (num "0")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_div_of_le_of_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app
       `le_of_tendsto_of_tendsto'
       [(Term.proj `f "." `tendsto_translation_number₀)
        (Term.proj `g "." `tendsto_translation_number₀)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `g "." `tendsto_translation_number₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f "." `tendsto_translation_number₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_tendsto_of_tendsto'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_of_tendsto_of_tendsto'
      [(Term.proj `f "." `tendsto_translation_number₀)
       (Term.proj `g "." `tendsto_translation_number₀)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Monotone
       [(CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_mono
  : Monotone τ
  :=
    fun
      f g h
        =>
        le_of_tendsto_of_tendsto' f . tendsto_translation_number₀ g . tendsto_translation_number₀
          fun n => div_le_div_of_le_of_nonneg pow_mono h n 0 n . cast_nonneg
#align circle_deg1_lift.translation_number_mono CircleDeg1Lift.translation_number_mono

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_translate [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [(«term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))])
         "="
         `x)))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app `translation_number_eq_of_tendsto₀' [(Term.hole "_")])
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [] `Nat.cast_add_one_ne_zero)
               ","
               (Tactic.simpLemma [] [] `mul_div_cancel_left)
               ","
               (Tactic.simpLemma [] [] `tendsto_const_nhds)]
              "]"]
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `translation_number_eq_of_tendsto₀' [(Term.hole "_")])
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `Nat.cast_add_one_ne_zero)
              ","
              (Tactic.simpLemma [] [] `mul_div_cancel_left)
              ","
              (Tactic.simpLemma [] [] `tendsto_const_nhds)]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `Nat.cast_add_one_ne_zero)
             ","
             (Tactic.simpLemma [] [] `mul_div_cancel_left)
             ","
             (Tactic.simpLemma [] [] `tendsto_const_nhds)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `Nat.cast_add_one_ne_zero)
         ","
         (Tactic.simpLemma [] [] `mul_div_cancel_left)
         ","
         (Tactic.simpLemma [] [] `tendsto_const_nhds)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tendsto_const_nhds
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_div_cancel_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_add_one_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `translation_number_eq_of_tendsto₀' [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_eq_of_tendsto₀'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(«term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))])
       "="
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
       [(«term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Multiplicative.ofAdd [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiplicative.ofAdd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `translate
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `translate "<|" (Term.app `Multiplicative.ofAdd [`x]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_translate
  ( x : ℝ ) : τ translate <| Multiplicative.ofAdd x = x
  :=
    translation_number_eq_of_tendsto₀' _
      <|
      by simp [ Nat.cast_add_one_ne_zero , mul_div_cancel_left , tendsto_const_nhds ]
#align circle_deg1_lift.translation_number_translate CircleDeg1Lift.translation_number_translate

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_le_of_le_add [])
      (Command.declSig
       [(Term.implicitBinder "{" [`z] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`hz]
         [":"
          (Term.forall "∀" [`x] [] "," («term_≤_» (Term.app `f [`x]) "≤" («term_+_» `x "+" `z)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "≤"
         `z)))
      (Command.declValSimple
       ":="
       (Term.subst
        (Term.app `translation_number_translate [`z])
        "▸"
        [(Term.app
          `translation_number_mono
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.app
              `trans_rel_left
              [(Term.hole "_")
               (Term.app `hz [`x])
               (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])])))])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.app `translation_number_translate [`z])
       "▸"
       [(Term.app
         `translation_number_mono
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.app
             `trans_rel_left
             [(Term.hole "_")
              (Term.app `hz [`x])
              (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])])))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `translation_number_mono
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app
           `trans_rel_left
           [(Term.hole "_")
            (Term.app `hz [`x])
            (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app
         `trans_rel_left
         [(Term.hole "_")
          (Term.app `hz [`x])
          (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `trans_rel_left
       [(Term.hole "_") (Term.app `hz [`x]) (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hz [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hz [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trans_rel_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.app `translation_number_translate [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_translate
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "≤"
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_le_of_le_add
  { z : ℝ } ( hz : ∀ x , f x ≤ x + z ) : τ f ≤ z
  :=
    translation_number_translate z
      ▸
      translation_number_mono fun x => trans_rel_left _ hz x add_comm _ _
#align
  circle_deg1_lift.translation_number_le_of_le_add CircleDeg1Lift.translation_number_le_of_le_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `le_translation_number_of_add_le [])
      (Command.declSig
       [(Term.implicitBinder "{" [`z] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`hz]
         [":"
          (Term.forall "∀" [`x] [] "," («term_≤_» («term_+_» `x "+" `z) "≤" (Term.app `f [`x])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         `z
         "≤"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))))
      (Command.declValSimple
       ":="
       (Term.subst
        (Term.app `translation_number_translate [`z])
        "▸"
        [(Term.app
          `translation_number_mono
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.app
              `trans_rel_right
              [(Term.hole "_")
               (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])
               (Term.app `hz [`x])])))])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.app `translation_number_translate [`z])
       "▸"
       [(Term.app
         `translation_number_mono
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Term.app
             `trans_rel_right
             [(Term.hole "_")
              (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])
              (Term.app `hz [`x])])))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `translation_number_mono
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app
           `trans_rel_right
           [(Term.hole "_")
            (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])
            (Term.app `hz [`x])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app
         `trans_rel_right
         [(Term.hole "_")
          (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])
          (Term.app `hz [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `trans_rel_right
       [(Term.hole "_") (Term.app `add_comm [(Term.hole "_") (Term.hole "_")]) (Term.app `hz [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hz [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hz [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `add_comm [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `trans_rel_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.app `translation_number_translate [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_translate
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       `z
       "≤"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  le_translation_number_of_add_le
  { z : ℝ } ( hz : ∀ x , x + z ≤ f x ) : z ≤ τ f
  :=
    translation_number_translate z
      ▸
      translation_number_mono fun x => trans_rel_right _ add_comm _ _ hz x
#align
  circle_deg1_lift.le_translation_number_of_add_le CircleDeg1Lift.le_translation_number_of_add_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_le_of_le_add_int [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`m] [":" (termℤ "ℤ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_≤_» (Term.app `f [`x]) "≤" («term_+_» `x "+" `m))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "≤"
         `m)))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `le_of_tendsto' [(Term.app (Term.proj `f "." `tendsto_translation_number') [`x])])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           («term_<|_»
            (Term.proj
             (Term.app
              `div_le_iff'
              [(Term.typeAscription
                "("
                (Term.proj `n "." `cast_add_one_pos)
                ":"
                [(«term_<_»
                  (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  "<"
                  (Term.hole "_"))]
                ")")])
             "."
             `mpr)
            "<|"
            («term_<|_»
             (Term.proj `sub_le_iff_le_add' "." (fieldIdx "2"))
             "<|"
             (Term.subst
              (Term.proj (Term.app `coe_pow [`f («term_+_» `n "+" (num "1"))]) "." `symm)
              "▸"
              [(Term.subst
                (Term.app
                 (Term.explicit "@" `Nat.cast_add_one)
                 [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") `n])
                "▸"
                [(Term.app
                  (Term.proj `f "." `iterate_le_of_map_le_add_int)
                  [`h («term_+_» `n "+" (num "1"))])])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `le_of_tendsto' [(Term.app (Term.proj `f "." `tendsto_translation_number') [`x])])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          («term_<|_»
           (Term.proj
            (Term.app
             `div_le_iff'
             [(Term.typeAscription
               "("
               (Term.proj `n "." `cast_add_one_pos)
               ":"
               [(«term_<_»
                 (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 "<"
                 (Term.hole "_"))]
               ")")])
            "."
            `mpr)
           "<|"
           («term_<|_»
            (Term.proj `sub_le_iff_le_add' "." (fieldIdx "2"))
            "<|"
            (Term.subst
             (Term.proj (Term.app `coe_pow [`f («term_+_» `n "+" (num "1"))]) "." `symm)
             "▸"
             [(Term.subst
               (Term.app
                (Term.explicit "@" `Nat.cast_add_one)
                [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") `n])
               "▸"
               [(Term.app
                 (Term.proj `f "." `iterate_le_of_map_le_add_int)
                 [`h («term_+_» `n "+" (num "1"))])])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        («term_<|_»
         (Term.proj
          (Term.app
           `div_le_iff'
           [(Term.typeAscription
             "("
             (Term.proj `n "." `cast_add_one_pos)
             ":"
             [(«term_<_»
               (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
               "<"
               (Term.hole "_"))]
             ")")])
          "."
          `mpr)
         "<|"
         («term_<|_»
          (Term.proj `sub_le_iff_le_add' "." (fieldIdx "2"))
          "<|"
          (Term.subst
           (Term.proj (Term.app `coe_pow [`f («term_+_» `n "+" (num "1"))]) "." `symm)
           "▸"
           [(Term.subst
             (Term.app
              (Term.explicit "@" `Nat.cast_add_one)
              [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") `n])
             "▸"
             [(Term.app
               (Term.proj `f "." `iterate_le_of_map_le_add_int)
               [`h («term_+_» `n "+" (num "1"))])])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj
        (Term.app
         `div_le_iff'
         [(Term.typeAscription
           "("
           (Term.proj `n "." `cast_add_one_pos)
           ":"
           [(«term_<_»
             (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
             "<"
             (Term.hole "_"))]
           ")")])
        "."
        `mpr)
       "<|"
       («term_<|_»
        (Term.proj `sub_le_iff_le_add' "." (fieldIdx "2"))
        "<|"
        (Term.subst
         (Term.proj (Term.app `coe_pow [`f («term_+_» `n "+" (num "1"))]) "." `symm)
         "▸"
         [(Term.subst
           (Term.app
            (Term.explicit "@" `Nat.cast_add_one)
            [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") `n])
           "▸"
           [(Term.app
             (Term.proj `f "." `iterate_le_of_map_le_add_int)
             [`h («term_+_» `n "+" (num "1"))])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `sub_le_iff_le_add' "." (fieldIdx "2"))
       "<|"
       (Term.subst
        (Term.proj (Term.app `coe_pow [`f («term_+_» `n "+" (num "1"))]) "." `symm)
        "▸"
        [(Term.subst
          (Term.app
           (Term.explicit "@" `Nat.cast_add_one)
           [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") `n])
          "▸"
          [(Term.app
            (Term.proj `f "." `iterate_le_of_map_le_add_int)
            [`h («term_+_» `n "+" (num "1"))])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.proj (Term.app `coe_pow [`f («term_+_» `n "+" (num "1"))]) "." `symm)
       "▸"
       [(Term.subst
         (Term.app
          (Term.explicit "@" `Nat.cast_add_one)
          [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") `n])
         "▸"
         [(Term.app
           (Term.proj `f "." `iterate_le_of_map_le_add_int)
           [`h («term_+_» `n "+" (num "1"))])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.app
        (Term.explicit "@" `Nat.cast_add_one)
        [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") `n])
       "▸"
       [(Term.app
         (Term.proj `f "." `iterate_le_of_map_le_add_int)
         [`h («term_+_» `n "+" (num "1"))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f "." `iterate_le_of_map_le_add_int) [`h («term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f "." `iterate_le_of_map_le_add_int)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.app
       (Term.explicit "@" `Nat.cast_add_one)
       [(Data.Real.Basic.termℝ "ℝ") (Term.hole "_") `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Nat.cast_add_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_add_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.proj (Term.app `coe_pow [`f («term_+_» `n "+" (num "1"))]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `coe_pow [`f («term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coe_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `coe_pow [`f (Term.paren "(" («term_+_» `n "+" (num "1")) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `sub_le_iff_le_add' "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sub_le_iff_le_add'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        `div_le_iff'
        [(Term.typeAscription
          "("
          (Term.proj `n "." `cast_add_one_pos)
          ":"
          [(«term_<_»
            (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
            "<"
            (Term.hole "_"))]
          ")")])
       "."
       `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `div_le_iff'
       [(Term.typeAscription
         "("
         (Term.proj `n "." `cast_add_one_pos)
         ":"
         [(«term_<_»
           (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
           "<"
           (Term.hole "_"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.proj `n "." `cast_add_one_pos)
       ":"
       [(«term_<_»
         (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         "<"
         (Term.hole "_"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       "<"
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `n "." `cast_add_one_pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_iff'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `div_le_iff'
      [(Term.typeAscription
        "("
        (Term.proj `n "." `cast_add_one_pos)
        ":"
        [(«term_<_»
          (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
          "<"
          (Term.hole "_"))]
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `le_of_tendsto' [(Term.app (Term.proj `f "." `tendsto_translation_number') [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f "." `tendsto_translation_number') [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f "." `tendsto_translation_number')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `f "." `tendsto_translation_number') [`x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_tendsto'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_of_tendsto'
      [(Term.paren "(" (Term.app (Term.proj `f "." `tendsto_translation_number') [`x]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "≤"
       `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_le_of_le_add_int
  { x : ℝ } { m : ℤ } ( h : f x ≤ x + m ) : τ f ≤ m
  :=
    le_of_tendsto' f . tendsto_translation_number' x
      fun
        n
          =>
          div_le_iff' ( n . cast_add_one_pos : ( 0 : ℝ ) < _ ) . mpr
            <|
            sub_le_iff_le_add' . 2
              <|
              coe_pow f n + 1 . symm
                ▸
                @ Nat.cast_add_one ℝ _ n ▸ f . iterate_le_of_map_le_add_int h n + 1
#align
  circle_deg1_lift.translation_number_le_of_le_add_int CircleDeg1Lift.translation_number_le_of_le_add_int

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_le_of_le_add_nat [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`m] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_≤_» (Term.app `f [`x]) "≤" («term_+_» `x "+" `m))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "≤"
         `m)))
      (Command.declValSimple
       ":="
       (Term.app (Term.explicit "@" `translation_number_le_of_le_add_int) [`f `x `m `h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `translation_number_le_of_le_add_int) [`f `x `m `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `translation_number_le_of_le_add_int)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `translation_number_le_of_le_add_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "≤"
       `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_le_of_le_add_nat
  { x : ℝ } { m : ℕ } ( h : f x ≤ x + m ) : τ f ≤ m
  := @ translation_number_le_of_le_add_int f x m h
#align
  circle_deg1_lift.translation_number_le_of_le_add_nat CircleDeg1Lift.translation_number_le_of_le_add_nat

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `le_translation_number_of_add_int_le [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`m] [":" (termℤ "ℤ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_≤_» («term_+_» `x "+" `m) "≤" (Term.app `f [`x]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (coeNotation "↑" `m)
         "≤"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `ge_of_tendsto' [(Term.app (Term.proj `f "." `tendsto_translation_number') [`x])])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`n]
           []
           "=>"
           («term_<|_»
            (Term.proj
             (Term.app
              `le_div_iff
              [(Term.typeAscription
                "("
                (Term.proj `n "." `cast_add_one_pos)
                ":"
                [(«term_<_»
                  (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  "<"
                  (Term.hole "_"))]
                ")")])
             "."
             `mpr)
            "<|"
            («term_<|_»
             (Term.proj `le_sub_iff_add_le' "." (fieldIdx "2"))
             "<|"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `coe_pow)
                    ","
                    (Tactic.simpLemma
                     []
                     []
                     (Term.app
                      `mul_comm
                      [(Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)
                    ","
                    (Tactic.simpLemma [] [] (Term.app `f.le_iterate_of_add_int_le_map [`h]))]
                   "]"]
                  [])])))))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `ge_of_tendsto' [(Term.app (Term.proj `f "." `tendsto_translation_number') [`x])])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`n]
          []
          "=>"
          («term_<|_»
           (Term.proj
            (Term.app
             `le_div_iff
             [(Term.typeAscription
               "("
               (Term.proj `n "." `cast_add_one_pos)
               ":"
               [(«term_<_»
                 (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 "<"
                 (Term.hole "_"))]
               ")")])
            "."
            `mpr)
           "<|"
           («term_<|_»
            (Term.proj `le_sub_iff_add_le' "." (fieldIdx "2"))
            "<|"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `coe_pow)
                   ","
                   (Tactic.simpLemma
                    []
                    []
                    (Term.app
                     `mul_comm
                     [(Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                   ","
                   (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)
                   ","
                   (Tactic.simpLemma [] [] (Term.app `f.le_iterate_of_add_int_le_map [`h]))]
                  "]"]
                 [])])))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`n]
        []
        "=>"
        («term_<|_»
         (Term.proj
          (Term.app
           `le_div_iff
           [(Term.typeAscription
             "("
             (Term.proj `n "." `cast_add_one_pos)
             ":"
             [(«term_<_»
               (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
               "<"
               (Term.hole "_"))]
             ")")])
          "."
          `mpr)
         "<|"
         («term_<|_»
          (Term.proj `le_sub_iff_add_le' "." (fieldIdx "2"))
          "<|"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `coe_pow)
                 ","
                 (Tactic.simpLemma
                  []
                  []
                  (Term.app
                   `mul_comm
                   [(Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                 ","
                 (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)
                 ","
                 (Tactic.simpLemma [] [] (Term.app `f.le_iterate_of_add_int_le_map [`h]))]
                "]"]
               [])])))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj
        (Term.app
         `le_div_iff
         [(Term.typeAscription
           "("
           (Term.proj `n "." `cast_add_one_pos)
           ":"
           [(«term_<_»
             (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
             "<"
             (Term.hole "_"))]
           ")")])
        "."
        `mpr)
       "<|"
       («term_<|_»
        (Term.proj `le_sub_iff_add_le' "." (fieldIdx "2"))
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `coe_pow)
               ","
               (Tactic.simpLemma
                []
                []
                (Term.app
                 `mul_comm
                 [(Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)
               ","
               (Tactic.simpLemma [] [] (Term.app `f.le_iterate_of_add_int_le_map [`h]))]
              "]"]
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `le_sub_iff_add_le' "." (fieldIdx "2"))
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `coe_pow)
              ","
              (Tactic.simpLemma
               []
               []
               (Term.app
                `mul_comm
                [(Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)
              ","
              (Tactic.simpLemma [] [] (Term.app `f.le_iterate_of_add_int_le_map [`h]))]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `coe_pow)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.app
               `mul_comm
               [(Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)
             ","
             (Tactic.simpLemma [] [] (Term.app `f.le_iterate_of_add_int_le_map [`h]))]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `coe_pow)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.app `mul_comm [(Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Nat.cast_add_one)
         ","
         (Tactic.simpLemma [] [] (Term.app `f.le_iterate_of_add_int_le_map [`h]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.le_iterate_of_add_int_le_map [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.le_iterate_of_add_int_le_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_add_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [(Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `le_sub_iff_add_le' "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `le_sub_iff_add_le'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        `le_div_iff
        [(Term.typeAscription
          "("
          (Term.proj `n "." `cast_add_one_pos)
          ":"
          [(«term_<_»
            (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
            "<"
            (Term.hole "_"))]
          ")")])
       "."
       `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `le_div_iff
       [(Term.typeAscription
         "("
         (Term.proj `n "." `cast_add_one_pos)
         ":"
         [(«term_<_»
           (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
           "<"
           (Term.hole "_"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.proj `n "." `cast_add_one_pos)
       ":"
       [(«term_<_»
         (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         "<"
         (Term.hole "_"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       "<"
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `n "." `cast_add_one_pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_div_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_div_iff
      [(Term.typeAscription
        "("
        (Term.proj `n "." `cast_add_one_pos)
        ":"
        [(«term_<_»
          (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
          "<"
          (Term.hole "_"))]
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `ge_of_tendsto' [(Term.app (Term.proj `f "." `tendsto_translation_number') [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f "." `tendsto_translation_number') [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f "." `tendsto_translation_number')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `f "." `tendsto_translation_number') [`x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ge_of_tendsto'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `ge_of_tendsto'
      [(Term.paren "(" (Term.app (Term.proj `f "." `tendsto_translation_number') [`x]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (coeNotation "↑" `m)
       "≤"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  le_translation_number_of_add_int_le
  { x : ℝ } { m : ℤ } ( h : x + m ≤ f x ) : ↑ m ≤ τ f
  :=
    ge_of_tendsto' f . tendsto_translation_number' x
      fun
        n
          =>
          le_div_iff ( n . cast_add_one_pos : ( 0 : ℝ ) < _ ) . mpr
            <|
            le_sub_iff_add_le' . 2
              <|
              by
                simp
                  only
                  [
                    coe_pow
                      ,
                      mul_comm ( m : ℝ )
                      ,
                      ← Nat.cast_add_one
                      ,
                      f.le_iterate_of_add_int_le_map h
                    ]
#align
  circle_deg1_lift.le_translation_number_of_add_int_le CircleDeg1Lift.le_translation_number_of_add_int_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `le_translation_number_of_add_nat_le [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`m] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_≤_» («term_+_» `x "+" `m) "≤" (Term.app `f [`x]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (coeNotation "↑" `m)
         "≤"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))))
      (Command.declValSimple
       ":="
       (Term.app (Term.explicit "@" `le_translation_number_of_add_int_le) [`f `x `m `h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `le_translation_number_of_add_int_le) [`f `x `m `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `le_translation_number_of_add_int_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_translation_number_of_add_int_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (coeNotation "↑" `m)
       "≤"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  le_translation_number_of_add_nat_le
  { x : ℝ } { m : ℕ } ( h : x + m ≤ f x ) : ↑ m ≤ τ f
  := @ le_translation_number_of_add_int_le f x m h
#align
  circle_deg1_lift.le_translation_number_of_add_nat_le CircleDeg1Lift.le_translation_number_of_add_nat_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `f x - x` is an integer number `m` for some point `x`, then `τ f = m`.\nOn the circle this means that a map with a fixed point has rotation number zero. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_of_eq_add_int [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`m] [":" (termℤ "ℤ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_=_» (Term.app `f [`x]) "=" («term_+_» `x "+" `m))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "="
         `m)))
      (Command.declValSimple
       ":="
       (Term.app
        `le_antisymm
        [(«term_<|_»
          (Term.app `translation_number_le_of_le_add_int [`f])
          "<|"
          (Term.app `le_of_eq [`h]))
         («term_<|_»
          (Term.app `le_translation_number_of_add_int_le [`f])
          "<|"
          (Term.app `le_of_eq [(Term.proj `h "." `symm)]))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_antisymm
       [(«term_<|_»
         (Term.app `translation_number_le_of_le_add_int [`f])
         "<|"
         (Term.app `le_of_eq [`h]))
        («term_<|_»
         (Term.app `le_translation_number_of_add_int_le [`f])
         "<|"
         (Term.app `le_of_eq [(Term.proj `h "." `symm)]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `le_translation_number_of_add_int_le [`f])
       "<|"
       (Term.app `le_of_eq [(Term.proj `h "." `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_eq [(Term.proj `h "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `le_translation_number_of_add_int_le [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_translation_number_of_add_int_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `le_translation_number_of_add_int_le [`f])
      "<|"
      (Term.app `le_of_eq [(Term.proj `h "." `symm)]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app `translation_number_le_of_le_add_int [`f])
       "<|"
       (Term.app `le_of_eq [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_eq [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `translation_number_le_of_le_add_int [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_le_of_le_add_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `translation_number_le_of_le_add_int [`f])
      "<|"
      (Term.app `le_of_eq [`h]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "="
       `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `f x - x` is an integer number `m` for some point `x`, then `τ f = m`.
    On the circle this means that a map with a fixed point has rotation number zero. -/
  theorem
    translation_number_of_eq_add_int
    { x : ℝ } { m : ℤ } ( h : f x = x + m ) : τ f = m
    :=
      le_antisymm
        translation_number_le_of_le_add_int f <| le_of_eq h
          le_translation_number_of_add_int_le f <| le_of_eq h . symm
#align
  circle_deg1_lift.translation_number_of_eq_add_int CircleDeg1Lift.translation_number_of_eq_add_int

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `floor_sub_le_translation_number [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (coeNotation
          "↑"
          (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" («term_-_» (Term.app `f [`x]) "-" `x) "⌋"))
         "≤"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app `le_translation_number_of_add_int_le [`f])
        "<|"
        (Term.app
         (Term.proj `le_sub_iff_add_le' "." (fieldIdx "1"))
         [(«term_<|_» `floor_le "<|" («term_-_» (Term.app `f [`x]) "-" `x))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `le_translation_number_of_add_int_le [`f])
       "<|"
       (Term.app
        (Term.proj `le_sub_iff_add_le' "." (fieldIdx "1"))
        [(«term_<|_» `floor_le "<|" («term_-_» (Term.app `f [`x]) "-" `x))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `le_sub_iff_add_le' "." (fieldIdx "1"))
       [(«term_<|_» `floor_le "<|" («term_-_» (Term.app `f [`x]) "-" `x))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `floor_le "<|" («term_-_» (Term.app `f [`x]) "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `f [`x]) "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `floor_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `floor_le "<|" («term_-_» (Term.app `f [`x]) "-" `x))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `le_sub_iff_add_le' "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `le_sub_iff_add_le'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `le_translation_number_of_add_int_le [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_translation_number_of_add_int_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (coeNotation
        "↑"
        (Int.Algebra.Order.Floor.«term⌊_⌋» "⌊" («term_-_» (Term.app `f [`x]) "-" `x) "⌋"))
       "≤"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  floor_sub_le_translation_number
  ( x : ℝ ) : ↑ ⌊ f x - x ⌋ ≤ τ f
  := le_translation_number_of_add_int_le f <| le_sub_iff_add_le' . 1 floor_le <| f x - x
#align
  circle_deg1_lift.floor_sub_le_translation_number CircleDeg1Lift.floor_sub_le_translation_number

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_le_ceil_sub [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "≤"
         (Int.Algebra.Order.Floor.«term⌈_⌉» "⌈" («term_-_» (Term.app `f [`x]) "-" `x) "⌉"))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.app `translation_number_le_of_le_add_int [`f])
        "<|"
        (Term.app
         (Term.proj `sub_le_iff_le_add' "." (fieldIdx "1"))
         [(«term_<|_» `le_ceil "<|" («term_-_» (Term.app `f [`x]) "-" `x))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `translation_number_le_of_le_add_int [`f])
       "<|"
       (Term.app
        (Term.proj `sub_le_iff_le_add' "." (fieldIdx "1"))
        [(«term_<|_» `le_ceil "<|" («term_-_» (Term.app `f [`x]) "-" `x))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `sub_le_iff_le_add' "." (fieldIdx "1"))
       [(«term_<|_» `le_ceil "<|" («term_-_» (Term.app `f [`x]) "-" `x))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `le_ceil "<|" («term_-_» (Term.app `f [`x]) "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `f [`x]) "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `le_ceil
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `le_ceil "<|" («term_-_» (Term.app `f [`x]) "-" `x))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `sub_le_iff_le_add' "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sub_le_iff_le_add'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `translation_number_le_of_le_add_int [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `translation_number_le_of_le_add_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "≤"
       (Int.Algebra.Order.Floor.«term⌈_⌉» "⌈" («term_-_» (Term.app `f [`x]) "-" `x) "⌉"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Int.Algebra.Order.Floor.«term⌈_⌉» "⌈" («term_-_» (Term.app `f [`x]) "-" `x) "⌉")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `f [`x]) "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_le_ceil_sub
  ( x : ℝ ) : τ f ≤ ⌈ f x - x ⌉
  := translation_number_le_of_le_add_int f <| sub_le_iff_le_add' . 1 le_ceil <| f x - x
#align circle_deg1_lift.translation_number_le_ceil_sub CircleDeg1Lift.translation_number_le_ceil_sub

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map_lt_of_translation_number_lt_int [])
      (Command.declSig
       [(Term.implicitBinder "{" [`n] [":" (termℤ "ℤ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f])
           "<"
           `n)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec ":" («term_<_» (Term.app `f [`x]) "<" («term_+_» `x "+" `n))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `not_le "." (fieldIdx "1"))
        "<|"
        («term_<|_»
         (Term.app `mt [(Term.proj `f "." `le_translation_number_of_add_int_le)])
         "<|"
         (Term.app (Term.proj `not_le "." (fieldIdx "2")) [`h])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `not_le "." (fieldIdx "1"))
       "<|"
       («term_<|_»
        (Term.app `mt [(Term.proj `f "." `le_translation_number_of_add_int_le)])
        "<|"
        (Term.app (Term.proj `not_le "." (fieldIdx "2")) [`h])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `mt [(Term.proj `f "." `le_translation_number_of_add_int_le)])
       "<|"
       (Term.app (Term.proj `not_le "." (fieldIdx "2")) [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `not_le "." (fieldIdx "2")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `not_le "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `mt [(Term.proj `f "." `le_translation_number_of_add_int_le)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `le_translation_number_of_add_int_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `not_le "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_» (Term.app `f [`x]) "<" («term_+_» `x "+" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `x "+" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "<"
       `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  map_lt_of_translation_number_lt_int
  { n : ℤ } ( h : τ f < n ) ( x : ℝ ) : f x < x + n
  := not_le . 1 <| mt f . le_translation_number_of_add_int_le <| not_le . 2 h
#align
  circle_deg1_lift.map_lt_of_translation_number_lt_int CircleDeg1Lift.map_lt_of_translation_number_lt_int

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map_lt_of_translation_number_lt_nat [])
      (Command.declSig
       [(Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f])
           "<"
           `n)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec ":" («term_<_» (Term.app `f [`x]) "<" («term_+_» `x "+" `n))))
      (Command.declValSimple
       ":="
       (Term.app (Term.explicit "@" `map_lt_of_translation_number_lt_int) [`f `n `h `x])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `map_lt_of_translation_number_lt_int) [`f `n `h `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `map_lt_of_translation_number_lt_int)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_lt_of_translation_number_lt_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_» (Term.app `f [`x]) "<" («term_+_» `x "+" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `x "+" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "<"
       `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  map_lt_of_translation_number_lt_nat
  { n : ℕ } ( h : τ f < n ) ( x : ℝ ) : f x < x + n
  := @ map_lt_of_translation_number_lt_int f n h x
#align
  circle_deg1_lift.map_lt_of_translation_number_lt_nat CircleDeg1Lift.map_lt_of_translation_number_lt_nat

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map_lt_add_floor_translation_number_add_one [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         (Term.app `f [`x])
         "<"
         («term_+_»
          («term_+_»
           `x
           "+"
           (Int.Algebra.Order.Floor.«term⌊_⌋»
            "⌊"
            (Term.app
             (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
             [`f])
            "⌋"))
          "+"
          (num "1")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_assoc)] "]") [])
           []
           (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `map_lt_of_translation_number_lt_int
             [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
           []
           (Tactic.NormCast.pushCast "push_cast" [] [] [] [] [])
           []
           (Tactic.exact "exact" (Term.app `lt_floor_add_one [(Term.hole "_")]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_assoc)] "]") [])
          []
          (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `map_lt_of_translation_number_lt_int
            [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          []
          (Tactic.NormCast.pushCast "push_cast" [] [] [] [] [])
          []
          (Tactic.exact "exact" (Term.app `lt_floor_add_one [(Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `lt_floor_add_one [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_floor_add_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_floor_add_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.pushCast "push_cast" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `map_lt_of_translation_number_lt_int
        [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `map_lt_of_translation_number_lt_int
       [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_lt_of_translation_number_lt_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_assoc)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       (Term.app `f [`x])
       "<"
       («term_+_»
        («term_+_»
         `x
         "+"
         (Int.Algebra.Order.Floor.«term⌊_⌋»
          "⌊"
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [`f])
          "⌋"))
        "+"
        (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_+_»
        `x
        "+"
        (Int.Algebra.Order.Floor.«term⌊_⌋»
         "⌊"
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "⌋"))
       "+"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       `x
       "+"
       (Int.Algebra.Order.Floor.«term⌊_⌋»
        "⌊"
        (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
        "⌋"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Int.Algebra.Order.Floor.«term⌊_⌋»
       "⌊"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "⌋")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  map_lt_add_floor_translation_number_add_one
  ( x : ℝ ) : f x < x + ⌊ τ f ⌋ + 1
  :=
    by
      rw [ add_assoc ]
        norm_cast
        refine' map_lt_of_translation_number_lt_int _ _ _
        push_cast
        exact lt_floor_add_one _
#align
  circle_deg1_lift.map_lt_add_floor_translation_number_add_one CircleDeg1Lift.map_lt_add_floor_translation_number_add_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map_lt_add_translation_number_add_one [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         (Term.app `f [`x])
         "<"
         («term_+_»
          («term_+_»
           `x
           "+"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))
          "+"
          (num "1")))))
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         («term_<_»
          (Term.app `f [`x])
          "<"
          («term_+_»
           («term_+_»
            `x
            "+"
            (Int.Algebra.Order.Floor.«term⌊_⌋»
             "⌊"
             (Term.app
              (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
              [`f])
             "⌋"))
           "+"
           (num "1")))
         ":="
         (Term.app (Term.proj `f "." `map_lt_add_floor_translation_number_add_one) [`x]))
        [(calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           («term_+_»
            («term_+_»
             `x
             "+"
             (Term.app
              (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
              [`f]))
            "+"
            (num "1")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.mono "mono" ["*"] [] [] [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `floor_le
                [(Term.app
                  (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                  [`f])]))]))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_<_»
         (Term.app `f [`x])
         "<"
         («term_+_»
          («term_+_»
           `x
           "+"
           (Int.Algebra.Order.Floor.«term⌊_⌋»
            "⌊"
            (Term.app
             (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
             [`f])
            "⌋"))
          "+"
          (num "1")))
        ":="
        (Term.app (Term.proj `f "." `map_lt_add_floor_translation_number_add_one) [`x]))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           («term_+_»
            `x
            "+"
            (Term.app
             (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
             [`f]))
           "+"
           (num "1")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.mono "mono" ["*"] [] [] [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `floor_le
               [(Term.app
                 (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                 [`f])]))]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.mono "mono" ["*"] [] [] [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `floor_le
            [(Term.app
              (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
              [`f])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `floor_le
        [(Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `floor_le
       [(Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  map_lt_add_translation_number_add_one
  ( x : ℝ ) : f x < x + τ f + 1
  :=
    calc
      f x < x + ⌊ τ f ⌋ + 1 := f . map_lt_add_floor_translation_number_add_one x
      _ ≤ x + τ f + 1 := by mono * exact floor_le τ f
#align
  circle_deg1_lift.map_lt_add_translation_number_add_one CircleDeg1Lift.map_lt_add_translation_number_add_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_map_of_int_lt_translation_number [])
      (Command.declSig
       [(Term.implicitBinder "{" [`n] [":" (termℤ "ℤ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (coeNotation "↑" `n)
           "<"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec ":" («term_<_» («term_+_» `x "+" `n) "<" (Term.app `f [`x]))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `not_le "." (fieldIdx "1"))
        "<|"
        («term_<|_»
         (Term.app `mt [(Term.proj `f "." `translation_number_le_of_le_add_int)])
         "<|"
         (Term.app (Term.proj `not_le "." (fieldIdx "2")) [`h])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `not_le "." (fieldIdx "1"))
       "<|"
       («term_<|_»
        (Term.app `mt [(Term.proj `f "." `translation_number_le_of_le_add_int)])
        "<|"
        (Term.app (Term.proj `not_le "." (fieldIdx "2")) [`h])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `mt [(Term.proj `f "." `translation_number_le_of_le_add_int)])
       "<|"
       (Term.app (Term.proj `not_le "." (fieldIdx "2")) [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `not_le "." (fieldIdx "2")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `not_le "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `mt [(Term.proj `f "." `translation_number_le_of_le_add_int)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `translation_number_le_of_le_add_int)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `not_le "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_» («term_+_» `x "+" `n) "<" (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_» `x "+" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (coeNotation "↑" `n)
       "<"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_map_of_int_lt_translation_number
  { n : ℤ } ( h : ↑ n < τ f ) ( x : ℝ ) : x + n < f x
  := not_le . 1 <| mt f . translation_number_le_of_le_add_int <| not_le . 2 h
#align
  circle_deg1_lift.lt_map_of_int_lt_translation_number CircleDeg1Lift.lt_map_of_int_lt_translation_number

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_map_of_nat_lt_translation_number [])
      (Command.declSig
       [(Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (coeNotation "↑" `n)
           "<"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
       (Term.typeSpec ":" («term_<_» («term_+_» `x "+" `n) "<" (Term.app `f [`x]))))
      (Command.declValSimple
       ":="
       (Term.app (Term.explicit "@" `lt_map_of_int_lt_translation_number) [`f `n `h `x])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `lt_map_of_int_lt_translation_number) [`f `n `h `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `lt_map_of_int_lt_translation_number)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_map_of_int_lt_translation_number
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_» («term_+_» `x "+" `n) "<" (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_» `x "+" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (coeNotation "↑" `n)
       "<"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_map_of_nat_lt_translation_number
  { n : ℕ } ( h : ↑ n < τ f ) ( x : ℝ ) : x + n < f x
  := @ lt_map_of_int_lt_translation_number f n h x
#align
  circle_deg1_lift.lt_map_of_nat_lt_translation_number CircleDeg1Lift.lt_map_of_nat_lt_translation_number

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `f^n x - x`, `n > 0`, is an integer number `m` for some point `x`, then\n`τ f = m / n`. On the circle this means that a map with a periodic orbit has\na rational rotation number. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_of_map_pow_eq_add_int [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.implicitBinder "{" [`m] [":" (termℤ "ℤ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_=_» (Term.app («term_^_» `f "^" `n) [`x]) "=" («term_+_» `x "+" `m))]
         []
         ")")
        (Term.explicitBinder "(" [`hn] [":" («term_<_» (num "0") "<" `n)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "="
         («term_/_» `m "/" `n))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               (Term.proj («term_^_» `f "^" `n) "." `translation_number_of_eq_add_int)
               [`h]))))
           []
           (Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `translation_number_pow)
              ","
              (Tactic.rwRule [] `mul_comm)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_div_iff)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj `Nat.cast_ne_zero "." (fieldIdx "2"))
             [(Term.app `ne_of_gt [`hn])]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              (Term.proj («term_^_» `f "^" `n) "." `translation_number_of_eq_add_int)
              [`h]))))
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `translation_number_pow)
             ","
             (Tactic.rwRule [] `mul_comm)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_div_iff)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj `Nat.cast_ne_zero "." (fieldIdx "2"))
            [(Term.app `ne_of_gt [`hn])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app (Term.proj `Nat.cast_ne_zero "." (fieldIdx "2")) [(Term.app `ne_of_gt [`hn])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Nat.cast_ne_zero "." (fieldIdx "2")) [(Term.app `ne_of_gt [`hn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_of_gt [`hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ne_of_gt [`hn]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Nat.cast_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Nat.cast_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `translation_number_pow)
         ","
         (Tactic.rwRule [] `mul_comm)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_div_iff)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_div_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `translation_number_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app (Term.proj («term_^_» `f "^" `n) "." `translation_number_of_eq_add_int) [`h]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj («term_^_» `f "^" `n) "." `translation_number_of_eq_add_int) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_^_» `f "^" `n) "." `translation_number_of_eq_add_int)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `f "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `f "^" `n) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "="
       («term_/_» `m "/" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `m "/" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `f^n x - x`, `n > 0`, is an integer number `m` for some point `x`, then
    `τ f = m / n`. On the circle this means that a map with a periodic orbit has
    a rational rotation number. -/
  theorem
    translation_number_of_map_pow_eq_add_int
    { x : ℝ } { n : ℕ } { m : ℤ } ( h : f ^ n x = x + m ) ( hn : 0 < n ) : τ f = m / n
    :=
      by
        have := f ^ n . translation_number_of_eq_add_int h
          rwa [ translation_number_pow , mul_comm , ← eq_div_iff ] at this
          exact Nat.cast_ne_zero . 2 ne_of_gt hn
#align
  circle_deg1_lift.translation_number_of_map_pow_eq_add_int CircleDeg1Lift.translation_number_of_map_pow_eq_add_int

/-- If a predicate depends only on `f x - x` and holds for all `0 ≤ x ≤ 1`,
then it holds for all `x`. -/
theorem forall_map_sub_of_Icc (P : ℝ → Prop) (h : ∀ x ∈ Icc (0 : ℝ) 1, P (f x - x)) (x : ℝ) :
    P (f x - x) :=
  f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩
#align circle_deg1_lift.forall_map_sub_of_Icc CircleDeg1Lift.forall_map_sub_of_Icc

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_lt_of_forall_lt_add [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `Continuous [`f])] [] ")")
        (Term.implicitBinder "{" [`z] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`hz]
         [":"
          (Term.forall "∀" [`x] [] "," («term_<_» (Term.app `f [`x]) "<" («term_+_» `x "+" `z)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
         "<"
         `z)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xmem)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [])]
                "⟩")])]
            [":"
             (Std.ExtendedBinder.«term∃__,_»
              "∃"
              (Lean.binderIdent `x)
              («binderTerm∈_»
               "∈"
               (Term.app
                `Icc
                [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 (num "1")]))
              ","
              (Std.ExtendedBinder.«term∀__,_»
               "∀"
               (Lean.binderIdent `y)
               («binderTerm∈_»
                "∈"
                (Term.app
                 `Icc
                 [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  (num "1")]))
               ","
               («term_≤_»
                («term_-_» (Term.app `f [`y]) "-" `y)
                "≤"
                («term_-_» (Term.app `f [`x]) "-" `x))))]
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `is_compact_Icc.exists_forall_ge
             [(Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
              (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)]))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `lt_of_le_of_lt
             [(Term.hole "_")
              («term_<|_»
               (Term.proj `sub_lt_iff_lt_add' "." (fieldIdx "2"))
               "<|"
               (Term.app `hz [`x]))]))
           []
           (Tactic.apply "apply" `translation_number_le_of_le_add)
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_le_iff_le_add')] "]"]
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `f.forall_map_sub_of_Icc
             [(Term.fun
               "fun"
               (Term.basicFun
                [`a]
                []
                "=>"
                («term_≤_» `a "≤" («term_-_» (Term.app `f [`x]) "-" `x))))
              `hx]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xmem)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                 [])]
               "⟩")])]
           [":"
            (Std.ExtendedBinder.«term∃__,_»
             "∃"
             (Lean.binderIdent `x)
             («binderTerm∈_»
              "∈"
              (Term.app
               `Icc
               [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                (num "1")]))
             ","
             (Std.ExtendedBinder.«term∀__,_»
              "∀"
              (Lean.binderIdent `y)
              («binderTerm∈_»
               "∈"
               (Term.app
                `Icc
                [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 (num "1")]))
              ","
              («term_≤_»
               («term_-_» (Term.app `f [`y]) "-" `y)
               "≤"
               («term_-_» (Term.app `f [`x]) "-" `x))))]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `is_compact_Icc.exists_forall_ge
            [(Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
             (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)]))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `lt_of_le_of_lt
            [(Term.hole "_")
             («term_<|_»
              (Term.proj `sub_lt_iff_lt_add' "." (fieldIdx "2"))
              "<|"
              (Term.app `hz [`x]))]))
          []
          (Tactic.apply "apply" `translation_number_le_of_le_add)
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_le_iff_le_add')] "]"]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `f.forall_map_sub_of_Icc
            [(Term.fun
              "fun"
              (Term.basicFun [`a] [] "=>" («term_≤_» `a "≤" («term_-_» (Term.app `f [`x]) "-" `x))))
             `hx]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `f.forall_map_sub_of_Icc
        [(Term.fun
          "fun"
          (Term.basicFun [`a] [] "=>" («term_≤_» `a "≤" («term_-_» (Term.app `f [`x]) "-" `x))))
         `hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `f.forall_map_sub_of_Icc
       [(Term.fun
         "fun"
         (Term.basicFun [`a] [] "=>" («term_≤_» `a "≤" («term_-_» (Term.app `f [`x]) "-" `x))))
        `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun [`a] [] "=>" («term_≤_» `a "≤" («term_-_» (Term.app `f [`x]) "-" `x))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» `a "≤" («term_-_» (Term.app `f [`x]) "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `f [`x]) "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun [`a] [] "=>" («term_≤_» `a "≤" («term_-_» (Term.app `f [`x]) "-" `x))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.forall_map_sub_of_Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_le_iff_le_add')] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_le_iff_le_add'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `translation_number_le_of_le_add)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `translation_number_le_of_le_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `lt_of_le_of_lt
        [(Term.hole "_")
         («term_<|_» (Term.proj `sub_lt_iff_lt_add' "." (fieldIdx "2")) "<|" (Term.app `hz [`x]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_of_le_of_lt
       [(Term.hole "_")
        («term_<|_» (Term.proj `sub_lt_iff_lt_add' "." (fieldIdx "2")) "<|" (Term.app `hz [`x]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» (Term.proj `sub_lt_iff_lt_add' "." (fieldIdx "2")) "<|" (Term.app `hz [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hz [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `sub_lt_iff_lt_add' "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `sub_lt_iff_lt_add'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.proj `sub_lt_iff_lt_add' "." (fieldIdx "2")) "<|" (Term.app `hz [`x]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_of_le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `is_compact_Icc.exists_forall_ge
        [(Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
         (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_compact_Icc.exists_forall_ge
       [(Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
        (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf.sub [`continuous_id])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_id
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.sub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf.sub [`continuous_id]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `nonempty_Icc "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `nonempty_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_Icc.exists_forall_ge
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xmem)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
             [])]
           "⟩")])]
       [":"
        (Std.ExtendedBinder.«term∃__,_»
         "∃"
         (Lean.binderIdent `x)
         («binderTerm∈_»
          "∈"
          (Term.app
           `Icc
           [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
         ","
         (Std.ExtendedBinder.«term∀__,_»
          "∀"
          (Lean.binderIdent `y)
          («binderTerm∈_»
           "∈"
           (Term.app
            `Icc
            [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
          ","
          («term_≤_»
           («term_-_» (Term.app `f [`y]) "-" `y)
           "≤"
           («term_-_» (Term.app `f [`x]) "-" `x))))]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∃__,_»
       "∃"
       (Lean.binderIdent `x)
       («binderTerm∈_»
        "∈"
        (Term.app
         `Icc
         [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
       ","
       (Std.ExtendedBinder.«term∀__,_»
        "∀"
        (Lean.binderIdent `y)
        («binderTerm∈_»
         "∈"
         (Term.app
          `Icc
          [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
        ","
        («term_≤_»
         («term_-_» (Term.app `f [`y]) "-" `y)
         "≤"
         («term_-_» (Term.app `f [`x]) "-" `x))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `y)
       («binderTerm∈_»
        "∈"
        (Term.app
         `Icc
         [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
       ","
       («term_≤_» («term_-_» (Term.app `f [`y]) "-" `y) "≤" («term_-_» (Term.app `f [`x]) "-" `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» («term_-_» (Term.app `f [`y]) "-" `y) "≤" («term_-_» (Term.app `f [`x]) "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `f [`x]) "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_-_» (Term.app `f [`y]) "-" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "<"
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_lt_of_forall_lt_add
  ( hf : Continuous f ) { z : ℝ } ( hz : ∀ x , f x < x + z ) : τ f < z
  :=
    by
      obtain ⟨ x , xmem , hx ⟩ : ∃ x ∈ Icc ( 0 : ℝ ) 1 , ∀ y ∈ Icc ( 0 : ℝ ) 1 , f y - y ≤ f x - x
        exact
          is_compact_Icc.exists_forall_ge
            nonempty_Icc . 2 zero_le_one hf.sub continuous_id . ContinuousOn
        refine' lt_of_le_of_lt _ sub_lt_iff_lt_add' . 2 <| hz x
        apply translation_number_le_of_le_add
        simp only [ ← sub_le_iff_le_add' ]
        exact f.forall_map_sub_of_Icc fun a => a ≤ f x - x hx
#align
  circle_deg1_lift.translation_number_lt_of_forall_lt_add CircleDeg1Lift.translation_number_lt_of_forall_lt_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_translation_number_of_forall_add_lt [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `Continuous [`f])] [] ")")
        (Term.implicitBinder "{" [`z] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`hz]
         [":"
          (Term.forall "∀" [`x] [] "," («term_<_» («term_+_» `x "+" `z) "<" (Term.app `f [`x])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         `z
         "<"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xmem)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [])]
                "⟩")])]
            [":"
             (Std.ExtendedBinder.«term∃__,_»
              "∃"
              (Lean.binderIdent `x)
              («binderTerm∈_»
               "∈"
               (Term.app
                `Icc
                [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 (num "1")]))
              ","
              (Std.ExtendedBinder.«term∀__,_»
               "∀"
               (Lean.binderIdent `y)
               («binderTerm∈_»
                "∈"
                (Term.app
                 `Icc
                 [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  (num "1")]))
               ","
               («term_≤_»
                («term_-_» (Term.app `f [`x]) "-" `x)
                "≤"
                («term_-_» (Term.app `f [`y]) "-" `y))))]
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `is_compact_Icc.exists_forall_le
             [(Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
              (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)]))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `lt_of_lt_of_le
             [(«term_<|_»
               (Term.proj `lt_sub_iff_add_lt' "." (fieldIdx "2"))
               "<|"
               (Term.app `hz [`x]))
              (Term.hole "_")]))
           []
           (Tactic.apply "apply" `le_translation_number_of_add_le)
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `le_sub_iff_add_le')] "]"]
            [])
           []
           (Tactic.exact "exact" (Term.app `f.forall_map_sub_of_Icc [(Term.hole "_") `hx]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xmem)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                 [])]
               "⟩")])]
           [":"
            (Std.ExtendedBinder.«term∃__,_»
             "∃"
             (Lean.binderIdent `x)
             («binderTerm∈_»
              "∈"
              (Term.app
               `Icc
               [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                (num "1")]))
             ","
             (Std.ExtendedBinder.«term∀__,_»
              "∀"
              (Lean.binderIdent `y)
              («binderTerm∈_»
               "∈"
               (Term.app
                `Icc
                [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 (num "1")]))
              ","
              («term_≤_»
               («term_-_» (Term.app `f [`x]) "-" `x)
               "≤"
               («term_-_» (Term.app `f [`y]) "-" `y))))]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `is_compact_Icc.exists_forall_le
            [(Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
             (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)]))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `lt_of_lt_of_le
            [(«term_<|_»
              (Term.proj `lt_sub_iff_add_lt' "." (fieldIdx "2"))
              "<|"
              (Term.app `hz [`x]))
             (Term.hole "_")]))
          []
          (Tactic.apply "apply" `le_translation_number_of_add_le)
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `le_sub_iff_add_le')] "]"]
           [])
          []
          (Tactic.exact "exact" (Term.app `f.forall_map_sub_of_Icc [(Term.hole "_") `hx]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `f.forall_map_sub_of_Icc [(Term.hole "_") `hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.forall_map_sub_of_Icc [(Term.hole "_") `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.forall_map_sub_of_Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `le_sub_iff_add_le')] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_sub_iff_add_le'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `le_translation_number_of_add_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_translation_number_of_add_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `lt_of_lt_of_le
        [(«term_<|_» (Term.proj `lt_sub_iff_add_lt' "." (fieldIdx "2")) "<|" (Term.app `hz [`x]))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_of_lt_of_le
       [(«term_<|_» (Term.proj `lt_sub_iff_add_lt' "." (fieldIdx "2")) "<|" (Term.app `hz [`x]))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_<|_» (Term.proj `lt_sub_iff_add_lt' "." (fieldIdx "2")) "<|" (Term.app `hz [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hz [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `lt_sub_iff_add_lt' "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `lt_sub_iff_add_lt'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» (Term.proj `lt_sub_iff_add_lt' "." (fieldIdx "2")) "<|" (Term.app `hz [`x]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_of_lt_of_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `is_compact_Icc.exists_forall_le
        [(Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
         (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_compact_Icc.exists_forall_le
       [(Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
        (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `hf.sub [`continuous_id]) "." `ContinuousOn)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf.sub [`continuous_id])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_id
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.sub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf.sub [`continuous_id]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `nonempty_Icc "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `nonempty_Icc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `nonempty_Icc "." (fieldIdx "2")) [`zero_le_one])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_compact_Icc.exists_forall_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xmem)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
             [])]
           "⟩")])]
       [":"
        (Std.ExtendedBinder.«term∃__,_»
         "∃"
         (Lean.binderIdent `x)
         («binderTerm∈_»
          "∈"
          (Term.app
           `Icc
           [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
         ","
         (Std.ExtendedBinder.«term∀__,_»
          "∀"
          (Lean.binderIdent `y)
          («binderTerm∈_»
           "∈"
           (Term.app
            `Icc
            [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
          ","
          («term_≤_»
           («term_-_» (Term.app `f [`x]) "-" `x)
           "≤"
           («term_-_» (Term.app `f [`y]) "-" `y))))]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∃__,_»
       "∃"
       (Lean.binderIdent `x)
       («binderTerm∈_»
        "∈"
        (Term.app
         `Icc
         [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
       ","
       (Std.ExtendedBinder.«term∀__,_»
        "∀"
        (Lean.binderIdent `y)
        («binderTerm∈_»
         "∈"
         (Term.app
          `Icc
          [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
        ","
        («term_≤_»
         («term_-_» (Term.app `f [`x]) "-" `x)
         "≤"
         («term_-_» (Term.app `f [`y]) "-" `y))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `y)
       («binderTerm∈_»
        "∈"
        (Term.app
         `Icc
         [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")]))
       ","
       («term_≤_» («term_-_» (Term.app `f [`x]) "-" `x) "≤" («term_-_» (Term.app `f [`y]) "-" `y)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» («term_-_» (Term.app `f [`x]) "-" `x) "≤" («term_-_» (Term.app `f [`y]) "-" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `f [`y]) "-" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_-_» (Term.app `f [`x]) "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Icc
       [(Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Icc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       `z
       "<"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_translation_number_of_forall_add_lt
  ( hf : Continuous f ) { z : ℝ } ( hz : ∀ x , x + z < f x ) : z < τ f
  :=
    by
      obtain ⟨ x , xmem , hx ⟩ : ∃ x ∈ Icc ( 0 : ℝ ) 1 , ∀ y ∈ Icc ( 0 : ℝ ) 1 , f x - x ≤ f y - y
        exact
          is_compact_Icc.exists_forall_le
            nonempty_Icc . 2 zero_le_one hf.sub continuous_id . ContinuousOn
        refine' lt_of_lt_of_le lt_sub_iff_add_lt' . 2 <| hz x _
        apply le_translation_number_of_add_le
        simp only [ ← le_sub_iff_add_le' ]
        exact f.forall_map_sub_of_Icc _ hx
#align
  circle_deg1_lift.lt_translation_number_of_forall_add_lt CircleDeg1Lift.lt_translation_number_of_forall_add_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `f` is a continuous monotone map `ℝ → ℝ`, `f (x + 1) = f x + 1`, then there exists `x`\nsuch that `f x = x + τ f`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_eq_add_translation_number [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `Continuous [`f])] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         ","
         («term_=_»
          (Term.app `f [`x])
          "="
          («term_+_»
           `x
           "+"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
              ","
              («term_≤_» (Term.app `f [`x]) "≤" («term_+_» `x "+" `f.translation_number)))]
            [":="
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(byContra' "by_contra'" [(Lean.binderIdent `H)] [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `lt_irrefl
                    [(Term.hole "_")
                     (Term.app `f.lt_translation_number_of_forall_add_lt [`hf `H])]))])))]])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
              ","
              («term_≤_»
               («term_+_»
                `x
                "+"
                (Term.app
                 (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                 [`f]))
               "≤"
               (Term.app `f [`x])))]
            [":="
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(byContra' "by_contra'" [(Lean.binderIdent `H)] [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `lt_irrefl
                    [(Term.hole "_")
                     (Term.app `f.translation_number_lt_of_forall_lt_add [`hf `H])]))])))]])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `intermediate_value_univ₂
             [`hf (Term.app `continuous_id.add [`continuous_const]) `ha `hb]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `a)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `ha)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             ","
             («term_≤_» (Term.app `f [`x]) "≤" («term_+_» `x "+" `f.translation_number)))]
           [":="
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(byContra' "by_contra'" [(Lean.binderIdent `H)] [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `lt_irrefl
                   [(Term.hole "_")
                    (Term.app `f.lt_translation_number_of_forall_add_lt [`hf `H])]))])))]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
             ","
             («term_≤_»
              («term_+_»
               `x
               "+"
               (Term.app
                (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                [`f]))
              "≤"
              (Term.app `f [`x])))]
           [":="
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(byContra' "by_contra'" [(Lean.binderIdent `H)] [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `lt_irrefl
                   [(Term.hole "_")
                    (Term.app `f.translation_number_lt_of_forall_lt_add [`hf `H])]))])))]])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `intermediate_value_univ₂
            [`hf (Term.app `continuous_id.add [`continuous_const]) `ha `hb]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `intermediate_value_univ₂
        [`hf (Term.app `continuous_id.add [`continuous_const]) `ha `hb]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `intermediate_value_univ₂
       [`hf (Term.app `continuous_id.add [`continuous_const]) `ha `hb])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_id.add [`continuous_const])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_const
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_id.add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_id.add [`continuous_const])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `intermediate_value_univ₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
         ","
         («term_≤_»
          («term_+_»
           `x
           "+"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f]))
          "≤"
          (Term.app `f [`x])))]
       [":="
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(byContra' "by_contra'" [(Lean.binderIdent `H)] [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `lt_irrefl
               [(Term.hole "_")
                (Term.app `f.translation_number_lt_of_forall_lt_add [`hf `H])]))])))]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(byContra' "by_contra'" [(Lean.binderIdent `H)] [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `lt_irrefl
            [(Term.hole "_") (Term.app `f.translation_number_lt_of_forall_lt_add [`hf `H])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `lt_irrefl
        [(Term.hole "_") (Term.app `f.translation_number_lt_of_forall_lt_add [`hf `H])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_irrefl
       [(Term.hole "_") (Term.app `f.translation_number_lt_of_forall_lt_add [`hf `H])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.translation_number_lt_of_forall_lt_add [`hf `H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.translation_number_lt_of_forall_lt_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `f.translation_number_lt_of_forall_lt_add [`hf `H])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_irrefl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (byContra' "by_contra'" [(Lean.binderIdent `H)] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       ","
       («term_≤_»
        («term_+_»
         `x
         "+"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [`f]))
        "≤"
        (Term.app `f [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_+_»
        `x
        "+"
        (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
       "≤"
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_+_»
       `x
       "+"
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `f` is a continuous monotone map `ℝ → ℝ`, `f (x + 1) = f x + 1`, then there exists `x`
    such that `f x = x + τ f`. -/
  theorem
    exists_eq_add_translation_number
    ( hf : Continuous f ) : ∃ x , f x = x + τ f
    :=
      by
        obtain
            ⟨ a , ha ⟩
            : ∃ x , f x ≤ x + f.translation_number
            := by by_contra' H exact lt_irrefl _ f.lt_translation_number_of_forall_add_lt hf H
          obtain
            ⟨ b , hb ⟩
            : ∃ x , x + τ f ≤ f x
            := by by_contra' H exact lt_irrefl _ f.translation_number_lt_of_forall_lt_add hf H
          exact intermediate_value_univ₂ hf continuous_id.add continuous_const ha hb
#align
  circle_deg1_lift.exists_eq_add_translation_number CircleDeg1Lift.exists_eq_add_translation_number

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_eq_int_iff [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `Continuous [`f])] [] ")")
        (Term.implicitBinder "{" [`m] [":" (termℤ "ℤ")] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [`f])
          "="
          `m)
         "↔"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          ","
          («term_=_» (Term.app `f [`x]) "=" («term_+_» `x "+" `m))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.subst `h "▸" [(Term.app `f.exists_eq_add_translation_number [`hf])])))
              ","
              (Term.hole "_")]
             "⟩"))
           []
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                 [])]
               "⟩"))]
            [])
           []
           (Tactic.exact "exact" (Term.app `f.translation_number_of_eq_add_int [`hx]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.subst `h "▸" [(Term.app `f.exists_eq_add_translation_number [`hf])])))
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.exact "exact" (Term.app `f.translation_number_of_eq_add_int [`hx]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `f.translation_number_of_eq_add_int [`hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.translation_number_of_eq_add_int [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.translation_number_of_eq_add_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.subst `h "▸" [(Term.app `f.exists_eq_add_translation_number [`hf])])))
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.subst `h "▸" [(Term.app `f.exists_eq_add_translation_number [`hf])])))
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.subst `h "▸" [(Term.app `f.exists_eq_add_translation_number [`hf])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst `h "▸" [(Term.app `f.exists_eq_add_translation_number [`hf])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.exists_eq_add_translation_number [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.exists_eq_add_translation_number
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_»
        (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
        "="
        `m)
       "↔"
       («term∃_,_»
        "∃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        ","
        («term_=_» (Term.app `f [`x]) "=" («term_+_» `x "+" `m))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       ","
       («term_=_» (Term.app `f [`x]) "=" («term_+_» `x "+" `m)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `f [`x]) "=" («term_+_» `x "+" `m))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `x "+" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "="
       `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_eq_int_iff
  ( hf : Continuous f ) { m : ℤ } : τ f = m ↔ ∃ x , f x = x + m
  :=
    by
      refine' ⟨ fun h => h ▸ f.exists_eq_add_translation_number hf , _ ⟩
        rintro ⟨ x , hx ⟩
        exact f.translation_number_of_eq_add_int hx
#align circle_deg1_lift.translation_number_eq_int_iff CircleDeg1Lift.translation_number_eq_int_iff

theorem continuous_pow (hf : Continuous f) (n : ℕ) : Continuous ⇑(f ^ n : CircleDeg1Lift) :=
  by
  rw [coe_pow]
  exact hf.iterate n
#align circle_deg1_lift.continuous_pow CircleDeg1Lift.continuous_pow

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `translation_number_eq_rat_iff [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `Continuous [`f])] [] ")")
        (Term.implicitBinder "{" [`m] [":" (termℤ "ℤ")] "}")
        (Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`hn] [":" («term_<_» (num "0") "<" `n)] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [`f])
          "="
          («term_/_» `m "/" `n))
         "↔"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
          ","
          («term_=_» (Term.app («term_^_» `f "^" `n) [`x]) "=" («term_+_» `x "+" `m))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.seq_focus
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `eq_div_iff)
               ","
               (Tactic.rwRule [] `mul_comm)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `translation_number_pow)]
              "]")
             [])
            "<;>"
            "["
            [(Tactic.skip "skip")
             ","
             (Tactic.exact
              "exact"
              (Term.app `ne_of_gt [(Term.app (Term.proj `Nat.cast_pos "." (fieldIdx "2")) [`hn])]))]
            "]")
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj («term_^_» `f "^" `n) "." `translation_number_eq_int_iff)
             [(Term.app `f.continuous_pow [`hf `n])]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.seq_focus
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `eq_div_iff)
              ","
              (Tactic.rwRule [] `mul_comm)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `translation_number_pow)]
             "]")
            [])
           "<;>"
           "["
           [(Tactic.skip "skip")
            ","
            (Tactic.exact
             "exact"
             (Term.app `ne_of_gt [(Term.app (Term.proj `Nat.cast_pos "." (fieldIdx "2")) [`hn])]))]
           "]")
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj («term_^_» `f "^" `n) "." `translation_number_eq_int_iff)
            [(Term.app `f.continuous_pow [`hf `n])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj («term_^_» `f "^" `n) "." `translation_number_eq_int_iff)
        [(Term.app `f.continuous_pow [`hf `n])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj («term_^_» `f "^" `n) "." `translation_number_eq_int_iff)
       [(Term.app `f.continuous_pow [`hf `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.continuous_pow [`hf `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.continuous_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `f.continuous_pow [`hf `n])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_^_» `f "^" `n) "." `translation_number_eq_int_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `f "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `f "^" `n) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.seq_focus
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `eq_div_iff)
          ","
          (Tactic.rwRule [] `mul_comm)
          ","
          (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `translation_number_pow)]
         "]")
        [])
       "<;>"
       "["
       [(Tactic.skip "skip")
        ","
        (Tactic.exact
         "exact"
         (Term.app `ne_of_gt [(Term.app (Term.proj `Nat.cast_pos "." (fieldIdx "2")) [`hn])]))]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `ne_of_gt [(Term.app (Term.proj `Nat.cast_pos "." (fieldIdx "2")) [`hn])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_of_gt [(Term.app (Term.proj `Nat.cast_pos "." (fieldIdx "2")) [`hn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Nat.cast_pos "." (fieldIdx "2")) [`hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Nat.cast_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Nat.cast_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `Nat.cast_pos "." (fieldIdx "2")) [`hn])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.skip "skip")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `eq_div_iff)
         ","
         (Tactic.rwRule [] `mul_comm)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `translation_number_pow)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `translation_number_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_div_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_»
        (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
        "="
        («term_/_» `m "/" `n))
       "↔"
       («term∃_,_»
        "∃"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
        ","
        («term_=_» (Term.app («term_^_» `f "^" `n) [`x]) "=" («term_+_» `x "+" `m))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `x)] []))
       ","
       («term_=_» (Term.app («term_^_» `f "^" `n) [`x]) "=" («term_+_» `x "+" `m)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app («term_^_» `f "^" `n) [`x]) "=" («term_+_» `x "+" `m))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `x "+" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app («term_^_» `f "^" `n) [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      («term_^_» `f "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `f "^" `n) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
       "="
       («term_/_» `m "/" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `m "/" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  translation_number_eq_rat_iff
  ( hf : Continuous f ) { m : ℤ } { n : ℕ } ( hn : 0 < n ) : τ f = m / n ↔ ∃ x , f ^ n x = x + m
  :=
    by
      rw [ eq_div_iff , mul_comm , ← translation_number_pow ]
          <;>
          [
          skip , exact ne_of_gt Nat.cast_pos . 2 hn
          ]
        exact f ^ n . translation_number_eq_int_iff f.continuous_pow hf n
#align circle_deg1_lift.translation_number_eq_rat_iff CircleDeg1Lift.translation_number_eq_rat_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Consider two actions `f₁ f₂ : G →* circle_deg1_lift` of a group on the real line by lifts of\norientation preserving circle homeomorphisms. Suppose that for each `g : G` the homeomorphisms\n`f₁ g` and `f₂ g` have equal rotation numbers. Then there exists `F : circle_deg1_lift`  such that\n`F * f₁ g = f₂ g * F` for all `g : G`.\n\nThis is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et\ncohomologie bornee][ghys87:groupes]. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `semiconj_of_group_action_of_forall_translation_number_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`G] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.instBinder "[" [] (Term.app `Group [`G]) "]")
        (Term.explicitBinder
         "("
         [`f₁ `f₂]
         [":" (Algebra.Hom.Group.«term_→*_» `G " →* " `CircleDeg1Lift)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [`g]
           []
           ","
           («term_=_»
            (Term.app
             (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
             [(Term.app `f₁ [`g])])
            "="
            (Term.app
             (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
             [(Term.app `f₂ [`g])])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `F)] [":" `CircleDeg1Lift]))
         ","
         (Term.forall
          "∀"
          [`g]
          []
          ","
          (Term.app `Semiconj [`F (Term.app `f₁ [`g]) (Term.app `f₂ [`g])])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`x]
                 []
                 ","
                 (Term.app
                  `BddAbove
                  [(Term.app
                    `range
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`g]
                       []
                       "=>"
                       (Term.app `f₂ [(«term_⁻¹» `g "⁻¹") (Term.app `f₁ [`g `x])])))])])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine'
                   "refine'"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`x]
                     []
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [(«term_+_» `x "+" (num "2")) "," (Term.hole "_")]
                      "⟩"))))
                  []
                  (Std.Tactic.rintro
                   "rintro"
                   [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
                    (Std.Tactic.RCases.rintroPat.one
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩"))]
                   [])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (Term.app
                         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                         [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])])
                        "="
                        («term-_»
                         "-"
                         (Term.app
                          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ
                           "τ")
                          [(Term.app `f₂ [`g])]))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule
                             [(patternIgnore (token.«← » "←"))]
                             `MonoidHom.coe_toHomUnits)
                            ","
                            (Tactic.rwRule [] `MonoidHom.map_inv)
                            ","
                            (Tactic.rwRule [] `translation_number_units_inv)
                            ","
                            (Tactic.rwRule [] `MonoidHom.coe_toHomUnits)]
                           "]")
                          [])]))))))
                  []
                  (calcTactic
                   "calc"
                   (calcStep
                    («term_≤_»
                     (Term.app `f₂ [(«term_⁻¹» `g "⁻¹") (Term.app `f₁ [`g `x])])
                     "≤"
                     (Term.app
                      `f₂
                      [(«term_⁻¹» `g "⁻¹")
                       («term_+_»
                        («term_+_»
                         `x
                         "+"
                         (Term.app
                          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ
                           "τ")
                          [(Term.app `f₁ [`g])]))
                        "+"
                        (num "1"))]))
                    ":="
                    (Term.app
                     `mono
                     [(Term.hole "_")
                      (Term.proj
                       (Term.app
                        `map_lt_add_translation_number_add_one
                        [(Term.hole "_") (Term.hole "_")])
                       "."
                       `le)]))
                   [(calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_+_»
                       (Term.app
                        `f₂
                        [(«term_⁻¹» `g "⁻¹")
                         («term_+_»
                          `x
                          "+"
                          (Term.app
                           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ
                            "τ")
                           [(Term.app `f₂ [`g])]))])
                       "+"
                       (num "1")))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `map_add_one)]
                           "]")
                          [])]))))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      («term_+_»
                       («term_+_»
                        («term_+_»
                         («term_+_»
                          `x
                          "+"
                          (Term.app
                           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ
                            "τ")
                           [(Term.app `f₂ [`g])]))
                         "+"
                         (Term.app
                          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ
                           "τ")
                          [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
                        "+"
                        (num "1"))
                       "+"
                       (num "1")))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.mono "mono" [] [] [] [])
                         []
                         (Tactic.exact
                          "exact"
                          (Term.proj
                           (Term.app
                            `map_lt_add_translation_number_add_one
                            [(Term.hole "_") (Term.hole "_")])
                           "."
                           `le))]))))
                    (calcStep
                     («term_=_» (Term.hole "_") "=" («term_+_» `x "+" (num "2")))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          []
                          ["["
                           [(Tactic.simpLemma [] [] `this)
                            ","
                            (Tactic.simpLemma [] [] `bit0)
                            ","
                            (Tactic.simpLemma [] [] `add_assoc)]
                           "]"]
                          [])]))))])]))))))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `F₁
             []
             ":="
             (Term.app `to_order_iso.comp [`f₁.to_hom_units])
             []))
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `F₂
             []
             ":="
             (Term.app `to_order_iso.comp [`f₂.to_hom_units])
             []))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hF₁ []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`g]
                 []
                 ","
                 («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₁ [`g])) "=" (Term.app `f₁ [`g]))))]
              ":="
              (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hF₂ []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`g]
                 []
                 ","
                 («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₂ [`g])) "=" (Term.app `f₂ [`g]))))]
              ":="
              (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hF₁)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hF₂)]
             "]"]
            [])
           []
           (Tactic.«tactic_<;>_»
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [(Term.hole "_")
                 ","
                 (Term.fun "fun" (Term.basicFun [`x `y `hxy] [] "=>" (Term.hole "_")))
                 ","
                 (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]
                "⟩")
               ","
               (Term.app
                `cSup_div_semiconj
                [`F₂ `F₁ (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]
              "⟩"))
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `hF₁)
               ","
               (Tactic.simpLemma [] [] `hF₂)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `MonoidHom.map_inv)
               ","
               (Tactic.simpLemma [] [] `coe_mk)]
              "]"]
             []))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.app
               `csupᵢ_mono
               [(Term.app `this [`y])
                (Term.fun "fun" (Term.basicFun [`g] [] "=>" (Term.hole "_")))]))
             []
             (Tactic.exact
              "exact"
              (Term.app `mono [(Term.hole "_") (Term.app `mono [(Term.hole "_") `hxy])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `map_add_one)] "]"]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.proj
               (Term.app
                `Monotone.map_csupr_of_continuous_at
                [(Term.app `continuous_at_id.add [`continuous_at_const])
                 (Term.app
                  `monotone_id.add_const
                  [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
                 (Term.app `this [`x])])
               "."
               `symm))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.app `this [`x]))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`x]
                []
                ","
                (Term.app
                 `BddAbove
                 [(Term.app
                   `range
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`g]
                      []
                      "=>"
                      (Term.app `f₂ [(«term_⁻¹» `g "⁻¹") (Term.app `f₁ [`g `x])])))])])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`x]
                    []
                    "=>"
                    (Term.anonymousCtor
                     "⟨"
                     [(«term_+_» `x "+" (num "2")) "," (Term.hole "_")]
                     "⟩"))))
                 []
                 (Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Term.app
                        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                        [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])])
                       "="
                       («term-_»
                        "-"
                        (Term.app
                         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                         [(Term.app `f₂ [`g])]))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule
                            [(patternIgnore (token.«← » "←"))]
                            `MonoidHom.coe_toHomUnits)
                           ","
                           (Tactic.rwRule [] `MonoidHom.map_inv)
                           ","
                           (Tactic.rwRule [] `translation_number_units_inv)
                           ","
                           (Tactic.rwRule [] `MonoidHom.coe_toHomUnits)]
                          "]")
                         [])]))))))
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_≤_»
                    (Term.app `f₂ [(«term_⁻¹» `g "⁻¹") (Term.app `f₁ [`g `x])])
                    "≤"
                    (Term.app
                     `f₂
                     [(«term_⁻¹» `g "⁻¹")
                      («term_+_»
                       («term_+_»
                        `x
                        "+"
                        (Term.app
                         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                         [(Term.app `f₁ [`g])]))
                       "+"
                       (num "1"))]))
                   ":="
                   (Term.app
                    `mono
                    [(Term.hole "_")
                     (Term.proj
                      (Term.app
                       `map_lt_add_translation_number_add_one
                       [(Term.hole "_") (Term.hole "_")])
                      "."
                      `le)]))
                  [(calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     («term_+_»
                      (Term.app
                       `f₂
                       [(«term_⁻¹» `g "⁻¹")
                        («term_+_»
                         `x
                         "+"
                         (Term.app
                          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ
                           "τ")
                          [(Term.app `f₂ [`g])]))])
                      "+"
                      (num "1")))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `map_add_one)]
                          "]")
                         [])]))))
                   (calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     («term_+_»
                      («term_+_»
                       («term_+_»
                        («term_+_»
                         `x
                         "+"
                         (Term.app
                          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ
                           "τ")
                          [(Term.app `f₂ [`g])]))
                        "+"
                        (Term.app
                         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                         [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
                       "+"
                       (num "1"))
                      "+"
                      (num "1")))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.mono "mono" [] [] [] [])
                        []
                        (Tactic.exact
                         "exact"
                         (Term.proj
                          (Term.app
                           `map_lt_add_translation_number_add_one
                           [(Term.hole "_") (Term.hole "_")])
                          "."
                          `le))]))))
                   (calcStep
                    («term_=_» (Term.hole "_") "=" («term_+_» `x "+" (num "2")))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         []
                         ["["
                          [(Tactic.simpLemma [] [] `this)
                           ","
                           (Tactic.simpLemma [] [] `bit0)
                           ","
                           (Tactic.simpLemma [] [] `add_assoc)]
                          "]"]
                         [])]))))])]))))))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `F₁
            []
            ":="
            (Term.app `to_order_iso.comp [`f₁.to_hom_units])
            []))
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `F₂
            []
            ":="
            (Term.app `to_order_iso.comp [`f₂.to_hom_units])
            []))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hF₁ []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`g]
                []
                ","
                («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₁ [`g])) "=" (Term.app `f₁ [`g]))))]
             ":="
             (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hF₂ []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`g]
                []
                ","
                («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₂ [`g])) "=" (Term.app `f₂ [`g]))))]
             ":="
             (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hF₁)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hF₂)]
            "]"]
           [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.anonymousCtor
               "⟨"
               [(Term.hole "_")
                ","
                (Term.fun "fun" (Term.basicFun [`x `y `hxy] [] "=>" (Term.hole "_")))
                ","
                (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]
               "⟩")
              ","
              (Term.app
               `cSup_div_semiconj
               [`F₂ `F₁ (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]
             "⟩"))
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `hF₁)
              ","
              (Tactic.simpLemma [] [] `hF₂)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `MonoidHom.map_inv)
              ","
              (Tactic.simpLemma [] [] `coe_mk)]
             "]"]
            []))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              `csupᵢ_mono
              [(Term.app `this [`y])
               (Term.fun "fun" (Term.basicFun [`g] [] "=>" (Term.hole "_")))]))
            []
            (Tactic.exact
             "exact"
             (Term.app `mono [(Term.hole "_") (Term.app `mono [(Term.hole "_") `hxy])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `map_add_one)] "]"] [])
            []
            (Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               `Monotone.map_csupr_of_continuous_at
               [(Term.app `continuous_at_id.add [`continuous_at_const])
                (Term.app
                 `monotone_id.add_const
                 [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
                (Term.app `this [`x])])
              "."
              `symm))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `this [`x]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `this [`x]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `this [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `map_add_one)] "]"] [])
        []
        (Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           `Monotone.map_csupr_of_continuous_at
           [(Term.app `continuous_at_id.add [`continuous_at_const])
            (Term.app
             `monotone_id.add_const
             [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
            (Term.app `this [`x])])
          "."
          `symm))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         `Monotone.map_csupr_of_continuous_at
         [(Term.app `continuous_at_id.add [`continuous_at_const])
          (Term.app
           `monotone_id.add_const
           [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
          (Term.app `this [`x])])
        "."
        `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `Monotone.map_csupr_of_continuous_at
        [(Term.app `continuous_at_id.add [`continuous_at_const])
         (Term.app
          `monotone_id.add_const
          [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
         (Term.app `this [`x])])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Monotone.map_csupr_of_continuous_at
       [(Term.app `continuous_at_id.add [`continuous_at_const])
        (Term.app
         `monotone_id.add_const
         [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
        (Term.app `this [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `this [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `monotone_id.add_const
       [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `monotone_id.add_const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `monotone_id.add_const
      [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_at_id.add [`continuous_at_const])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_at_const
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_at_id.add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_at_id.add [`continuous_at_const])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Monotone.map_csupr_of_continuous_at
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Monotone.map_csupr_of_continuous_at
      [(Term.paren "(" (Term.app `continuous_at_id.add [`continuous_at_const]) ")")
       (Term.paren
        "("
        (Term.app
         `monotone_id.add_const
         [(Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
        ")")
       (Term.paren "(" (Term.app `this [`x]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `map_add_one)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          `csupᵢ_mono
          [(Term.app `this [`y]) (Term.fun "fun" (Term.basicFun [`g] [] "=>" (Term.hole "_")))]))
        []
        (Tactic.exact
         "exact"
         (Term.app `mono [(Term.hole "_") (Term.app `mono [(Term.hole "_") `hxy])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `mono [(Term.hole "_") (Term.app `mono [(Term.hole "_") `hxy])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mono [(Term.hole "_") (Term.app `mono [(Term.hole "_") `hxy])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mono [(Term.hole "_") `hxy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mono [(Term.hole "_") `hxy])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `csupᵢ_mono
        [(Term.app `this [`y]) (Term.fun "fun" (Term.basicFun [`g] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `csupᵢ_mono
       [(Term.app `this [`y]) (Term.fun "fun" (Term.basicFun [`g] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`g] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `this [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `this [`y]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `csupᵢ_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            (Term.fun "fun" (Term.basicFun [`x `y `hxy] [] "=>" (Term.hole "_")))
            ","
            (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]
           "⟩")
          ","
          (Term.app
           `cSup_div_semiconj
           [`F₂ `F₁ (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]
         "⟩"))
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `hF₁)
          ","
          (Tactic.simpLemma [] [] `hF₂)
          ","
          (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `MonoidHom.map_inv)
          ","
          (Tactic.simpLemma [] [] `coe_mk)]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `hF₁)
         ","
         (Tactic.simpLemma [] [] `hF₂)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `MonoidHom.map_inv)
         ","
         (Tactic.simpLemma [] [] `coe_mk)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `MonoidHom.map_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hF₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hF₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(Term.hole "_")
           ","
           (Term.fun "fun" (Term.basicFun [`x `y `hxy] [] "=>" (Term.hole "_")))
           ","
           (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]
          "⟩")
         ","
         (Term.app
          `cSup_div_semiconj
          [`F₂ `F₁ (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.fun "fun" (Term.basicFun [`x `y `hxy] [] "=>" (Term.hole "_")))
          ","
          (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]
         "⟩")
        ","
        (Term.app
         `cSup_div_semiconj
         [`F₂ `F₁ (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cSup_div_semiconj
       [`F₂ `F₁ (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `F₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `F₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cSup_div_semiconj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.fun "fun" (Term.basicFun [`x `y `hxy] [] "=>" (Term.hole "_")))
        ","
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x `y `hxy] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hF₁)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `hF₂)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hF₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hF₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hF₂ []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`g]
            []
            ","
            («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₂ [`g])) "=" (Term.app `f₂ [`g]))))]
         ":="
         (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`g]
       []
       ","
       («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₂ [`g])) "=" (Term.app `f₂ [`g])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₂ [`g])) "=" (Term.app `f₂ [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f₂ [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term⇑_» "⇑" (Term.app `F₂ [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `F₂ [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `F₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `F₂ [`g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1023, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hF₁ []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`g]
            []
            ","
            («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₁ [`g])) "=" (Term.app `f₁ [`g]))))]
         ":="
         (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl)))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`g]
       []
       ","
       («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₁ [`g])) "=" (Term.app `f₁ [`g])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Init.Coe.«term⇑_» "⇑" (Term.app `F₁ [`g])) "=" (Term.app `f₁ [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f₁ [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Init.Coe.«term⇑_» "⇑" (Term.app `F₁ [`g]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `F₁ [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `F₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `F₁ [`g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1023, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.set
       "set"
       []
       (Mathlib.Tactic.setArgsRest `F₂ [] ":=" (Term.app `to_order_iso.comp [`f₂.to_hom_units]) []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_order_iso.comp [`f₂.to_hom_units])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₂.to_hom_units
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_order_iso.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.set
       "set"
       []
       (Mathlib.Tactic.setArgsRest `F₁ [] ":=" (Term.app `to_order_iso.comp [`f₁.to_hom_units]) []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `to_order_iso.comp [`f₁.to_hom_units])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₁.to_hom_units
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_order_iso.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`x]
            []
            ","
            (Term.app
             `BddAbove
             [(Term.app
               `range
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`g]
                  []
                  "=>"
                  (Term.app `f₂ [(«term_⁻¹» `g "⁻¹") (Term.app `f₁ [`g `x])])))])])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.anonymousCtor "⟨" [(«term_+_» `x "+" (num "2")) "," (Term.hole "_")] "⟩"))))
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.app
                    (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                    [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])])
                   "="
                   («term-_»
                    "-"
                    (Term.app
                     (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                     [(Term.app `f₂ [`g])]))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `MonoidHom.coe_toHomUnits)
                       ","
                       (Tactic.rwRule [] `MonoidHom.map_inv)
                       ","
                       (Tactic.rwRule [] `translation_number_units_inv)
                       ","
                       (Tactic.rwRule [] `MonoidHom.coe_toHomUnits)]
                      "]")
                     [])]))))))
             []
             (calcTactic
              "calc"
              (calcStep
               («term_≤_»
                (Term.app `f₂ [(«term_⁻¹» `g "⁻¹") (Term.app `f₁ [`g `x])])
                "≤"
                (Term.app
                 `f₂
                 [(«term_⁻¹» `g "⁻¹")
                  («term_+_»
                   («term_+_»
                    `x
                    "+"
                    (Term.app
                     (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                     [(Term.app `f₁ [`g])]))
                   "+"
                   (num "1"))]))
               ":="
               (Term.app
                `mono
                [(Term.hole "_")
                 (Term.proj
                  (Term.app
                   `map_lt_add_translation_number_add_one
                   [(Term.hole "_") (Term.hole "_")])
                  "."
                  `le)]))
              [(calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 («term_+_»
                  (Term.app
                   `f₂
                   [(«term_⁻¹» `g "⁻¹")
                    («term_+_»
                     `x
                     "+"
                     (Term.app
                      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                      [(Term.app `f₂ [`g])]))])
                  "+"
                  (num "1")))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `map_add_one)]
                      "]")
                     [])]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    («term_+_»
                     `x
                     "+"
                     (Term.app
                      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                      [(Term.app `f₂ [`g])]))
                    "+"
                    (Term.app
                     (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                     [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
                   "+"
                   (num "1"))
                  "+"
                  (num "1")))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.mono "mono" [] [] [] [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.proj
                      (Term.app
                       `map_lt_add_translation_number_add_one
                       [(Term.hole "_") (Term.hole "_")])
                      "."
                      `le))]))))
               (calcStep
                («term_=_» (Term.hole "_") "=" («term_+_» `x "+" (num "2")))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["["
                      [(Tactic.simpLemma [] [] `this)
                       ","
                       (Tactic.simpLemma [] [] `bit0)
                       ","
                       (Tactic.simpLemma [] [] `add_assoc)]
                      "]"]
                     [])]))))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.anonymousCtor "⟨" [(«term_+_» `x "+" (num "2")) "," (Term.hole "_")] "⟩"))))
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                 [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])])
                "="
                («term-_»
                 "-"
                 (Term.app
                  (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                  [(Term.app `f₂ [`g])]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `MonoidHom.coe_toHomUnits)
                    ","
                    (Tactic.rwRule [] `MonoidHom.map_inv)
                    ","
                    (Tactic.rwRule [] `translation_number_units_inv)
                    ","
                    (Tactic.rwRule [] `MonoidHom.coe_toHomUnits)]
                   "]")
                  [])]))))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             (Term.app `f₂ [(«term_⁻¹» `g "⁻¹") (Term.app `f₁ [`g `x])])
             "≤"
             (Term.app
              `f₂
              [(«term_⁻¹» `g "⁻¹")
               («term_+_»
                («term_+_»
                 `x
                 "+"
                 (Term.app
                  (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                  [(Term.app `f₁ [`g])]))
                "+"
                (num "1"))]))
            ":="
            (Term.app
             `mono
             [(Term.hole "_")
              (Term.proj
               (Term.app `map_lt_add_translation_number_add_one [(Term.hole "_") (Term.hole "_")])
               "."
               `le)]))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               (Term.app
                `f₂
                [(«term_⁻¹» `g "⁻¹")
                 («term_+_»
                  `x
                  "+"
                  (Term.app
                   (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                   [(Term.app `f₂ [`g])]))])
               "+"
               (num "1")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `map_add_one)]
                   "]")
                  [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_+_»
               («term_+_»
                («term_+_»
                 («term_+_»
                  `x
                  "+"
                  (Term.app
                   (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                   [(Term.app `f₂ [`g])]))
                 "+"
                 (Term.app
                  (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
                  [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
                "+"
                (num "1"))
               "+"
               (num "1")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.mono "mono" [] [] [] [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.proj
                   (Term.app
                    `map_lt_add_translation_number_add_one
                    [(Term.hole "_") (Term.hole "_")])
                   "."
                   `le))]))))
            (calcStep
             («term_=_» (Term.hole "_") "=" («term_+_» `x "+" (num "2")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `this)
                    ","
                    (Tactic.simpLemma [] [] `bit0)
                    ","
                    (Tactic.simpLemma [] [] `add_assoc)]
                   "]"]
                  [])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (Term.app `f₂ [(«term_⁻¹» `g "⁻¹") (Term.app `f₁ [`g `x])])
         "≤"
         (Term.app
          `f₂
          [(«term_⁻¹» `g "⁻¹")
           («term_+_»
            («term_+_»
             `x
             "+"
             (Term.app
              (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
              [(Term.app `f₁ [`g])]))
            "+"
            (num "1"))]))
        ":="
        (Term.app
         `mono
         [(Term.hole "_")
          (Term.proj
           (Term.app `map_lt_add_translation_number_add_one [(Term.hole "_") (Term.hole "_")])
           "."
           `le)]))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_+_»
           (Term.app
            `f₂
            [(«term_⁻¹» `g "⁻¹")
             («term_+_»
              `x
              "+"
              (Term.app
               (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
               [(Term.app `f₂ [`g])]))])
           "+"
           (num "1")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `map_add_one)] "]")
              [])]))))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_+_»
           («term_+_»
            («term_+_»
             («term_+_»
              `x
              "+"
              (Term.app
               (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
               [(Term.app `f₂ [`g])]))
             "+"
             (Term.app
              (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
              [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
            "+"
            (num "1"))
           "+"
           (num "1")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.mono "mono" [] [] [] [])
             []
             (Tactic.exact
              "exact"
              (Term.proj
               (Term.app `map_lt_add_translation_number_add_one [(Term.hole "_") (Term.hole "_")])
               "."
               `le))]))))
        (calcStep
         («term_=_» (Term.hole "_") "=" («term_+_» `x "+" (num "2")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `this)
                ","
                (Tactic.simpLemma [] [] `bit0)
                ","
                (Tactic.simpLemma [] [] `add_assoc)]
               "]"]
              [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `this)
             ","
             (Tactic.simpLemma [] [] `bit0)
             ","
             (Tactic.simpLemma [] [] `add_assoc)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `this)
         ","
         (Tactic.simpLemma [] [] `bit0)
         ","
         (Tactic.simpLemma [] [] `add_assoc)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bit0
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term_+_» `x "+" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `x "+" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.mono "mono" [] [] [] [])
          []
          (Tactic.exact
           "exact"
           (Term.proj
            (Term.app `map_lt_add_translation_number_add_one [(Term.hole "_") (Term.hole "_")])
            "."
            `le))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app `map_lt_add_translation_number_add_one [(Term.hole "_") (Term.hole "_")])
        "."
        `le))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `map_lt_add_translation_number_add_one [(Term.hole "_") (Term.hole "_")])
       "."
       `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `map_lt_add_translation_number_add_one [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_lt_add_translation_number_add_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `map_lt_add_translation_number_add_one [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.mono "mono" [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_+_»
        («term_+_»
         («term_+_»
          («term_+_»
           `x
           "+"
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [(Term.app `f₂ [`g])]))
          "+"
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
         "+"
         (num "1"))
        "+"
        (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_+_»
        («term_+_»
         («term_+_»
          `x
          "+"
          (Term.app
           (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
           [(Term.app `f₂ [`g])]))
         "+"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
        "+"
        (num "1"))
       "+"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       («term_+_»
        («term_+_»
         `x
         "+"
         (Term.app
          (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
          [(Term.app `f₂ [`g])]))
        "+"
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
       "+"
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       («term_+_»
        `x
        "+"
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [(Term.app `f₂ [`g])]))
       "+"
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
       [(Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `g "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `f₂ [(«term_⁻¹» `g "⁻¹")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Consider two actions `f₁ f₂ : G →* circle_deg1_lift` of a group on the real line by lifts of
    orientation preserving circle homeomorphisms. Suppose that for each `g : G` the homeomorphisms
    `f₁ g` and `f₂ g` have equal rotation numbers. Then there exists `F : circle_deg1_lift`  such that
    `F * f₁ g = f₂ g * F` for all `g : G`.
    
    This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
    cohomologie bornee][ghys87:groupes]. -/
  theorem
    semiconj_of_group_action_of_forall_translation_number_eq
    { G : Type _ } [ Group G ] ( f₁ f₂ : G →* CircleDeg1Lift ) ( h : ∀ g , τ f₁ g = τ f₂ g )
      : ∃ F : CircleDeg1Lift , ∀ g , Semiconj F f₁ g f₂ g
    :=
      by
        have
            : ∀ x , BddAbove range fun g => f₂ g ⁻¹ f₁ g x
              :=
              by
                refine' fun x => ⟨ x + 2 , _ ⟩
                  rintro _ ⟨ g , rfl ⟩
                  have
                    : τ f₂ g ⁻¹ = - τ f₂ g
                      :=
                      by
                        rw
                          [
                            ← MonoidHom.coe_toHomUnits
                              ,
                              MonoidHom.map_inv
                              ,
                              translation_number_units_inv
                              ,
                              MonoidHom.coe_toHomUnits
                            ]
                  calc
                    f₂ g ⁻¹ f₁ g x ≤ f₂ g ⁻¹ x + τ f₁ g + 1
                      :=
                      mono _ map_lt_add_translation_number_add_one _ _ . le
                    _ = f₂ g ⁻¹ x + τ f₂ g + 1 := by rw [ h , map_add_one ]
                      _ ≤ x + τ f₂ g + τ f₂ g ⁻¹ + 1 + 1
                        :=
                        by mono exact map_lt_add_translation_number_add_one _ _ . le
                      _ = x + 2 := by simp [ this , bit0 , add_assoc ]
          set F₁ := to_order_iso.comp f₁.to_hom_units
          set F₂ := to_order_iso.comp f₂.to_hom_units
          have hF₁ : ∀ g , ⇑ F₁ g = f₁ g := fun _ => rfl
          have hF₂ : ∀ g , ⇑ F₂ g = f₂ g := fun _ => rfl
          simp only [ ← hF₁ , ← hF₂ ]
          refine' ⟨ ⟨ _ , fun x y hxy => _ , fun x => _ ⟩ , cSup_div_semiconj F₂ F₁ fun x => _ ⟩
            <;>
            simp only [ hF₁ , hF₂ , ← MonoidHom.map_inv , coe_mk ]
          · refine' csupᵢ_mono this y fun g => _ exact mono _ mono _ hxy
          ·
            simp only [ map_add_one ]
              exact
                Monotone.map_csupr_of_continuous_at
                    continuous_at_id.add continuous_at_const monotone_id.add_const ( 1 : ℝ ) this x
                  .
                  symm
          · exact this x
#align
  circle_deg1_lift.semiconj_of_group_action_of_forall_translation_number_eq CircleDeg1Lift.semiconj_of_group_action_of_forall_translation_number_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If two lifts of circle homeomorphisms have the same translation number, then they are\nsemiconjugate by a `circle_deg1_lift`. This version uses arguments `f₁ f₂ : circle_deg1_liftˣ`\nto assume that `f₁` and `f₂` are homeomorphisms. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `units_semiconj_of_translation_number_eq [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f₁ `f₂]
         [":" (Algebra.Group.Units.«term_ˣ» `CircleDeg1Lift "ˣ")]
         "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f₁])
           "="
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f₂]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `F)] [":" `CircleDeg1Lift]))
         ","
         (Term.app `Semiconj [`F `f₁ `f₂]))))
      (Command.declValSimple
       ":="
       (Std.Tactic.haveI
        "haveI"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [`n]
             [(Term.typeSpec ":" (Term.app `Multiplicative [(termℤ "ℤ")]))]
             ","
             («term_=_»
              (Term.app
               (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
               [(Term.app
                 (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
                 [(Term.app `zpowersHom [(Term.hole "_") `f₁]) `n])])
              "="
              (Term.app
               (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
               [(Term.app
                 (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
                 [(Term.app `zpowersHom [(Term.hole "_") `f₂]) `n])]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.intro "intro" [`n])
              []
              (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])])))))
        []
        (Term.app
         (Term.proj
          (Term.app
           `semiconj_of_group_action_of_forall_translation_number_eq
           [(Term.hole "_") (Term.hole "_") `this])
          "."
          `imp)
         [(Term.fun
           "fun"
           (Term.basicFun
            [`F `hF]
            []
            "=>"
            (Term.app `hF [(Term.app `Multiplicative.ofAdd [(num "1")])])))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.haveI
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`n]
            [(Term.typeSpec ":" (Term.app `Multiplicative [(termℤ "ℤ")]))]
            ","
            («term_=_»
             (Term.app
              (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
              [(Term.app
                (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
                [(Term.app `zpowersHom [(Term.hole "_") `f₁]) `n])])
             "="
             (Term.app
              (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
              [(Term.app
                (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
                [(Term.app `zpowersHom [(Term.hole "_") `f₂]) `n])]))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`n])
             []
             (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])])))))
       []
       (Term.app
        (Term.proj
         (Term.app
          `semiconj_of_group_action_of_forall_translation_number_eq
          [(Term.hole "_") (Term.hole "_") `this])
         "."
         `imp)
        [(Term.fun
          "fun"
          (Term.basicFun
           [`F `hF]
           []
           "=>"
           (Term.app `hF [(Term.app `Multiplicative.ofAdd [(num "1")])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `semiconj_of_group_action_of_forall_translation_number_eq
         [(Term.hole "_") (Term.hole "_") `this])
        "."
        `imp)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`F `hF]
          []
          "=>"
          (Term.app `hF [(Term.app `Multiplicative.ofAdd [(num "1")])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`F `hF]
        []
        "=>"
        (Term.app `hF [(Term.app `Multiplicative.ofAdd [(num "1")])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hF [(Term.app `Multiplicative.ofAdd [(num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Multiplicative.ofAdd [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Multiplicative.ofAdd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Multiplicative.ofAdd [(num "1")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hF
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hF
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `semiconj_of_group_action_of_forall_translation_number_eq
        [(Term.hole "_") (Term.hole "_") `this])
       "."
       `imp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `semiconj_of_group_action_of_forall_translation_number_eq
       [(Term.hole "_") (Term.hole "_") `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `semiconj_of_group_action_of_forall_translation_number_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `semiconj_of_group_action_of_forall_translation_number_eq
      [(Term.hole "_") (Term.hole "_") `this])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`n])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`n])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`n]
       [(Term.typeSpec ":" (Term.app `Multiplicative [(termℤ "ℤ")]))]
       ","
       («term_=_»
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [(Term.app
           (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
           [(Term.app `zpowersHom [(Term.hole "_") `f₁]) `n])])
        "="
        (Term.app
         (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
         [(Term.app
           (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
           [(Term.app `zpowersHom [(Term.hole "_") `f₂]) `n])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(Term.app
          (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
          [(Term.app `zpowersHom [(Term.hole "_") `f₁]) `n])])
       "="
       (Term.app
        (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
        [(Term.app
          (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
          [(Term.app `zpowersHom [(Term.hole "_") `f₂]) `n])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
       [(Term.app
         (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
         [(Term.app `zpowersHom [(Term.hole "_") `f₂]) `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
       [(Term.app `zpowersHom [(Term.hole "_") `f₂]) `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `zpowersHom [(Term.hole "_") `f₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zpowersHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zpowersHom [(Term.hole "_") `f₂])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Units.coeHom [(Term.hole "_")]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Units.coeHom [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Units.coeHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Units.coeHom [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `Units.coeHom [(Term.hole "_")]) ")") "." `comp)
      [(Term.paren "(" (Term.app `zpowersHom [(Term.hole "_") `f₂]) ")") `n])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If two lifts of circle homeomorphisms have the same translation number, then they are
    semiconjugate by a `circle_deg1_lift`. This version uses arguments `f₁ f₂ : circle_deg1_liftˣ`
    to assume that `f₁` and `f₂` are homeomorphisms. -/
  theorem
    units_semiconj_of_translation_number_eq
    { f₁ f₂ : CircleDeg1Lift ˣ } ( h : τ f₁ = τ f₂ ) : ∃ F : CircleDeg1Lift , Semiconj F f₁ f₂
    :=
      haveI
        :
            ∀
              n
              : Multiplicative ℤ
              ,
              τ Units.coeHom _ . comp zpowersHom _ f₁ n = τ Units.coeHom _ . comp zpowersHom _ f₂ n
          :=
          by intro n simp [ h ]
        semiconj_of_group_action_of_forall_translation_number_eq _ _ this . imp
          fun F hF => hF Multiplicative.ofAdd 1
#align
  circle_deg1_lift.units_semiconj_of_translation_number_eq CircleDeg1Lift.units_semiconj_of_translation_number_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If two lifts of circle homeomorphisms have the same translation number, then they are\nsemiconjugate by a `circle_deg1_lift`. This version uses assumptions `is_unit f₁` and `is_unit f₂`\nto assume that `f₁` and `f₂` are homeomorphisms. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `semiconj_of_is_unit_of_translation_number_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f₁ `f₂] [":" `CircleDeg1Lift] "}")
        (Term.explicitBinder "(" [`h₁] [":" (Term.app `IsUnit [`f₁])] [] ")")
        (Term.explicitBinder "(" [`h₂] [":" (Term.app `IsUnit [`f₂])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f₁])
           "="
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f₂]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `F)] [":" `CircleDeg1Lift]))
         ","
         (Term.app `Semiconj [`F `f₁ `f₂]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `h₁) "," (Tactic.casesTarget [] `h₂)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.exact "exact" (Term.app `units_semiconj_of_translation_number_eq [`h]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `h₁) "," (Tactic.casesTarget [] `h₂)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                       [])]
                     "⟩")])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact "exact" (Term.app `units_semiconj_of_translation_number_eq [`h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `units_semiconj_of_translation_number_eq [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `units_semiconj_of_translation_number_eq [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `units_semiconj_of_translation_number_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `h₁) "," (Tactic.casesTarget [] `h₂)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f₂)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `F)] [":" `CircleDeg1Lift]))
       ","
       (Term.app `Semiconj [`F `f₁ `f₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Semiconj [`F `f₁ `f₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Semiconj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `CircleDeg1Lift
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f₁])
       "="
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If two lifts of circle homeomorphisms have the same translation number, then they are
    semiconjugate by a `circle_deg1_lift`. This version uses assumptions `is_unit f₁` and `is_unit f₂`
    to assume that `f₁` and `f₂` are homeomorphisms. -/
  theorem
    semiconj_of_is_unit_of_translation_number_eq
    { f₁ f₂ : CircleDeg1Lift } ( h₁ : IsUnit f₁ ) ( h₂ : IsUnit f₂ ) ( h : τ f₁ = τ f₂ )
      : ∃ F : CircleDeg1Lift , Semiconj F f₁ f₂
    :=
      by
        rcases h₁ , h₂ with ⟨ ⟨ f₁ , rfl ⟩ , ⟨ f₂ , rfl ⟩ ⟩
          exact units_semiconj_of_translation_number_eq h
#align
  circle_deg1_lift.semiconj_of_is_unit_of_translation_number_eq CircleDeg1Lift.semiconj_of_is_unit_of_translation_number_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If two lifts of circle homeomorphisms have the same translation number, then they are\nsemiconjugate by a `circle_deg1_lift`. This version uses assumptions `bijective f₁` and\n`bijective f₂` to assume that `f₁` and `f₂` are homeomorphisms. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `semiconj_of_bijective_of_translation_number_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f₁ `f₂] [":" `CircleDeg1Lift] "}")
        (Term.explicitBinder "(" [`h₁] [":" (Term.app `Bijective [`f₁])] [] ")")
        (Term.explicitBinder "(" [`h₂] [":" (Term.app `Bijective [`f₂])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f₁])
           "="
           (Term.app
            (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
            [`f₂]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `F)] [":" `CircleDeg1Lift]))
         ","
         (Term.app `Semiconj [`F `f₁ `f₂]))))
      (Command.declValSimple
       ":="
       (Term.app
        `semiconj_of_is_unit_of_translation_number_eq
        [(Term.app (Term.proj `is_unit_iff_bijective "." (fieldIdx "2")) [`h₁])
         (Term.app (Term.proj `is_unit_iff_bijective "." (fieldIdx "2")) [`h₂])
         `h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `semiconj_of_is_unit_of_translation_number_eq
       [(Term.app (Term.proj `is_unit_iff_bijective "." (fieldIdx "2")) [`h₁])
        (Term.app (Term.proj `is_unit_iff_bijective "." (fieldIdx "2")) [`h₂])
        `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `is_unit_iff_bijective "." (fieldIdx "2")) [`h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `is_unit_iff_bijective "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `is_unit_iff_bijective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `is_unit_iff_bijective "." (fieldIdx "2")) [`h₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `is_unit_iff_bijective "." (fieldIdx "2")) [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `is_unit_iff_bijective "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `is_unit_iff_bijective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `is_unit_iff_bijective "." (fieldIdx "2")) [`h₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `semiconj_of_is_unit_of_translation_number_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `F)] [":" `CircleDeg1Lift]))
       ","
       (Term.app `Semiconj [`F `f₁ `f₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Semiconj [`F `f₁ `f₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Semiconj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `CircleDeg1Lift
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f₁])
       "="
       (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ") [`f₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ "τ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ', expected 'CircleDeg1Lift.Dynamics.Circle.RotationNumber.TranslationNumber.termτ._@.Dynamics.Circle.RotationNumber.TranslationNumber._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If two lifts of circle homeomorphisms have the same translation number, then they are
    semiconjugate by a `circle_deg1_lift`. This version uses assumptions `bijective f₁` and
    `bijective f₂` to assume that `f₁` and `f₂` are homeomorphisms. -/
  theorem
    semiconj_of_bijective_of_translation_number_eq
    { f₁ f₂ : CircleDeg1Lift } ( h₁ : Bijective f₁ ) ( h₂ : Bijective f₂ ) ( h : τ f₁ = τ f₂ )
      : ∃ F : CircleDeg1Lift , Semiconj F f₁ f₂
    :=
      semiconj_of_is_unit_of_translation_number_eq
        is_unit_iff_bijective . 2 h₁ is_unit_iff_bijective . 2 h₂ h
#align
  circle_deg1_lift.semiconj_of_bijective_of_translation_number_eq CircleDeg1Lift.semiconj_of_bijective_of_translation_number_eq

end CircleDeg1Lift

