import Mathbin.Algebra.IterateHom 
import Mathbin.Analysis.SpecificLimits 
import Mathbin.Topology.Algebra.Ordered.MonotoneContinuity 
import Mathbin.Order.Iterate 
import Mathbin.Order.SemiconjSup

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

open_locale TopologicalSpace Classical

/-!
### Definition and monoid structure
-/


/-- A lift of a monotone degree one map `S¹ → S¹`. -/
structure CircleDeg1Lift : Type where 
  toFun : ℝ → ℝ 
  monotone' : Monotone to_fun 
  map_add_one' : ∀ x, to_fun (x+1) = to_fun x+1

namespace CircleDeg1Lift

instance  : CoeFun CircleDeg1Lift fun _ => ℝ → ℝ :=
  ⟨CircleDeg1Lift.toFun⟩

@[simp]
theorem coe_mk f h₁ h₂ : «expr⇑ » (mk f h₁ h₂) = f :=
  rfl

variable(f g : CircleDeg1Lift)

protected theorem Monotone : Monotone f :=
  f.monotone'

@[mono]
theorem mono {x y} (h : x ≤ y) : f x ≤ f y :=
  f.monotone h

theorem strict_mono_iff_injective : StrictMono f ↔ injective f :=
  f.monotone.strict_mono_iff_injective

@[simp]
theorem map_add_one : ∀ x, f (x+1) = f x+1 :=
  f.map_add_one'

@[simp]
theorem map_one_add (x : ℝ) : f (1+x) = 1+f x :=
  by 
    rw [add_commₓ, map_add_one, add_commₓ]

theorem coe_inj : ∀ ⦃f g : CircleDeg1Lift⦄, (f : ℝ → ℝ) = g → f = g :=
  fun ⟨f, fm, fd⟩ ⟨g, gm, gd⟩ h =>
    by 
      congr <;> exact h

@[ext]
theorem ext ⦃f g : CircleDeg1Lift⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_inj$ funext h

theorem ext_iff {f g : CircleDeg1Lift} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

instance  : Monoidₓ CircleDeg1Lift :=
  { mul :=
      fun f g =>
        { toFun := f ∘ g, monotone' := f.monotone.comp g.monotone,
          map_add_one' :=
            fun x =>
              by 
                simp [map_add_one] },
    one := ⟨id, monotone_id, fun _ => rfl⟩, mul_one := fun f => coe_inj$ Function.comp.right_id f,
    one_mul := fun f => coe_inj$ Function.comp.left_id f, mul_assoc := fun f₁ f₂ f₃ => coe_inj rfl }

instance  : Inhabited CircleDeg1Lift :=
  ⟨1⟩

@[simp]
theorem coe_mul : «expr⇑ » (f*g) = (f ∘ g) :=
  rfl

theorem mul_apply x : (f*g) x = f (g x) :=
  rfl

@[simp]
theorem coe_one : «expr⇑ » (1 : CircleDeg1Lift) = id :=
  rfl

instance units_has_coe_to_fun : CoeFun (Units CircleDeg1Lift) fun _ => ℝ → ℝ :=
  ⟨fun f => «expr⇑ » (f : CircleDeg1Lift)⟩

@[simp, normCast]
theorem units_coe (f : Units CircleDeg1Lift) : «expr⇑ » (f : CircleDeg1Lift) = f :=
  rfl

@[simp]
theorem units_inv_apply_apply (f : Units CircleDeg1Lift) (x : ℝ) : (f⁻¹ : Units CircleDeg1Lift) (f x) = x :=
  by 
    simp only [←units_coe, ←mul_apply, f.inv_mul, coe_one, id]

@[simp]
theorem units_apply_inv_apply (f : Units CircleDeg1Lift) (x : ℝ) : f ((f⁻¹ : Units CircleDeg1Lift) x) = x :=
  by 
    simp only [←units_coe, ←mul_apply, f.mul_inv, coe_one, id]

/-- If a lift of a circle map is bijective, then it is an order automorphism of the line. -/
def to_order_iso : Units CircleDeg1Lift →* ℝ ≃o ℝ :=
  { toFun :=
      fun f =>
        { toFun := f, invFun := «expr⇑ » (f⁻¹), left_inv := units_inv_apply_apply f,
          right_inv := units_apply_inv_apply f,
          map_rel_iff' :=
            fun x y =>
              ⟨fun h =>
                  by 
                    simpa using mono («expr↑ » (f⁻¹)) h,
                mono f⟩ },
    map_one' := rfl, map_mul' := fun f g => rfl }

@[simp]
theorem coe_to_order_iso (f : Units CircleDeg1Lift) : «expr⇑ » (to_order_iso f) = f :=
  rfl

@[simp]
theorem coe_to_order_iso_symm (f : Units CircleDeg1Lift) :
  «expr⇑ » (to_order_iso f).symm = (f⁻¹ : Units CircleDeg1Lift) :=
  rfl

@[simp]
theorem coe_to_order_iso_inv (f : Units CircleDeg1Lift) : «expr⇑ » (to_order_iso f⁻¹) = (f⁻¹ : Units CircleDeg1Lift) :=
  rfl

theorem is_unit_iff_bijective {f : CircleDeg1Lift} : IsUnit f ↔ bijective f :=
  ⟨fun ⟨u, h⟩ => h ▸ (to_order_iso u).Bijective,
    fun h =>
      Units.is_unit
        { val := f,
          inv :=
            { toFun := (Equiv.ofBijective f h).symm,
              monotone' :=
                fun x y hxy =>
                  (f.strict_mono_iff_injective.2 h.1).le_iff_le.1
                    (by 
                      simp only [Equiv.of_bijective_apply_symm_apply f h, hxy]),
              map_add_one' :=
                fun x =>
                  h.1$
                    by 
                      simp only [Equiv.of_bijective_apply_symm_apply f, f.map_add_one] },
          val_inv := ext$ Equiv.of_bijective_apply_symm_apply f h,
          inv_val := ext$ Equiv.of_bijective_symm_apply_apply f h }⟩

theorem coe_pow : ∀ n : ℕ, «expr⇑ » (f ^ n) = f^[n]
| 0 => rfl
| n+1 =>
  by 
    ext x 
    simp [coe_pow n, pow_succ'ₓ]

theorem semiconj_by_iff_semiconj {f g₁ g₂ : CircleDeg1Lift} : SemiconjBy f g₁ g₂ ↔ semiconj f g₁ g₂ :=
  ext_iff

theorem commute_iff_commute {f g : CircleDeg1Lift} : Commute f g ↔ Function.Commute f g :=
  ext_iff

/-!
### Translate by a constant
-/


/-- The map `y ↦ x + y` as a `circle_deg1_lift`. More precisely, we define a homomorphism from
`multiplicative ℝ` to `units circle_deg1_lift`, so the translation by `x` is
`translation (multiplicative.of_add x)`. -/
def translate : Multiplicative ℝ →* Units CircleDeg1Lift :=
  by 
    refine' (Units.map _).comp to_units.to_monoid_hom <;>
      exact
        { toFun := fun x => ⟨fun y => x.to_add+y, fun y₁ y₂ h => add_le_add_left h _, fun y => (add_assocₓ _ _ _).symm⟩,
          map_one' := ext$ zero_addₓ, map_mul' := fun x y => ext$ add_assocₓ _ _ }

@[simp]
theorem translate_apply (x y : ℝ) : translate (Multiplicative.ofAdd x) y = x+y :=
  rfl

@[simp]
theorem translate_inv_apply (x y : ℝ) : ((translate$ Multiplicative.ofAdd x)⁻¹) y = (-x)+y :=
  rfl

@[simp]
theorem translate_zpow (x : ℝ) (n : ℤ) :
  translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd$ «expr↑ » n*x) :=
  by 
    simp only [←zsmul_eq_mul, of_add_zsmul, MonoidHom.map_zpow]

@[simp]
theorem translate_pow (x : ℝ) (n : ℕ) :
  translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd$ «expr↑ » n*x) :=
  translate_zpow x n

@[simp]
theorem translate_iterate (x : ℝ) (n : ℕ) :
  translate (Multiplicative.ofAdd x)^[n] = translate (Multiplicative.ofAdd$ «expr↑ » n*x) :=
  by 
    rw [←units_coe, ←coe_pow, ←Units.coe_pow, translate_pow, units_coe]

/-!
### Commutativity with integer translations

In this section we prove that `f` commutes with translations by an integer number.
First we formulate these statements (for a natural or an integer number,
addition on the left or on the right, addition or subtraction) using `function.commute`,
then reformulate as `simp` lemmas `map_int_add` etc.
-/


theorem commute_nat_add (n : ℕ) : Function.Commute f ((·+·) n) :=
  by 
    simpa only [nsmul_one, add_left_iterate] using Function.Commute.iterate_right f.map_one_add n

theorem commute_add_nat (n : ℕ) : Function.Commute f fun x => x+n :=
  by 
    simp only [add_commₓ _ (n : ℝ), f.commute_nat_add n]

theorem commute_sub_nat (n : ℕ) : Function.Commute f fun x => x - n :=
  by 
    simpa only [sub_eq_add_neg] using
      (f.commute_add_nat n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

theorem commute_add_int : ∀ n : ℤ, Function.Commute f fun x => x+n
| (n : ℕ) => f.commute_add_nat n
| -[1+ n] =>
  by 
    simpa only [sub_eq_add_neg] using f.commute_sub_nat (n+1)

theorem commute_int_add (n : ℤ) : Function.Commute f ((·+·) n) :=
  by 
    simpa only [add_commₓ _ (n : ℝ)] using f.commute_add_int n

theorem commute_sub_int (n : ℤ) : Function.Commute f fun x => x - n :=
  by 
    simpa only [sub_eq_add_neg] using
      (f.commute_add_int n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

@[simp]
theorem map_int_add (m : ℤ) (x : ℝ) : f (m+x) = m+f x :=
  f.commute_int_add m x

@[simp]
theorem map_add_int (x : ℝ) (m : ℤ) : f (x+m) = f x+m :=
  f.commute_add_int m x

@[simp]
theorem map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
  f.commute_sub_int n x

@[simp]
theorem map_add_nat (x : ℝ) (n : ℕ) : f (x+n) = f x+n :=
  f.map_add_int x n

@[simp]
theorem map_nat_add (n : ℕ) (x : ℝ) : f (n+x) = n+f x :=
  f.map_int_add n x

@[simp]
theorem map_sub_nat (x : ℝ) (n : ℕ) : f (x - n) = f x - n :=
  f.map_sub_int x n

theorem map_int_of_map_zero (n : ℤ) : f n = f 0+n :=
  by 
    rw [←f.map_add_int, zero_addₓ]

@[simp]
theorem map_fract_sub_fract_eq (x : ℝ) : f (fract x) - fract x = f x - x :=
  by 
    rw [Int.fract, f.map_sub_int, sub_sub_sub_cancel_right]

/-!
### Pointwise order on circle maps
-/


/-- Monotone circle maps form a lattice with respect to the pointwise order -/
noncomputable instance  : Lattice CircleDeg1Lift :=
  { sup :=
      fun f g =>
        { toFun := fun x => max (f x) (g x), monotone' := fun x y h => max_le_max (f.mono h) (g.mono h),
          map_add_one' :=
            fun x =>
              by 
                simp [max_add_add_right] },
    le := fun f g => ∀ x, f x ≤ g x, le_refl := fun f x => le_reflₓ (f x),
    le_trans := fun f₁ f₂ f₃ h₁₂ h₂₃ x => le_transₓ (h₁₂ x) (h₂₃ x),
    le_antisymm := fun f₁ f₂ h₁₂ h₂₁ => ext$ fun x => le_antisymmₓ (h₁₂ x) (h₂₁ x),
    le_sup_left := fun f g x => le_max_leftₓ (f x) (g x), le_sup_right := fun f g x => le_max_rightₓ (f x) (g x),
    sup_le := fun f₁ f₂ f₃ h₁ h₂ x => max_leₓ (h₁ x) (h₂ x),
    inf :=
      fun f g =>
        { toFun := fun x => min (f x) (g x), monotone' := fun x y h => min_le_min (f.mono h) (g.mono h),
          map_add_one' :=
            fun x =>
              by 
                simp [min_add_add_right] },
    inf_le_left := fun f g x => min_le_leftₓ (f x) (g x), inf_le_right := fun f g x => min_le_rightₓ (f x) (g x),
    le_inf := fun f₁ f₂ f₃ h₂ h₃ x => le_minₓ (h₂ x) (h₃ x) }

@[simp]
theorem sup_apply (x : ℝ) : (f⊔g) x = max (f x) (g x) :=
  rfl

@[simp]
theorem inf_apply (x : ℝ) : (f⊓g) x = min (f x) (g x) :=
  rfl

theorem iterate_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f^[n] :=
  fun f g h => f.monotone.iterate_le_of_le h _

theorem iterate_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  iterate_monotone n h

theorem pow_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f ^ n ≤ g ^ n :=
  fun x =>
    by 
      simp only [coe_pow, iterate_mono h n x]

theorem pow_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f ^ n :=
  fun f g h => pow_mono h n

/-!
### Estimates on `(f * g) 0`

We prove the estimates `f 0 + ⌊g 0⌋ ≤ f (g 0) ≤ f 0 + ⌈g 0⌉` and some corollaries with added/removed
floors and ceils.

We also prove that for two semiconjugate maps `g₁`, `g₂`, the distance between `g₁ 0` and `g₂ 0`
is less than two.
-/


theorem map_le_of_map_zero (x : ℝ) : f x ≤ f 0+⌈x⌉ :=
  calc f x ≤ f ⌈x⌉ := f.monotone$ le_ceil _ 
    _ = f 0+⌈x⌉ := f.map_int_of_map_zero _
    

theorem map_map_zero_le : f (g 0) ≤ f 0+⌈g 0⌉ :=
  f.map_le_of_map_zero (g 0)

theorem floor_map_map_zero_le : ⌊f (g 0)⌋ ≤ ⌊f 0⌋+⌈g 0⌉ :=
  calc ⌊f (g 0)⌋ ≤ ⌊f 0+⌈g 0⌉⌋ := floor_mono$ f.map_map_zero_le g 
    _ = ⌊f 0⌋+⌈g 0⌉ := floor_add_int _ _
    

theorem ceil_map_map_zero_le : ⌈f (g 0)⌉ ≤ ⌈f 0⌉+⌈g 0⌉ :=
  calc ⌈f (g 0)⌉ ≤ ⌈f 0+⌈g 0⌉⌉ := ceil_mono$ f.map_map_zero_le g 
    _ = ⌈f 0⌉+⌈g 0⌉ := ceil_add_int _ _
    

theorem map_map_zero_lt : f (g 0) < (f 0+g 0)+1 :=
  calc f (g 0) ≤ f 0+⌈g 0⌉ := f.map_map_zero_le g 
    _ < f 0+g 0+1 := add_lt_add_left (ceil_lt_add_one _) _ 
    _ = (f 0+g 0)+1 := (add_assocₓ _ _ _).symm
    

theorem le_map_of_map_zero (x : ℝ) : (f 0+⌊x⌋) ≤ f x :=
  calc (f 0+⌊x⌋) = f ⌊x⌋ := (f.map_int_of_map_zero _).symm 
    _ ≤ f x := f.monotone$ floor_le _
    

theorem le_map_map_zero : (f 0+⌊g 0⌋) ≤ f (g 0) :=
  f.le_map_of_map_zero (g 0)

theorem le_floor_map_map_zero : (⌊f 0⌋+⌊g 0⌋) ≤ ⌊f (g 0)⌋ :=
  calc (⌊f 0⌋+⌊g 0⌋) = ⌊f 0+⌊g 0⌋⌋ := (floor_add_int _ _).symm 
    _ ≤ ⌊f (g 0)⌋ := floor_mono$ f.le_map_map_zero g
    

theorem le_ceil_map_map_zero : (⌈f 0⌉+⌊g 0⌋) ≤ ⌈(f*g) 0⌉ :=
  calc (⌈f 0⌉+⌊g 0⌋) = ⌈f 0+⌊g 0⌋⌉ := (ceil_add_int _ _).symm 
    _ ≤ ⌈f (g 0)⌉ := ceil_mono$ f.le_map_map_zero g
    

theorem lt_map_map_zero : (f 0+g 0) - 1 < f (g 0) :=
  calc (f 0+g 0) - 1 = f 0+g 0 - 1 := add_sub_assoc _ _ _ 
    _ < f 0+⌊g 0⌋ := add_lt_add_left (sub_one_lt_floor _) _ 
    _ ≤ f (g 0) := f.le_map_map_zero g
    

theorem dist_map_map_zero_lt : dist (f 0+g 0) (f (g 0)) < 1 :=
  by 
    rw [dist_comm, Real.dist_eq, abs_lt, lt_sub_iff_add_lt', sub_lt_iff_lt_add', ←sub_eq_add_neg]
    exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩

theorem dist_map_zero_lt_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semiconj f g₁ g₂) :
  dist (g₁ 0) (g₂ 0) < 2 :=
  calc dist (g₁ 0) (g₂ 0) ≤ dist (g₁ 0) (f (g₁ 0) - f 0)+dist _ (g₂ 0) := dist_triangle _ _ _ 
    _ = dist (f 0+g₁ 0) (f (g₁ 0))+dist (g₂ 0+f 0) (g₂ (f 0)) :=
    by 
      simp only [h.eq, Real.dist_eq, sub_sub, add_commₓ (f 0), sub_sub_assoc_swap, abs_sub_comm (g₂ (f 0))]
    _ < 2 := add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)
    

theorem dist_map_zero_lt_of_semiconj_by {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂) : dist (g₁ 0) (g₂ 0) < 2 :=
  dist_map_zero_lt_of_semiconj$ semiconj_by_iff_semiconj.1 h

/-!
### Limits at infinities and continuity
-/


protected theorem tendsto_at_bot : tendsto f at_bot at_bot :=
  tendsto_at_bot_mono f.map_le_of_map_zero$
    tendsto_at_bot_add_const_left _ _$
      (tendsto_at_bot_mono fun x => (ceil_lt_add_one x).le)$ tendsto_at_bot_add_const_right _ _ tendsto_id

protected theorem tendsto_at_top : tendsto f at_top at_top :=
  tendsto_at_top_mono f.le_map_of_map_zero$
    tendsto_at_top_add_const_left _ _$
      (tendsto_at_top_mono fun x => (sub_one_lt_floor x).le)$
        by 
          simpa [sub_eq_add_neg] using tendsto_at_top_add_const_right _ _ tendsto_id

theorem continuous_iff_surjective : Continuous f ↔ Function.Surjective f :=
  ⟨fun h => h.surjective f.tendsto_at_top f.tendsto_at_bot, f.monotone.continuous_of_surjective⟩

/-!
### Estimates on `(f^n) x`

If we know that `f x` is `≤`/`<`/`≥`/`>`/`=` to `x + m`, then we have a similar estimate on
`f^[n] x` and `x + n * m`.

For `≤`, `≥`, and `=` we formulate both `of` (implication) and `iff` versions because implications
work for `n = 0`. For `<` and `>` we formulate only `iff` versions.
-/


theorem iterate_le_of_map_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x+m) (n : ℕ) : (f^[n]) x ≤ x+n*m :=
  by 
    simpa only [nsmul_eq_mul, add_right_iterate] using
      (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const m) h n

theorem le_iterate_of_add_int_le_map {x : ℝ} {m : ℤ} (h : (x+m) ≤ f x) (n : ℕ) : (x+n*m) ≤ (f^[n]) x :=
  by 
    simpa only [nsmul_eq_mul, add_right_iterate] using
      (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const m) f.monotone h n

theorem iterate_eq_of_map_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x+m) (n : ℕ) : (f^[n]) x = x+n*m :=
  by 
    simpa only [nsmul_eq_mul, add_right_iterate] using (f.commute_add_int m).iterate_eq_of_map_eq n h

theorem iterate_pos_le_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : ((f^[n]) x ≤ x+n*m) ↔ f x ≤ x+m :=
  by 
    simpa only [nsmul_eq_mul, add_right_iterate] using
      (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strict_mono_id.add_const m) hn

theorem iterate_pos_lt_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : ((f^[n]) x < x+n*m) ↔ f x < x+m :=
  by 
    simpa only [nsmul_eq_mul, add_right_iterate] using
      (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strict_mono_id.add_const m) hn

theorem iterate_pos_eq_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : ((f^[n]) x = x+n*m) ↔ f x = x+m :=
  by 
    simpa only [nsmul_eq_mul, add_right_iterate] using
      (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strict_mono_id.add_const m) hn

theorem le_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : (x+n*m) ≤ (f^[n]) x ↔ (x+m) ≤ f x :=
  by 
    simpa only [not_ltₓ] using not_congr (f.iterate_pos_lt_iff hn)

theorem lt_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) : (x+n*m) < (f^[n]) x ↔ (x+m) < f x :=
  by 
    simpa only [not_leₓ] using not_congr (f.iterate_pos_le_iff hn)

theorem mul_floor_map_zero_le_floor_iterate_zero (n : ℕ) : («expr↑ » n*⌊f 0⌋) ≤ ⌊(f^[n]) 0⌋ :=
  by 
    rw [le_floor, Int.cast_mul, Int.cast_coe_nat, ←zero_addₓ ((n : ℝ)*_)]
    apply le_iterate_of_add_int_le_map 
    simp [floor_le]

/-!
### Definition of translation number
-/


noncomputable theory

/-- An auxiliary sequence used to define the translation number. -/
def transnum_aux_seq (n : ℕ) : ℝ :=
  (f ^ 2 ^ n) 0 / 2 ^ n

/-- The translation number of a `circle_deg1_lift`, $τ(f)=\lim_{n→∞}\frac{f^n(x)-x}{n}$. We use
an auxiliary sequence `\frac{f^{2^n}(0)}{2^n}` to define `τ(f)` because some proofs are simpler
this way. -/
def translation_number : ℝ :=
  limₓ at_top f.transnum_aux_seq

local notation "τ" => translation_number

theorem transnum_aux_seq_def : f.transnum_aux_seq = fun n : ℕ => (f ^ 2 ^ n) 0 / 2 ^ n :=
  rfl

theorem translation_number_eq_of_tendsto_aux {τ' : ℝ} (h : tendsto f.transnum_aux_seq at_top (𝓝 τ')) : τ f = τ' :=
  h.lim_eq

theorem translation_number_eq_of_tendsto₀ {τ' : ℝ} (h : tendsto (fun n : ℕ => (f^[n]) 0 / n) at_top (𝓝 τ')) :
  τ f = τ' :=
  f.translation_number_eq_of_tendsto_aux$
    by 
      simpa [· ∘ ·, transnum_aux_seq_def, coe_pow] using h.comp (Nat.tendsto_pow_at_top_at_top_of_one_lt one_lt_two)

theorem translation_number_eq_of_tendsto₀' {τ' : ℝ} (h : tendsto (fun n : ℕ => (f^[n+1]) 0 / n+1) at_top (𝓝 τ')) :
  τ f = τ' :=
  f.translation_number_eq_of_tendsto₀$ (tendsto_add_at_top_iff_nat 1).1 h

theorem transnum_aux_seq_zero : f.transnum_aux_seq 0 = f 0 :=
  by 
    simp [transnum_aux_seq]

-- error in Dynamics.Circle.RotationNumber.TranslationNumber: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem transnum_aux_seq_dist_lt
(n : exprℕ()) : «expr < »(dist (f.transnum_aux_seq n) (f.transnum_aux_seq «expr + »(n, 1)), «expr / »(«expr / »(1, 2), «expr ^ »(2, n))) :=
begin
  have [] [":", expr «expr < »(0, («expr ^ »(2, «expr + »(n, 1)) : exprℝ()))] [":=", expr pow_pos zero_lt_two _],
  rw ["[", expr div_div_eq_div_mul, ",", "<-", expr pow_succ, ",", "<-", expr abs_of_pos this, "]"] [],
  replace [] [] [":=", expr abs_pos.2 (ne_of_gt this)],
  convert [] [expr (div_lt_div_right this).2 («expr ^ »(f, «expr ^ »(2, n)).dist_map_map_zero_lt «expr ^ »(f, «expr ^ »(2, n)))] [],
  simp_rw ["[", expr transnum_aux_seq, ",", expr real.dist_eq, "]"] [],
  rw ["[", "<-", expr abs_div, ",", expr sub_div, ",", expr pow_succ', ",", expr pow_succ, ",", "<-", expr two_mul, ",", expr mul_div_mul_left _ _ (@two_ne_zero exprℝ() _ _), ",", expr pow_mul, ",", expr sq, ",", expr mul_apply, "]"] []
end

theorem tendsto_translation_number_aux : tendsto f.transnum_aux_seq at_top (𝓝$ τ f) :=
  (cauchy_seq_of_le_geometric_two 1 fun n => le_of_ltₓ$ f.transnum_aux_seq_dist_lt n).tendsto_lim

theorem dist_map_zero_translation_number_le : dist (f 0) (τ f) ≤ 1 :=
  f.transnum_aux_seq_zero ▸
    dist_le_of_le_geometric_two_of_tendsto₀ 1 (fun n => le_of_ltₓ$ f.transnum_aux_seq_dist_lt n)
      f.tendsto_translation_number_aux

-- error in Dynamics.Circle.RotationNumber.TranslationNumber: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_translation_number_of_dist_bounded_aux
(x : exprℕ() → exprℝ())
(C : exprℝ())
(H : ∀
 n : exprℕ(), «expr ≤ »(dist («expr ^ »(f, n) 0) (x n), C)) : tendsto (λ
 n : exprℕ(), «expr / »(x «expr ^ »(2, n), «expr ^ »(2, n))) at_top «expr $ »(expr𝓝(), exprτ() f) :=
begin
  refine [expr f.tendsto_translation_number_aux.congr_dist (squeeze_zero (λ _, dist_nonneg) _ _)],
  { exact [expr λ n, «expr / »(C, «expr ^ »(2, n))] },
  { intro [ident n],
    have [] [":", expr «expr < »(0, («expr ^ »(2, n) : exprℝ()))] [":=", expr pow_pos zero_lt_two _],
    convert [] [expr (div_le_div_right this).2 (H «expr ^ »(2, n))] [],
    rw ["[", expr transnum_aux_seq, ",", expr real.dist_eq, ",", "<-", expr sub_div, ",", expr abs_div, ",", expr abs_of_pos this, ",", expr real.dist_eq, "]"] [] },
  { exact [expr «expr ▸ »(mul_zero C, tendsto_const_nhds.mul «expr $ »(tendsto_inv_at_top_zero.comp, tendsto_pow_at_top_at_top_of_one_lt one_lt_two))] }
end

theorem translation_number_eq_of_dist_bounded {f g : CircleDeg1Lift} (C : ℝ)
  (H : ∀ n : ℕ, dist ((f ^ n) 0) ((g ^ n) 0) ≤ C) : τ f = τ g :=
  Eq.symm$ g.translation_number_eq_of_tendsto_aux$ f.tendsto_translation_number_of_dist_bounded_aux _ C H

@[simp]
theorem translation_number_one : τ 1 = 0 :=
  translation_number_eq_of_tendsto₀ _$
    by 
      simp [tendsto_const_nhds]

theorem translation_number_eq_of_semiconj_by {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂) : τ g₁ = τ g₂ :=
  translation_number_eq_of_dist_bounded 2$ fun n => le_of_ltₓ$ dist_map_zero_lt_of_semiconj_by$ H.pow_right n

theorem translation_number_eq_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (H : Function.Semiconj f g₁ g₂) : τ g₁ = τ g₂ :=
  translation_number_eq_of_semiconj_by$ semiconj_by_iff_semiconj.2 H

-- error in Dynamics.Circle.RotationNumber.TranslationNumber: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem translation_number_mul_of_commute
{f g : circle_deg1_lift}
(h : commute f g) : «expr = »(exprτ() «expr * »(f, g), «expr + »(exprτ() f, exprτ() g)) :=
begin
  have [] [":", expr tendsto (λ
    n : exprℕ(), «expr / »(λ
     k, «expr + »(«expr ^ »(f, k) 0, «expr ^ »(g, k) 0) «expr ^ »(2, n), «expr ^ »(2, n))) at_top «expr $ »(expr𝓝(), «expr + »(exprτ() f, exprτ() g))] [":=", expr «expr $ »((f.tendsto_translation_number_aux.add g.tendsto_translation_number_aux).congr, λ
    n, (add_div («expr ^ »(f, «expr ^ »(2, n)) 0) («expr ^ »(g, «expr ^ »(2, n)) 0) «expr ^ »((2 : exprℝ()), n)).symm)],
  refine [expr tendsto_nhds_unique («expr * »(f, g).tendsto_translation_number_of_dist_bounded_aux _ 1 (λ n, _)) this],
  rw ["[", expr h.mul_pow, ",", expr dist_comm, "]"] [],
  exact [expr le_of_lt («expr ^ »(f, n).dist_map_map_zero_lt «expr ^ »(g, n))]
end

@[simp]
theorem translation_number_units_inv (f : Units CircleDeg1Lift) : τ («expr↑ » (f⁻¹)) = -τ f :=
  eq_neg_iff_add_eq_zero.2$
    by 
      simp [←translation_number_mul_of_commute (Commute.refl _).units_inv_left]

@[simp]
theorem translation_number_pow : ∀ n : ℕ, τ (f ^ n) = n*τ f
| 0 =>
  by 
    simp 
| n+1 =>
  by 
    rw [pow_succ'ₓ, translation_number_mul_of_commute (Commute.pow_self f n), translation_number_pow n,
      Nat.cast_add_one, add_mulₓ, one_mulₓ]

@[simp]
theorem translation_number_zpow (f : Units CircleDeg1Lift) : ∀ n : ℤ, τ (f ^ n : Units _) = n*τ f
| (n : ℕ) =>
  by 
    simp [translation_number_pow f n]
| -[1+ n] =>
  by 
    simp 
    ring

@[simp]
theorem translation_number_conj_eq (f : Units CircleDeg1Lift) (g : CircleDeg1Lift) :
  τ ((«expr↑ » f*g)*«expr↑ » (f⁻¹)) = τ g :=
  (translation_number_eq_of_semiconj_by (f.mk_semiconj_by g)).symm

@[simp]
theorem translation_number_conj_eq' (f : Units CircleDeg1Lift) (g : CircleDeg1Lift) : τ ((«expr↑ » (f⁻¹)*g)*f) = τ g :=
  translation_number_conj_eq (f⁻¹) g

theorem dist_pow_map_zero_mul_translation_number_le (n : ℕ) : dist ((f ^ n) 0) (n*f.translation_number) ≤ 1 :=
  f.translation_number_pow n ▸ (f ^ n).dist_map_zero_translation_number_le

-- error in Dynamics.Circle.RotationNumber.TranslationNumber: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_translation_number₀' : tendsto (λ
 n : exprℕ(), «expr / »(«expr ^ »(f, «expr + »(n, 1)) 0, «expr + »(n, 1))) at_top «expr $ »(expr𝓝(), exprτ() f) :=
begin
  refine [expr «expr $ »(tendsto_iff_dist_tendsto_zero.2, squeeze_zero (λ
     _, dist_nonneg) (λ n, _) ((tendsto_const_div_at_top_nhds_0_nat 1).comp (tendsto_add_at_top_nat 1)))],
  dsimp [] [] [] [],
  have [] [":", expr «expr < »((0 : exprℝ()), «expr + »(n, 1))] [":=", expr n.cast_add_one_pos],
  rw ["[", expr real.dist_eq, ",", expr div_sub' _ _ _ (ne_of_gt this), ",", expr abs_div, ",", "<-", expr real.dist_eq, ",", expr abs_of_pos this, ",", expr div_le_div_right this, ",", "<-", expr nat.cast_add_one, "]"] [],
  apply [expr dist_pow_map_zero_mul_translation_number_le]
end

theorem tendsto_translation_number₀ : tendsto (fun n : ℕ => (f ^ n) 0 / n) at_top (𝓝$ τ f) :=
  (tendsto_add_at_top_iff_nat 1).1 f.tendsto_translation_number₀'

/-- For any `x : ℝ` the sequence $\frac{f^n(x)-x}{n}$ tends to the translation number of `f`.
In particular, this limit does not depend on `x`. -/
theorem tendsto_translation_number (x : ℝ) : tendsto (fun n : ℕ => ((f ^ n) x - x) / n) at_top (𝓝$ τ f) :=
  by 
    rw [←translation_number_conj_eq' (translate$ Multiplicative.ofAdd x)]
    convert tendsto_translation_number₀ _ 
    ext n 
    simp [sub_eq_neg_add, Units.conj_pow']

theorem tendsto_translation_number' (x : ℝ) : tendsto (fun n : ℕ => ((f ^ n+1) x - x) / n+1) at_top (𝓝$ τ f) :=
  (tendsto_add_at_top_iff_nat 1).2 (f.tendsto_translation_number x)

theorem translation_number_mono : Monotone τ :=
  fun f g h =>
    le_of_tendsto_of_tendsto' f.tendsto_translation_number₀ g.tendsto_translation_number₀$
      fun n => div_le_div_of_le_of_nonneg (pow_mono h n 0) n.cast_nonneg

theorem translation_number_translate (x : ℝ) : τ (translate$ Multiplicative.ofAdd x) = x :=
  translation_number_eq_of_tendsto₀' _$
    by 
      simp [Nat.cast_add_one_ne_zero, mul_div_cancel_left, tendsto_const_nhds]

theorem translation_number_le_of_le_add {z : ℝ} (hz : ∀ x, f x ≤ x+z) : τ f ≤ z :=
  translation_number_translate z ▸ translation_number_mono fun x => trans_rel_left _ (hz x) (add_commₓ _ _)

theorem le_translation_number_of_add_le {z : ℝ} (hz : ∀ x, (x+z) ≤ f x) : z ≤ τ f :=
  translation_number_translate z ▸ translation_number_mono fun x => trans_rel_right _ (add_commₓ _ _) (hz x)

theorem translation_number_le_of_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x+m) : τ f ≤ m :=
  le_of_tendsto' (f.tendsto_translation_number' x)$
    fun n =>
      (div_le_iff' (n.cast_add_one_pos : (0 : ℝ) < _)).mpr$
        sub_le_iff_le_add'.2$ (coe_pow f (n+1)).symm ▸ f.iterate_le_of_map_le_add_int h (n+1)

theorem translation_number_le_of_le_add_nat {x : ℝ} {m : ℕ} (h : f x ≤ x+m) : τ f ≤ m :=
  @translation_number_le_of_le_add_int f x m h

theorem le_translation_number_of_add_int_le {x : ℝ} {m : ℤ} (h : (x+m) ≤ f x) : «expr↑ » m ≤ τ f :=
  ge_of_tendsto' (f.tendsto_translation_number' x)$
    fun n =>
      (le_div_iff (n.cast_add_one_pos : (0 : ℝ) < _)).mpr$
        le_sub_iff_add_le'.2$
          by 
            simp only [coe_pow, mul_commₓ (m : ℝ), ←Nat.cast_add_one, f.le_iterate_of_add_int_le_map h]

theorem le_translation_number_of_add_nat_le {x : ℝ} {m : ℕ} (h : (x+m) ≤ f x) : «expr↑ » m ≤ τ f :=
  @le_translation_number_of_add_int_le f x m h

/-- If `f x - x` is an integer number `m` for some point `x`, then `τ f = m`.
On the circle this means that a map with a fixed point has rotation number zero. -/
theorem translation_number_of_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x+m) : τ f = m :=
  le_antisymmₓ (translation_number_le_of_le_add_int f$ le_of_eqₓ h)
    (le_translation_number_of_add_int_le f$ le_of_eqₓ h.symm)

theorem floor_sub_le_translation_number (x : ℝ) : «expr↑ » ⌊f x - x⌋ ≤ τ f :=
  le_translation_number_of_add_int_le f$ le_sub_iff_add_le'.1 (floor_le$ f x - x)

theorem translation_number_le_ceil_sub (x : ℝ) : τ f ≤ ⌈f x - x⌉ :=
  translation_number_le_of_le_add_int f$ sub_le_iff_le_add'.1 (le_ceil$ f x - x)

theorem map_lt_of_translation_number_lt_int {n : ℤ} (h : τ f < n) (x : ℝ) : f x < x+n :=
  not_leₓ.1$ mt f.le_translation_number_of_add_int_le$ not_leₓ.2 h

theorem map_lt_of_translation_number_lt_nat {n : ℕ} (h : τ f < n) (x : ℝ) : f x < x+n :=
  @map_lt_of_translation_number_lt_int f n h x

theorem map_lt_add_floor_translation_number_add_one (x : ℝ) : f x < (x+⌊τ f⌋)+1 :=
  by 
    rw [add_assocₓ]
    normCast 
    refine' map_lt_of_translation_number_lt_int _ _ _ 
    pushCast 
    exact lt_floor_add_one _

theorem map_lt_add_translation_number_add_one (x : ℝ) : f x < (x+τ f)+1 :=
  calc f x < (x+⌊τ f⌋)+1 := f.map_lt_add_floor_translation_number_add_one x 
    _ ≤ (x+τ f)+1 :=
    by 
      mono*
      exact floor_le (τ f)
    

theorem lt_map_of_int_lt_translation_number {n : ℤ} (h : «expr↑ » n < τ f) (x : ℝ) : (x+n) < f x :=
  not_leₓ.1$ mt f.translation_number_le_of_le_add_int$ not_leₓ.2 h

theorem lt_map_of_nat_lt_translation_number {n : ℕ} (h : «expr↑ » n < τ f) (x : ℝ) : (x+n) < f x :=
  @lt_map_of_int_lt_translation_number f n h x

-- error in Dynamics.Circle.RotationNumber.TranslationNumber: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f^n x - x`, `n > 0`, is an integer number `m` for some point `x`, then
`τ f = m / n`. On the circle this means that a map with a periodic orbit has
a rational rotation number. -/
theorem translation_number_of_map_pow_eq_add_int
{x : exprℝ()}
{n : exprℕ()}
{m : exprℤ()}
(h : «expr = »(«expr ^ »(f, n) x, «expr + »(x, m)))
(hn : «expr < »(0, n)) : «expr = »(exprτ() f, «expr / »(m, n)) :=
begin
  have [] [] [":=", expr «expr ^ »(f, n).translation_number_of_eq_add_int h],
  rwa ["[", expr translation_number_pow, ",", expr mul_comm, ",", "<-", expr eq_div_iff, "]"] ["at", ident this],
  exact [expr nat.cast_ne_zero.2 (ne_of_gt hn)]
end

/-- If a predicate depends only on `f x - x` and holds for all `0 ≤ x ≤ 1`,
then it holds for all `x`. -/
theorem forall_map_sub_of_Icc (P : ℝ → Prop) (h : ∀ x _ : x ∈ Icc (0 : ℝ) 1, P (f x - x)) (x : ℝ) : P (f x - x) :=
  f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_ltₓ (fract_lt_one _)⟩

theorem translation_number_lt_of_forall_lt_add (hf : Continuous f) {z : ℝ} (hz : ∀ x, f x < x+z) : τ f < z :=
  by 
    obtain ⟨x, xmem, hx⟩ : ∃ (x : _)(_ : x ∈ Icc (0 : ℝ) 1), ∀ y _ : y ∈ Icc (0 : ℝ) 1, f y - y ≤ f x - x 
    exact is_compact_Icc.exists_forall_ge (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).ContinuousOn 
    refine' lt_of_le_of_ltₓ _ (sub_lt_iff_lt_add'.2$ hz x)
    apply translation_number_le_of_le_add 
    simp only [←sub_le_iff_le_add']
    exact f.forall_map_sub_of_Icc (fun a => a ≤ f x - x) hx

theorem lt_translation_number_of_forall_add_lt (hf : Continuous f) {z : ℝ} (hz : ∀ x, (x+z) < f x) : z < τ f :=
  by 
    obtain ⟨x, xmem, hx⟩ : ∃ (x : _)(_ : x ∈ Icc (0 : ℝ) 1), ∀ y _ : y ∈ Icc (0 : ℝ) 1, f x - x ≤ f y - y 
    exact is_compact_Icc.exists_forall_le (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).ContinuousOn 
    refine' lt_of_lt_of_leₓ (lt_sub_iff_add_lt'.2$ hz x) _ 
    apply le_translation_number_of_add_le 
    simp only [←le_sub_iff_add_le']
    exact f.forall_map_sub_of_Icc _ hx

/-- If `f` is a continuous monotone map `ℝ → ℝ`, `f (x + 1) = f x + 1`, then there exists `x`
such that `f x = x + τ f`. -/
theorem exists_eq_add_translation_number (hf : Continuous f) : ∃ x, f x = x+τ f :=
  by 
    obtain ⟨a, ha⟩ : ∃ x, f x ≤ x+f.translation_number
    ·
      byContra H 
      pushNeg  at H 
      exact lt_irreflₓ _ (f.lt_translation_number_of_forall_add_lt hf H)
    obtain ⟨b, hb⟩ : ∃ x, (x+τ f) ≤ f x
    ·
      byContra H 
      pushNeg  at H 
      exact lt_irreflₓ _ (f.translation_number_lt_of_forall_lt_add hf H)
    exact intermediate_value_univ₂ hf (continuous_id.add continuous_const) ha hb

theorem translation_number_eq_int_iff (hf : Continuous f) {m : ℤ} : τ f = m ↔ ∃ x, f x = x+m :=
  by 
    refine' ⟨fun h => h ▸ f.exists_eq_add_translation_number hf, _⟩
    rintro ⟨x, hx⟩
    exact f.translation_number_of_eq_add_int hx

theorem continuous_pow (hf : Continuous f) (n : ℕ) : Continuous («expr⇑ » (f ^ n : CircleDeg1Lift)) :=
  by 
    rw [coe_pow]
    exact hf.iterate n

theorem translation_number_eq_rat_iff (hf : Continuous f) {m : ℤ} {n : ℕ} (hn : 0 < n) :
  τ f = m / n ↔ ∃ x, (f ^ n) x = x+m :=
  by 
    rw [eq_div_iff, mul_commₓ, ←translation_number_pow] <;> [skip, exact ne_of_gtₓ (Nat.cast_pos.2 hn)]
    exact (f ^ n).translation_number_eq_int_iff (f.continuous_pow hf n)

-- error in Dynamics.Circle.RotationNumber.TranslationNumber: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Consider two actions `f₁ f₂ : G →* circle_deg1_lift` of a group on the real line by lifts of
orientation preserving circle homeomorphisms. Suppose that for each `g : G` the homeomorphisms
`f₁ g` and `f₂ g` have equal rotation numbers. Then there exists `F : circle_deg1_lift`  such that
`F * f₁ g = f₂ g * F` for all `g : G`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
theorem semiconj_of_group_action_of_forall_translation_number_eq
{G : Type*}
[group G]
(f₁ f₂ : «expr →* »(G, circle_deg1_lift))
(h : ∀
 g, «expr = »(exprτ() (f₁ g), exprτ() (f₂ g))) : «expr∃ , »((F : circle_deg1_lift), ∀ g, semiconj F (f₁ g) (f₂ g)) :=
begin
  have [] [":", expr ∀ x, bdd_above «expr $ »(range, λ g, f₂ «expr ⁻¹»(g) (f₁ g x))] [],
  { refine [expr λ x, ⟨«expr + »(x, 2), _⟩],
    rintro ["_", "⟨", ident g, ",", ident rfl, "⟩"],
    have [] [":", expr «expr = »(exprτ() (f₂ «expr ⁻¹»(g)), «expr- »(exprτ() (f₂ g)))] [],
    by rw ["[", "<-", expr monoid_hom.coe_to_hom_units, ",", expr monoid_hom.map_inv, ",", expr translation_number_units_inv, ",", expr monoid_hom.coe_to_hom_units, "]"] [],
    calc
      «expr ≤ »(f₂ «expr ⁻¹»(g) (f₁ g x), f₂ «expr ⁻¹»(g) «expr + »(«expr + »(x, exprτ() (f₁ g)), 1)) : mono _ (map_lt_add_translation_number_add_one _ _).le
      «expr = »(..., «expr + »(f₂ «expr ⁻¹»(g) «expr + »(x, exprτ() (f₂ g)), 1)) : by rw ["[", expr h, ",", expr map_add_one, "]"] []
      «expr ≤ »(..., «expr + »(«expr + »(«expr + »(«expr + »(x, exprτ() (f₂ g)), exprτ() (f₂ «expr ⁻¹»(g))), 1), 1)) : by { mono [] [] [] [],
        exact [expr (map_lt_add_translation_number_add_one _ _).le] }
      «expr = »(..., «expr + »(x, 2)) : by simp [] [] [] ["[", expr this, ",", expr bit0, ",", expr add_assoc, "]"] [] [] },
  set [] [ident F₁] [] [":="] [expr to_order_iso.comp f₁.to_hom_units] [],
  set [] [ident F₂] [] [":="] [expr to_order_iso.comp f₂.to_hom_units] [],
  have [ident hF₁] [":", expr ∀ g, «expr = »(«expr⇑ »(F₁ g), f₁ g)] [":=", expr λ _, rfl],
  have [ident hF₂] [":", expr ∀ g, «expr = »(«expr⇑ »(F₂ g), f₂ g)] [":=", expr λ _, rfl],
  simp [] [] ["only"] ["[", "<-", expr hF₁, ",", "<-", expr hF₂, "]"] [] [],
  refine [expr ⟨⟨_, λ
     x
     y
     hxy, _, λ
     x, _⟩, cSup_div_semiconj F₂ F₁ (λ
     x, _)⟩]; simp [] [] ["only"] ["[", expr hF₁, ",", expr hF₂, ",", "<-", expr monoid_hom.map_inv, ",", expr coe_mk, "]"] [] [],
  { refine [expr csupr_le_csupr (this y) (λ g, _)],
    exact [expr mono _ (mono _ hxy)] },
  { simp [] [] ["only"] ["[", expr map_add_one, "]"] [] [],
    exact [expr (map_csupr_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) (monotone_id.add_const (1 : exprℝ())) (this x)).symm] },
  { exact [expr this x] }
end

-- error in Dynamics.Circle.RotationNumber.TranslationNumber: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses arguments `f₁ f₂ : units circle_deg1_lift`
to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem units_semiconj_of_translation_number_eq
{f₁ f₂ : units circle_deg1_lift}
(h : «expr = »(exprτ() f₁, exprτ() f₂)) : «expr∃ , »((F : circle_deg1_lift), semiconj F f₁ f₂) :=
begin
  have [] [":", expr ∀
   n : multiplicative exprℤ(), «expr = »(exprτ() ((units.coe_hom _).comp (zpowers_hom _ f₁) n), exprτ() ((units.coe_hom _).comp (zpowers_hom _ f₂) n))] [],
  { intro [ident n],
    simp [] [] [] ["[", expr h, "]"] [] [] },
  exact [expr (semiconj_of_group_action_of_forall_translation_number_eq _ _ this).imp (λ
    F hF, hF (multiplicative.of_add 1))]
end

/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses assumptions `is_unit f₁` and `is_unit f₂`
to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem semiconj_of_is_unit_of_translation_number_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : IsUnit f₁) (h₂ : IsUnit f₂)
  (h : τ f₁ = τ f₂) : ∃ F : CircleDeg1Lift, semiconj F f₁ f₂ :=
  by 
    rcases h₁, h₂ with ⟨⟨f₁, rfl⟩, ⟨f₂, rfl⟩⟩
    exact units_semiconj_of_translation_number_eq h

/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `circle_deg1_lift`. This version uses assumptions `bijective f₁` and
`bijective f₂` to assume that `f₁` and `f₂` are homeomorphisms. -/
theorem semiconj_of_bijective_of_translation_number_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : bijective f₁) (h₂ : bijective f₂)
  (h : τ f₁ = τ f₂) : ∃ F : CircleDeg1Lift, semiconj F f₁ f₂ :=
  semiconj_of_is_unit_of_translation_number_eq (is_unit_iff_bijective.2 h₁) (is_unit_iff_bijective.2 h₂) h

end CircleDeg1Lift

