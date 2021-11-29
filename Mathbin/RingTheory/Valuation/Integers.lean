import Mathbin.RingTheory.Valuation.Basic

/-!
# Ring of integers under a given valuation

The elements with valuation less than or equal to 1.

TODO: Define characteristic predicate.
-/


universe u v w

namespace Valuation

section Ringₓ

variable{R : Type u}{Γ₀ : Type v}[Ringₓ R][LinearOrderedCommGroupWithZero Γ₀]

variable(v : Valuation R Γ₀)

/-- The ring of integers under a given valuation is the subring of elements with valuation ≤ 1. -/
def integer : Subring R :=
  { Carrier := { x | v x ≤ 1 }, one_mem' := le_of_eqₓ v.map_one,
    mul_mem' := fun x y hx hy => trans_rel_right (· ≤ ·) (v.map_mul x y) (mul_le_one' hx hy),
    zero_mem' := trans_rel_right (· ≤ ·) v.map_zero zero_le_one',
    add_mem' := fun x y hx hy => le_transₓ (v.map_add x y) (max_leₓ hx hy),
    neg_mem' := fun x hx => trans_rel_right (· ≤ ·) (v.map_neg x) hx }

end Ringₓ

section CommRingₓ

variable{R : Type u}{Γ₀ : Type v}[CommRingₓ R][LinearOrderedCommGroupWithZero Γ₀]

variable(v : Valuation R Γ₀)

variable(O : Type w)[CommRingₓ O][Algebra O R]

/-- Given a valuation v : R → Γ₀ and a ring homomorphism O →+* R, we say that O is the integers of v
if f is injective, and its range is exactly `v.integer`. -/
structure integers : Prop where 
  hom_inj : Function.Injective (algebraMap O R)
  map_le_one : ∀ x, v (algebraMap O R x) ≤ 1 
  exists_of_le_one : ∀ ⦃r⦄, v r ≤ 1 → ∃ x, algebraMap O R x = r

instance  : Algebra v.integer R :=
  Algebra.ofSubring v.integer

theorem integer.integers : v.integers v.integer :=
  { hom_inj := Subtype.coe_injective, map_le_one := fun r => r.2, exists_of_le_one := fun r hr => ⟨⟨r, hr⟩, rfl⟩ }

namespace Integers

variable{v O}(hv : integers v O)

include hv

theorem one_of_is_unit {x : O} (hx : IsUnit x) : v (algebraMap O R x) = 1 :=
  let ⟨u, hu⟩ := hx 
  le_antisymmₓ (hv.2 _)$
    by 
      rw [←v.map_one, ←(algebraMap O R).map_one, ←u.mul_inv, ←mul_oneₓ (v (algebraMap O R x)), hu,
        (algebraMap O R).map_mul, v.map_mul]
      exact mul_le_mul_left' (hv.2 (u⁻¹ : Units O)) _

theorem is_unit_of_one {x : O} (hx : IsUnit (algebraMap O R x)) (hvx : v (algebraMap O R x) = 1) : IsUnit x :=
  let ⟨u, hu⟩ := hx 
  have h1 : v u ≤ 1 := hu.symm ▸ hv.2 x 
  have h2 : v (u⁻¹ : Units R) ≤ 1 :=
    by 
      rw [←one_mulₓ (v _), ←hvx, ←v.map_mul, ←hu, u.mul_inv, hu, hvx, v.map_one]
  let ⟨r1, hr1⟩ := hv.3 h1 
  let ⟨r2, hr2⟩ := hv.3 h2
  ⟨⟨r1, r2,
      hv.1$
        by 
          rw [RingHom.map_mul, RingHom.map_one, hr1, hr2, Units.mul_inv],
      hv.1$
        by 
          rw [RingHom.map_mul, RingHom.map_one, hr1, hr2, Units.inv_mul]⟩,
    hv.1$ hr1.trans hu⟩

theorem le_of_dvd {x y : O} (h : x ∣ y) : v (algebraMap O R y) ≤ v (algebraMap O R x) :=
  let ⟨z, hz⟩ := h 
  by 
    rw [←mul_oneₓ (v (algebraMap O R x)), hz, RingHom.map_mul, v.map_mul]
    exact mul_le_mul_left' (hv.2 z) _

end Integers

end CommRingₓ

section Field

variable{F : Type u}{Γ₀ : Type v}[Field F][LinearOrderedCommGroupWithZero Γ₀]

variable{v : Valuation F Γ₀}{O : Type w}[CommRingₓ O][Algebra O F](hv : integers v O)

include hv

namespace Integers

-- error in RingTheory.Valuation.Integers: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dvd_of_le {x y : O} (h : «expr ≤ »(v (algebra_map O F x), v (algebra_map O F y))) : «expr ∣ »(y, x) :=
«expr $ »(classical.by_cases (λ
  hy : «expr = »(algebra_map O F y, 0), have hx : «expr = »(x, 0), from «expr $ »(hv.1, «expr ▸ »((algebra_map O F).map_zero.symm, «expr $ »(v.zero_iff.1, le_zero_iff.1 «expr ▸ »(v.map_zero, «expr ▸ »(hy, h))))),
  «expr ▸ »(hx.symm, dvd_zero y)), λ
 hy : «expr ≠ »(algebra_map O F y, 0), have «expr ≤ »(v «expr * »(«expr ⁻¹»(algebra_map O F y), algebra_map O F x), 1), by { rw ["[", "<-", expr v.map_one, ",", "<-", expr inv_mul_cancel hy, ",", expr v.map_mul, ",", expr v.map_mul, "]"] [],
   exact [expr mul_le_mul_left' h _] },
 let ⟨z, hz⟩ := hv.3 this in
 ⟨z, «expr $ »(hv.1, «expr ▸ »(((algebra_map O F).map_mul y z).symm, «expr ▸ »(hz.symm, (mul_inv_cancel_left₀ hy _).symm)))⟩)

theorem dvd_iff_le {x y : O} : x ∣ y ↔ v (algebraMap O F y) ≤ v (algebraMap O F x) :=
  ⟨hv.le_of_dvd, hv.dvd_of_le⟩

theorem le_iff_dvd {x y : O} : v (algebraMap O F x) ≤ v (algebraMap O F y) ↔ y ∣ x :=
  ⟨hv.dvd_of_le, hv.le_of_dvd⟩

end Integers

end Field

end Valuation

