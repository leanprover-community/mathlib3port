import Mathbin.Algebra.Algebra.Basic 
import Mathbin.Topology.LocallyConstant.Basic

/-!
# Algebraic structure on locally constant functions

This file puts algebraic structure (`add_group`, etc)
on the type of locally constant functions.

-/


namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X]

@[toAdditive]
instance [HasOne Y] : HasOne (LocallyConstant X Y) :=
  { one := const X 1 }

@[simp, toAdditive]
theorem coe_one [HasOne Y] : ⇑(1 : LocallyConstant X Y) = (1 : X → Y) :=
  rfl

@[toAdditive]
theorem one_apply [HasOne Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
  rfl

@[toAdditive]
instance [HasInv Y] : HasInv (LocallyConstant X Y) :=
  { inv := fun f => ⟨f⁻¹, f.is_locally_constant.inv⟩ }

@[simp, toAdditive]
theorem coe_inv [HasInv Y] (f : LocallyConstant X Y) : ⇑f⁻¹ = f⁻¹ :=
  rfl

@[toAdditive]
theorem inv_apply [HasInv Y] (f : LocallyConstant X Y) (x : X) : (f⁻¹) x = f x⁻¹ :=
  rfl

@[toAdditive]
instance [Mul Y] : Mul (LocallyConstant X Y) :=
  { mul := fun f g => ⟨f*g, f.is_locally_constant.mul g.is_locally_constant⟩ }

@[simp, toAdditive]
theorem coe_mul [Mul Y] (f g : LocallyConstant X Y) : (⇑f*g) = f*g :=
  rfl

@[toAdditive]
theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f*g) x = f x*g x :=
  rfl

@[toAdditive]
instance [MulOneClass Y] : MulOneClass (LocallyConstant X Y) :=
  { LocallyConstant.hasOne, LocallyConstant.hasMul with
    one_mul :=
      by 
        intros 
        ext 
        simp only [mul_apply, one_apply, one_mulₓ],
    mul_one :=
      by 
        intros 
        ext 
        simp only [mul_apply, one_apply, mul_oneₓ] }

/-- `coe_fn` is a `monoid_hom`. -/
@[toAdditive "`coe_fn` is an `add_monoid_hom`.", simps]
def coe_fn_monoid_hom [MulOneClass Y] : LocallyConstant X Y →* X → Y :=
  { toFun := coeFn, map_one' := rfl, map_mul' := fun _ _ => rfl }

/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[toAdditive "The constant-function embedding, as an additive monoid hom.", simps]
def const_monoid_hom [MulOneClass Y] : Y →* LocallyConstant X Y :=
  { toFun := const X, map_one' := rfl, map_mul' := fun _ _ => rfl }

instance [MulZeroClass Y] : MulZeroClass (LocallyConstant X Y) :=
  { LocallyConstant.hasZero, LocallyConstant.hasMul with
    zero_mul :=
      by 
        intros 
        ext 
        simp only [mul_apply, zero_apply, zero_mul],
    mul_zero :=
      by 
        intros 
        ext 
        simp only [mul_apply, zero_apply, mul_zero] }

instance [MulZeroOneClass Y] : MulZeroOneClass (LocallyConstant X Y) :=
  { LocallyConstant.mulZeroClass, LocallyConstant.mulOneClass with  }

@[toAdditive]
instance [Div Y] : Div (LocallyConstant X Y) :=
  { div := fun f g => ⟨f / g, f.is_locally_constant.div g.is_locally_constant⟩ }

@[toAdditive]
theorem coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g :=
  rfl

@[toAdditive]
theorem div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / g x :=
  rfl

@[toAdditive]
instance [Semigroupₓ Y] : Semigroupₓ (LocallyConstant X Y) :=
  { LocallyConstant.hasMul with
    mul_assoc :=
      by 
        intros 
        ext 
        simp only [mul_apply, mul_assocₓ] }

instance [SemigroupWithZero Y] : SemigroupWithZero (LocallyConstant X Y) :=
  { LocallyConstant.mulZeroClass, LocallyConstant.semigroup with  }

@[toAdditive]
instance [CommSemigroupₓ Y] : CommSemigroupₓ (LocallyConstant X Y) :=
  { LocallyConstant.semigroup with
    mul_comm :=
      by 
        intros 
        ext 
        simp only [mul_apply, mul_commₓ] }

@[toAdditive]
instance [Monoidₓ Y] : Monoidₓ (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.mulOneClass with mul := ·*· }

@[toAdditive]
instance [CommMonoidₓ Y] : CommMonoidₓ (LocallyConstant X Y) :=
  { LocallyConstant.commSemigroup, LocallyConstant.monoid with  }

@[toAdditive]
instance [Groupₓ Y] : Groupₓ (LocallyConstant X Y) :=
  { LocallyConstant.monoid, LocallyConstant.hasInv, LocallyConstant.hasDiv with
    mul_left_inv :=
      by 
        intros 
        ext 
        simp only [mul_apply, inv_apply, one_apply, mul_left_invₓ],
    div_eq_mul_inv :=
      by 
        intros 
        ext 
        simp only [mul_apply, inv_apply, div_apply, div_eq_mul_inv] }

@[toAdditive]
instance [CommGroupₓ Y] : CommGroupₓ (LocallyConstant X Y) :=
  { LocallyConstant.commMonoid, LocallyConstant.group with  }

instance [Distrib Y] : Distrib (LocallyConstant X Y) :=
  { LocallyConstant.hasAdd, LocallyConstant.hasMul with
    left_distrib :=
      by 
        intros 
        ext 
        simp only [mul_apply, add_apply, mul_addₓ],
    right_distrib :=
      by 
        intros 
        ext 
        simp only [mul_apply, add_apply, add_mulₓ] }

instance [NonUnitalNonAssocSemiring Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y) :=
  { LocallyConstant.addCommMonoid, LocallyConstant.hasMul, LocallyConstant.distrib, LocallyConstant.mulZeroClass with  }

instance [NonUnitalSemiring Y] : NonUnitalSemiring (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.nonUnitalNonAssocSemiring with  }

instance [NonAssocSemiring Y] : NonAssocSemiring (LocallyConstant X Y) :=
  { LocallyConstant.mulOneClass, LocallyConstant.nonUnitalNonAssocSemiring with  }

/-- The constant-function embedding, as a ring hom.  -/
@[simps]
def const_ring_hom [NonAssocSemiring Y] : Y →+* LocallyConstant X Y :=
  { const_monoid_hom, const_add_monoid_hom with toFun := const X }

instance [Semiringₓ Y] : Semiringₓ (LocallyConstant X Y) :=
  { LocallyConstant.addCommMonoid, LocallyConstant.monoid, LocallyConstant.distrib, LocallyConstant.mulZeroClass with  }

instance [CommSemiringₓ Y] : CommSemiringₓ (LocallyConstant X Y) :=
  { LocallyConstant.semiring, LocallyConstant.commMonoid with  }

instance [Ringₓ Y] : Ringₓ (LocallyConstant X Y) :=
  { LocallyConstant.semiring, LocallyConstant.addCommGroup with  }

instance [CommRingₓ Y] : CommRingₓ (LocallyConstant X Y) :=
  { LocallyConstant.commSemiring, LocallyConstant.ring with  }

variable {R : Type _}

instance [HasScalar R Y] : HasScalar R (LocallyConstant X Y) :=
  { smul := fun r f => { toFun := r • f, IsLocallyConstant := ((IsLocallyConstant f).comp ((· • ·) r) : _) } }

@[simp]
theorem coe_smul [HasScalar R Y] (r : R) (f : LocallyConstant X Y) : ⇑(r • f) = r • f :=
  rfl

theorem smul_apply [HasScalar R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
  rfl

instance [Monoidₓ R] [MulAction R Y] : MulAction R (LocallyConstant X Y) :=
  Function.Injective.mulAction _ coe_injective fun _ _ => rfl

instance [Monoidₓ R] [AddMonoidₓ Y] [DistribMulAction R Y] : DistribMulAction R (LocallyConstant X Y) :=
  Function.Injective.distribMulAction coe_fn_add_monoid_hom coe_injective fun _ _ => rfl

instance [Semiringₓ R] [AddCommMonoidₓ Y] [Module R Y] : Module R (LocallyConstant X Y) :=
  Function.Injective.module R coe_fn_add_monoid_hom coe_injective fun _ _ => rfl

section Algebra

variable [CommSemiringₓ R] [Semiringₓ Y] [Algebra R Y]

instance : Algebra R (LocallyConstant X Y) :=
  { toRingHom := const_ring_hom.comp$ algebraMap R Y,
    commutes' :=
      by 
        intros 
        ext 
        exact Algebra.commutes' _ _,
    smul_def' :=
      by 
        intros 
        ext 
        exact Algebra.smul_def' _ _ }

@[simp]
theorem coe_algebra_map (r : R) : ⇑algebraMap R (LocallyConstant X Y) r = algebraMap R (X → Y) r :=
  rfl

end Algebra

end LocallyConstant

