import Mathbin.Algebra.Ring.Basic
import Mathbin.Algebra.Group.Opposite

/-!
# Ring structures on the multiplicative opposite
-/


universe u v

variable (α : Type u)

namespace MulOpposite

instance [Distrib α] : Distrib (αᵐᵒᵖ) :=
  { MulOpposite.hasAdd α, MulOpposite.hasMul α with
    left_distrib := fun x y z => unop_injective $ add_mulₓ (unop y) (unop z) (unop x),
    right_distrib := fun x y z => unop_injective $ mul_addₓ (unop z) (unop x) (unop y) }

instance [MulZeroClass α] : MulZeroClass (αᵐᵒᵖ) where
  zero := 0
  mul := · * ·
  zero_mul := fun x => unop_injective $ mul_zero $ unop x
  mul_zero := fun x => unop_injective $ zero_mul $ unop x

instance [MulZeroOneClass α] : MulZeroOneClass (αᵐᵒᵖ) :=
  { MulOpposite.mulZeroClass α, MulOpposite.mulOneClass α with }

instance [SemigroupWithZero α] : SemigroupWithZero (αᵐᵒᵖ) :=
  { MulOpposite.semigroup α, MulOpposite.mulZeroClass α with }

instance [MonoidWithZeroₓ α] : MonoidWithZeroₓ (αᵐᵒᵖ) :=
  { MulOpposite.monoid α, MulOpposite.mulZeroOneClass α with }

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (αᵐᵒᵖ) :=
  { MulOpposite.addCommMonoid α, MulOpposite.mulZeroClass α, MulOpposite.distrib α with }

instance [NonUnitalSemiring α] : NonUnitalSemiring (αᵐᵒᵖ) :=
  { MulOpposite.semigroupWithZero α, MulOpposite.nonUnitalNonAssocSemiring α with }

instance [NonAssocSemiring α] : NonAssocSemiring (αᵐᵒᵖ) :=
  { MulOpposite.mulZeroOneClass α, MulOpposite.nonUnitalNonAssocSemiring α with }

instance [Semiringₓ α] : Semiringₓ (αᵐᵒᵖ) :=
  { MulOpposite.nonUnitalSemiring α, MulOpposite.nonAssocSemiring α, MulOpposite.monoidWithZero α with }

instance [CommSemiringₓ α] : CommSemiringₓ (αᵐᵒᵖ) :=
  { MulOpposite.semiring α, MulOpposite.commSemigroup α with }

instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (αᵐᵒᵖ) :=
  { MulOpposite.addCommGroup α, MulOpposite.mulZeroClass α, MulOpposite.distrib α with }

instance [Ringₓ α] : Ringₓ (αᵐᵒᵖ) :=
  { MulOpposite.addCommGroup α, MulOpposite.monoid α, MulOpposite.semiring α with }

instance [CommRingₓ α] : CommRingₓ (αᵐᵒᵖ) :=
  { MulOpposite.ring α, MulOpposite.commSemiring α with }

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (αᵐᵒᵖ) where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun x y H : op (_ * _) = op (0 : α) =>
    Or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero $ op_injective H) (fun hy => Or.inr $ unop_injective $ hy) fun hx =>
      Or.inl $ unop_injective $ hx

instance [Ringₓ α] [IsDomain α] : IsDomain (αᵐᵒᵖ) :=
  { MulOpposite.no_zero_divisors α, MulOpposite.ring α, MulOpposite.nontrivial α with }

instance [GroupWithZeroₓ α] : GroupWithZeroₓ (αᵐᵒᵖ) :=
  { MulOpposite.monoidWithZero α, MulOpposite.divInvMonoid α, MulOpposite.nontrivial α with
    mul_inv_cancel := fun x hx => unop_injective $ inv_mul_cancel $ unop_injective.Ne hx,
    inv_zero := unop_injective inv_zero }

end MulOpposite

open MulOpposite

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := ff })]
def RingHom.toOpposite {R S : Type _} [Semiringₓ R] [Semiringₓ S] (f : R →+* S) (hf : ∀ x y, Commute (f x) (f y)) :
    R →+* Sᵐᵒᵖ :=
  { ((op_add_equiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp (↑f) : R →+ Sᵐᵒᵖ), f.to_monoid_hom.to_opposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A monoid homomorphism `f : R →* S` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := ff })]
def RingHom.fromOpposite {R S : Type _} [Semiringₓ R] [Semiringₓ S] (f : R →+* S) (hf : ∀ x y, Commute (f x) (f y)) :
    Rᵐᵒᵖ →+* S :=
  { (f.to_add_monoid_hom.comp (op_add_equiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.to_monoid_hom.from_opposite hf with toFun := f ∘ MulOpposite.unop }

/-- A ring hom `α →+* β` can equivalently be viewed as a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def RingHom.op {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (α →+* β) ≃ (αᵐᵒᵖ →+* βᵐᵒᵖ) where
  toFun := fun f => { f.to_add_monoid_hom.mul_op, f.to_monoid_hom.op with }
  invFun := fun f => { f.to_add_monoid_hom.mul_unop, f.to_monoid_hom.unop with }
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    simp

/-- The 'unopposite' of a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. Inverse to `ring_hom.op`. -/
@[simp]
def RingHom.unop {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (αᵐᵒᵖ →+* βᵐᵒᵖ) ≃ (α →+* β) :=
  RingHom.op.symm

