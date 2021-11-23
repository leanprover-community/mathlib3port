import Mathbin.Tactic.ApplyFun 
import Mathbin.Algebra.Field.Opposite 
import Mathbin.Algebra.FieldPower 
import Mathbin.Data.Equiv.RingAut 
import Mathbin.GroupTheory.GroupAction.Units 
import Mathbin.GroupTheory.GroupAction.Opposite 
import Mathbin.Algebra.Ring.CompTypeclasses

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/


universe u v

open MulOpposite

/--
Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class HasStar(R : Type u) where 
  star : R → R

variable{R : Type u}

export HasStar(star)

/--
A star operation (e.g. complex conjugate).
-/
add_decl_doc star

/--
Typeclass for a star operation with is involutive.
-/
class HasInvolutiveStar(R : Type u) extends HasStar R where 
  star_involutive : Function.Involutive star

export HasInvolutiveStar(star_involutive)

@[simp]
theorem star_star [HasInvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _

theorem star_injective [HasInvolutiveStar R] : Function.Injective (star : R → R) :=
  star_involutive.Injective

/--
A `*`-monoid is a monoid `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class StarMonoid(R : Type u)[Monoidₓ R] extends HasInvolutiveStar R where 
  star_mul : ∀ r s : R, star (r*s) = star s*star r

export StarMonoid(star_mul)

attribute [simp] star_mul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
theorem star_mul' [CommMonoidₓ R] [StarMonoid R] (x y : R) : star (x*y) = star x*star y :=
  (star_mul x y).trans (mul_commₓ _ _)

/-- `star` as an `mul_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starMulEquiv [Monoidₓ R] [StarMonoid R] : R ≃* «expr ᵐᵒᵖ» R :=
  { (HasInvolutiveStar.star_involutive.toEquiv star).trans op_equiv with toFun := fun x => MulOpposite.op (star x),
    map_mul' := fun x y => (star_mul x y).symm ▸ MulOpposite.op_mul _ _ }

/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def starMulAut [CommMonoidₓ R] [StarMonoid R] : MulAut R :=
  { HasInvolutiveStar.star_involutive.toEquiv star with toFun := star, map_mul' := star_mul' }

variable(R)

@[simp]
theorem star_one [Monoidₓ R] [StarMonoid R] : star (1 : R) = 1 :=
  op_injective$ (starMulEquiv : R ≃* «expr ᵐᵒᵖ» R).map_one.trans (op_one _).symm

variable{R}

@[simp]
theorem star_pow [Monoidₓ R] [StarMonoid R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
  op_injective$ ((starMulEquiv : R ≃* «expr ᵐᵒᵖ» R).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm

@[simp]
theorem star_inv [Groupₓ R] [StarMonoid R] (x : R) : star (x⁻¹) = star x⁻¹ :=
  op_injective$ ((starMulEquiv : R ≃* «expr ᵐᵒᵖ» R).toMonoidHom.map_inv x).trans (op_inv (star x)).symm

@[simp]
theorem star_zpow [Groupₓ R] [StarMonoid R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective$ ((starMulEquiv : R ≃* «expr ᵐᵒᵖ» R).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div [CommGroupₓ R] [StarMonoid R] (x y : R) : star (x / y) = star x / star y :=
  (starMulAut : R ≃* R).toMonoidHom.map_div _ _

section 

open_locale BigOperators

@[simp]
theorem star_prod [CommMonoidₓ R] [StarMonoid R] {α : Type _} (s : Finset α) (f : α → R) :
  star (∏x in s, f x) = ∏x in s, star (f x) :=
  (starMulAut : R ≃* R).map_prod _ _

end 

/--
Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def starMonoidOfComm {R : Type _} [CommMonoidₓ R] : StarMonoid R :=
  { star := id, star_involutive := fun x => rfl, star_mul := mul_commₓ }

section 

attribute [local instance] starMonoidOfComm

/-- Note that since `star_monoid_of_comm` is reducible, `simp` can already prove this. --/
theorem star_id_of_comm {R : Type _} [CommSemiringₓ R] {x : R} : star x = x :=
  rfl

end 

/--
A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition.
-/
class StarAddMonoid(R : Type u)[AddMonoidₓ R] extends HasInvolutiveStar R where 
  star_add : ∀ r s : R, star (r+s) = star r+star s

export StarAddMonoid(star_add)

attribute [simp] star_add

/-- `star` as an `add_equiv` -/
@[simps apply]
def starAddEquiv [AddMonoidₓ R] [StarAddMonoid R] : R ≃+ R :=
  { HasInvolutiveStar.star_involutive.toEquiv star with toFun := star, map_add' := star_add }

variable(R)

@[simp]
theorem star_zero [AddMonoidₓ R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero

variable{R}

@[simp]
theorem star_neg [AddGroupₓ R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _

@[simp]
theorem star_sub [AddGroupₓ R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _

@[simp]
theorem star_nsmul [AddCommMonoidₓ R] [StarAddMonoid R] (x : R) (n : ℕ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _

@[simp]
theorem star_zsmul [AddCommGroupₓ R] [StarAddMonoid R] (x : R) (n : ℤ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _

section 

open_locale BigOperators

@[simp]
theorem star_sum [AddCommMonoidₓ R] [StarAddMonoid R] {α : Type _} (s : Finset α) (f : α → R) :
  star (∑x in s, f x) = ∑x in s, star (f x) :=
  (starAddEquiv : R ≃+ R).map_sum _ _

end 

/--
A `*`-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a `*`-monoid
(i.e. `star (r * s) = star s * star r`).
-/
class StarRing(R : Type u)[Semiringₓ R] extends StarMonoid R where 
  star_add : ∀ r s : R, star (r+s) = star r+star s

instance (priority := 100)StarRing.toStarAddMonoid [Semiringₓ R] [StarRing R] : StarAddMonoid R :=
  { star_add := StarRing.star_add }

/-- `star` as an `ring_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starRingEquiv [Semiringₓ R] [StarRing R] : R ≃+* «expr ᵐᵒᵖ» R :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ «expr ᵐᵒᵖ» R), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }

/-- `star` as a `ring_aut` for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `complex_conjugate` -/
def starRingAut [CommSemiringₓ R] [StarRing R] : RingAut R :=
  { starAddEquiv, starMulAut with toFun := star }

localized [ComplexConjugate] notation "conj" => starRingAut

/-- This is not a simp lemma, since we usually want simp to keep `star_ring_aut` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
theorem star_ring_aut_apply [CommSemiringₓ R] [StarRing R] {x : R} : starRingAut x = star x :=
  rfl

@[simp]
theorem star_ring_aut_self_apply [CommSemiringₓ R] [StarRing R] (x : R) : starRingAut (starRingAut x) = x :=
  star_star x

alias star_ring_aut_self_apply ← Complex.conj_conj

alias star_ring_aut_self_apply ← IsROrC.conj_conj

@[simp]
theorem star_inv' [DivisionRing R] [StarRing R] (x : R) : star (x⁻¹) = star x⁻¹ :=
  op_injective$ ((starRingEquiv : R ≃+* «expr ᵐᵒᵖ» R).toRingHom.map_inv x).trans (op_inv (star x)).symm

@[simp]
theorem star_zpow₀ [DivisionRing R] [StarRing R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective$ ((starRingEquiv : R ≃+* «expr ᵐᵒᵖ» R).toRingHom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div' [Field R] [StarRing R] (x y : R) : star (x / y) = star x / star y :=
  (starRingAut : R ≃+* R).toRingHom.map_div _ _

@[simp]
theorem star_bit0 [Ringₓ R] [StarRing R] (r : R) : star (bit0 r) = bit0 (star r) :=
  by 
    simp [bit0]

@[simp]
theorem star_bit1 [Ringₓ R] [StarRing R] (r : R) : star (bit1 r) = bit1 (star r) :=
  by 
    simp [bit1]

/--
Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def starRingOfComm {R : Type _} [CommSemiringₓ R] : StarRing R :=
  { starMonoidOfComm with star := id, star_add := fun x y => rfl }

/--
An ordered `*`-ring is a ring which is both an ordered ring and a `*`-ring,
and `0 ≤ star r * r` for every `r`.

(In a Banach algebra, the natural ordering is given by the positive cone
which is the closure of the sums of elements `star r * r`.
This ordering makes the Banach algebra an ordered `*`-ring.)
-/
class StarOrderedRing(R : Type u)[OrderedSemiring R] extends StarRing R where 
  star_mul_self_nonneg : ∀ r : R, 0 ≤ star r*r

theorem star_mul_self_nonneg [OrderedSemiring R] [StarOrderedRing R] {r : R} : 0 ≤ star r*r :=
  StarOrderedRing.star_mul_self_nonneg r

/--
A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_scalar R A]`.

If used as `[comm_ring R] [star_ring R] [semiring A] [star_ring A] [algebra R A]`, this represents a
star algebra.
-/
class StarModule(R : Type u)(A : Type v)[HasStar R][HasStar A][HasScalar R A] where 
  star_smul : ∀ r : R a : A, star (r • a) = star r • star a

export StarModule(star_smul)

attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `monoid.to_mul_action`. -/
instance StarMonoid.toStarModule [CommMonoidₓ R] [StarMonoid R] : StarModule R R :=
  ⟨star_mul'⟩

namespace RingHomInvPair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance  [CommSemiringₓ R] [StarRing R] :
  RingHomInvPair ((starRingAut : RingAut R) : R →+* R) ((starRingAut : RingAut R) : R →+* R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

/-! ### Instances -/


namespace Units

variable[Monoidₓ R][StarMonoid R]

instance  : StarMonoid (Units R) :=
  { star :=
      fun u =>
        { val := star u, inv := star («expr↑ » (u⁻¹)),
          val_inv := (star_mul _ _).symm.trans$ (congr_argₓ star u.inv_val).trans$ star_one _,
          inv_val := (star_mul _ _).symm.trans$ (congr_argₓ star u.val_inv).trans$ star_one _ },
    star_involutive := fun u => Units.ext (star_involutive _), star_mul := fun u v => Units.ext (star_mul _ _) }

@[simp]
theorem coe_star (u : Units R) : «expr↑ » (star u) = (star («expr↑ » u) : R) :=
  rfl

@[simp]
theorem coe_star_inv (u : Units R) : «expr↑ » (star u⁻¹) = (star («expr↑ » (u⁻¹)) : R) :=
  rfl

instance  {A : Type _} [HasStar A] [HasScalar R A] [StarModule R A] : StarModule (Units R) A :=
  ⟨fun u a => (star_smul («expr↑ » u) a : _)⟩

end Units

theorem IsUnit.star [Monoidₓ R] [StarMonoid R] {a : R} : IsUnit a → IsUnit (star a)
| ⟨u, hu⟩ => ⟨star u, hu ▸ rfl⟩

@[simp]
theorem is_unit_star [Monoidₓ R] [StarMonoid R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩

theorem Ringₓ.inverse_star [Semiringₓ R] [StarRing R] (a : R) : Ring.inverse (star a) = star (Ring.inverse a) :=
  by 
    byCases' ha : IsUnit a
    ·
      obtain ⟨u, rfl⟩ := ha 
      rw [Ring.inverse_unit, ←Units.coe_star, Ring.inverse_unit, ←Units.coe_star_inv]
    rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ (mt is_unit_star.mp ha), star_zero]

namespace MulOpposite

/-- The opposite type carries the same star operation. -/
instance  [HasStar R] : HasStar («expr ᵐᵒᵖ» R) :=
  { star := fun r => op (star r.unop) }

@[simp]
theorem unop_star [HasStar R] (r : «expr ᵐᵒᵖ» R) : unop (star r) = star (unop r) :=
  rfl

@[simp]
theorem op_star [HasStar R] (r : R) : op (star r) = star (op r) :=
  rfl

instance  [HasInvolutiveStar R] : HasInvolutiveStar («expr ᵐᵒᵖ» R) :=
  { star_involutive := fun r => unop_injective (star_star r.unop) }

instance  [Monoidₓ R] [StarMonoid R] : StarMonoid («expr ᵐᵒᵖ» R) :=
  { star_mul := fun x y => unop_injective (star_mul y.unop x.unop) }

instance  [AddMonoidₓ R] [StarAddMonoid R] : StarAddMonoid («expr ᵐᵒᵖ» R) :=
  { star_add := fun x y => unop_injective (star_add x.unop y.unop) }

instance  [Semiringₓ R] [StarRing R] : StarRing («expr ᵐᵒᵖ» R) :=
  { MulOpposite.starAddMonoid with  }

end MulOpposite

/-- A commutative star monoid is a star module over its opposite via
`monoid.to_opposite_mul_action`. -/
instance StarMonoid.toOppositeStarModule [CommMonoidₓ R] [StarMonoid R] : StarModule («expr ᵐᵒᵖ» R) R :=
  ⟨fun r s => star_mul' s r.unop⟩

