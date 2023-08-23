/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Ring.Aut
import Mathbin.Algebra.Ring.CompTypeclasses
import Mathbin.Data.Rat.Cast
import Mathbin.GroupTheory.GroupAction.Opposite
import Mathbin.Data.SetLike.Basic

#align_import algebra.star.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Star monoids, rings, and modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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


assert_not_exists Finset

assert_not_exists Subgroup

universe u v

open MulOpposite

#print Star /-
/-- Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class Star (R : Type u) where
  unit : R → R
#align has_star Star
-/

variable {R : Type u}

export Star (unit)

/-- A star operation (e.g. complex conjugate).
-/
add_decl_doc star

#print StarMemClass /-
/-- `star_mem_class S G` states `S` is a type of subsets `s ⊆ G` closed under star. -/
class StarMemClass (S R : Type _) [Star R] [SetLike S R] where
  star_mem : ∀ {s : S} {r : R}, r ∈ s → star r ∈ s
#align star_mem_class StarMemClass
-/

export StarMemClass (star_mem)

namespace StarMemClass

variable {S : Type u} [Star R] [SetLike S R] [hS : StarMemClass S R] (s : S)

instance : Star s where unit r := ⟨star (r : R), star_mem r.Prop⟩

end StarMemClass

#print InvolutiveStar /-
/-- Typeclass for a star operation with is involutive.
-/
class InvolutiveStar (R : Type u) extends Star R where
  star_involutive : Function.Involutive star
#align has_involutive_star InvolutiveStar
-/

export InvolutiveStar (star_involutive)

#print star_star /-
@[simp]
theorem star_star [InvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _
#align star_star star_star
-/

#print star_injective /-
theorem star_injective [InvolutiveStar R] : Function.Injective (star : R → R) :=
  star_involutive.Injective
#align star_injective star_injective
-/

#print star_inj /-
@[simp]
theorem star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = y :=
  star_injective.eq_iff
#align star_inj star_inj
-/

#print Equiv.star /-
/-- `star` as an equivalence when it is involutive. -/
protected def Equiv.star [InvolutiveStar R] : Equiv.Perm R :=
  star_involutive.toPerm _
#align equiv.star Equiv.star
-/

#print eq_star_of_eq_star /-
theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by simp [h]
#align eq_star_of_eq_star eq_star_of_eq_star
-/

#print eq_star_iff_eq_star /-
theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩
#align eq_star_iff_eq_star eq_star_iff_eq_star
-/

#print star_eq_iff_star_eq /-
theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
  eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm
#align star_eq_iff_star_eq star_eq_iff_star_eq
-/

#print TrivialStar /-
/-- Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class TrivialStar (R : Type u) [Star R] : Prop where
  star_trivial : ∀ r : R, star r = r
#align has_trivial_star TrivialStar
-/

export TrivialStar (star_trivial)

attribute [simp] star_trivial

#print StarSemigroup /-
/-- A `*`-semigroup is a semigroup `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class StarSemigroup (R : Type u) [Semigroup R] extends InvolutiveStar R where
  star_hMul : ∀ r s : R, star (r * s) = star s * star r
#align star_semigroup StarSemigroup
-/

export StarSemigroup (star_hMul)

attribute [simp] star_mul

section StarSemigroup

variable [Semigroup R] [StarSemigroup R]

#print star_star_mul /-
theorem star_star_mul (x y : R) : star (star x * y) = star y * x := by rw [star_mul, star_star]
#align star_star_mul star_star_mul
-/

#print star_mul_star /-
theorem star_mul_star (x y : R) : star (x * star y) = y * star x := by rw [star_mul, star_star]
#align star_mul_star star_mul_star
-/

#print semiconjBy_star_star_star /-
@[simp]
theorem semiconjBy_star_star_star {x y z : R} :
    SemiconjBy (star x) (star z) (star y) ↔ SemiconjBy x y z := by
  simp_rw [SemiconjBy, ← star_mul, star_inj, eq_comm]
#align semiconj_by_star_star_star semiconjBy_star_star_star
-/

alias ⟨_, SemiconjBy.star_star_star⟩ := semiconjBy_star_star_star
#align semiconj_by.star_star_star SemiconjBy.star_star_star

#print commute_star_star /-
@[simp]
theorem commute_star_star {x y : R} : Commute (star x) (star y) ↔ Commute x y :=
  semiconjBy_star_star_star
#align commute_star_star commute_star_star
-/

alias ⟨_, Commute.star_star⟩ := commute_star_star
#align commute.star_star Commute.star_star

#print commute_star_comm /-
theorem commute_star_comm {x y : R} : Commute (star x) y ↔ Commute x (star y) := by
  rw [← commute_star_star, star_star]
#align commute_star_comm commute_star_comm
-/

end StarSemigroup

#print star_mul' /-
/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
theorem star_mul' [CommSemigroup R] [StarSemigroup R] (x y : R) : star (x * y) = star x * star y :=
  (star_hMul x y).trans (mul_comm _ _)
#align star_mul' star_mul'
-/

#print starMulEquiv /-
/-- `star` as an `mul_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starMulEquiv [Semigroup R] [StarSemigroup R] : R ≃* Rᵐᵒᵖ :=
  {
    (InvolutiveStar.star_involutive.toPerm star).trans
      opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => (star_hMul x y).symm ▸ MulOpposite.op_mul _ _ }
#align star_mul_equiv starMulEquiv
-/

#print starMulAut /-
/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def starMulAut [CommSemigroup R] [StarSemigroup R] : MulAut R :=
  {
    InvolutiveStar.star_involutive.toPerm
      star with
    toFun := star
    map_mul' := star_mul' }
#align star_mul_aut starMulAut
-/

variable (R)

#print star_one /-
@[simp]
theorem star_one [Monoid R] [StarSemigroup R] : star (1 : R) = 1 :=
  op_injective <| (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans (op_one _).symm
#align star_one star_one
-/

variable {R}

#print star_pow /-
@[simp]
theorem star_pow [Monoid R] [StarSemigroup R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm
#align star_pow star_pow
-/

#print star_inv /-
@[simp]
theorem star_inv [Group R] [StarSemigroup R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm
#align star_inv star_inv
-/

#print star_zpow /-
@[simp]
theorem star_zpow [Group R] [StarSemigroup R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm
#align star_zpow star_zpow
-/

#print star_div /-
/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div [CommGroup R] [StarSemigroup R] (x y : R) : star (x / y) = star x / star y :=
  map_div (starMulAut : R ≃* R) _ _
#align star_div star_div
-/

#print starSemigroupOfComm /-
/-- Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def starSemigroupOfComm {R : Type _} [CommMonoid R] : StarSemigroup R
    where
  unit := id
  star_involutive x := rfl
  star_hMul := mul_comm
#align star_semigroup_of_comm starSemigroupOfComm
-/

section

attribute [local instance] starSemigroupOfComm

#print star_id_of_comm /-
/-- Note that since `star_semigroup_of_comm` is reducible, `simp` can already prove this. -/
theorem star_id_of_comm {R : Type _} [CommSemiring R] {x : R} : star x = x :=
  rfl
#align star_id_of_comm star_id_of_comm
-/

end

#print StarAddMonoid /-
/-- A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition.
-/
class StarAddMonoid (R : Type u) [AddMonoid R] extends InvolutiveStar R where
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_add_monoid StarAddMonoid
-/

export StarAddMonoid (star_add)

attribute [simp] star_add

#print starAddEquiv /-
/-- `star` as an `add_equiv` -/
@[simps apply]
def starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R :=
  {
    InvolutiveStar.star_involutive.toPerm
      star with
    toFun := star
    map_add' := star_add }
#align star_add_equiv starAddEquiv
-/

variable (R)

#print star_zero /-
@[simp]
theorem star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero
#align star_zero star_zero
-/

variable {R}

#print star_eq_zero /-
@[simp]
theorem star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 :=
  starAddEquiv.map_eq_zero_iff
#align star_eq_zero star_eq_zero
-/

#print star_ne_zero /-
theorem star_ne_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x ≠ 0 ↔ x ≠ 0 :=
  star_eq_zero.Not
#align star_ne_zero star_ne_zero
-/

#print star_neg /-
@[simp]
theorem star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _
#align star_neg star_neg
-/

#print star_sub /-
@[simp]
theorem star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _
#align star_sub star_sub
-/

#print star_nsmul /-
@[simp]
theorem star_nsmul [AddMonoid R] [StarAddMonoid R] (x : R) (n : ℕ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _
#align star_nsmul star_nsmul
-/

#print star_zsmul /-
@[simp]
theorem star_zsmul [AddGroup R] [StarAddMonoid R] (x : R) (n : ℤ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _
#align star_zsmul star_zsmul
-/

#print StarRing /-
/-- A `*`-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a `*`-semigroup
(i.e. `star (r * s) = star s * star r`).
-/
class StarRing (R : Type u) [NonUnitalSemiring R] extends StarSemigroup R where
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_ring StarRing
-/

#print StarRing.toStarAddMonoid /-
instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalSemiring R] [StarRing R] :
    StarAddMonoid R where star_add := StarRing.star_add
#align star_ring.to_star_add_monoid StarRing.toStarAddMonoid
-/

#print starRingEquiv /-
/-- `star` as an `ring_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starRingEquiv [NonUnitalSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }
#align star_ring_equiv starRingEquiv
-/

#print star_natCast /-
@[simp, norm_cast]
theorem star_natCast [Semiring R] [StarRing R] (n : ℕ) : star (n : R) = n :=
  (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)
#align star_nat_cast star_natCast
-/

#print star_intCast /-
@[simp, norm_cast]
theorem star_intCast [Ring R] [StarRing R] (z : ℤ) : star (z : R) = z :=
  (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)
#align star_int_cast star_intCast
-/

#print star_ratCast /-
@[simp, norm_cast]
theorem star_ratCast [DivisionRing R] [StarRing R] (r : ℚ) : star (r : R) = r :=
  (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)
#align star_rat_cast star_ratCast
-/

#print starRingAut /-
/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
def starRingAut [CommSemiring R] [StarRing R] : RingAut R :=
  { starAddEquiv, starMulAut with toFun := star }
#align star_ring_aut starRingAut
-/

variable (R)

#print starRingEnd /-
/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `complex_conjugate`.

Note that this is the preferred form (over `star_ring_aut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[star_ring_end R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑star_ring_aut : R →* R)`. -/
def starRingEnd [CommSemiring R] [StarRing R] : R →+* R :=
  @starRingAut R _ _
#align star_ring_end starRingEnd
-/

variable {R}

scoped[ComplexConjugate] notation "conj" => starRingEnd hole!

#print starRingEnd_apply /-
/-- This is not a simp lemma, since we usually want simp to keep `star_ring_end` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
theorem starRingEnd_apply [CommSemiring R] [StarRing R] {x : R} : starRingEnd R x = star x :=
  rfl
#align star_ring_end_apply starRingEnd_apply
-/

#print starRingEnd_self_apply /-
@[simp]
theorem starRingEnd_self_apply [CommSemiring R] [StarRing R] (x : R) :
    starRingEnd R (starRingEnd R x) = x :=
  star_star x
#align star_ring_end_self_apply starRingEnd_self_apply
-/

#print RingHom.involutiveStar /-
instance RingHom.involutiveStar {S : Type _} [NonAssocSemiring S] [CommSemiring R] [StarRing R] :
    InvolutiveStar (S →+* R)
    where
  toHasStar := { unit := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by intro; ext;
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]
#align ring_hom.has_involutive_star RingHom.involutiveStar
-/

#print RingHom.star_def /-
theorem RingHom.star_def {S : Type _} [NonAssocSemiring S] [CommSemiring R] [StarRing R]
    (f : S →+* R) : Star.star f = RingHom.comp (starRingEnd R) f :=
  rfl
#align ring_hom.star_def RingHom.star_def
-/

#print RingHom.star_apply /-
theorem RingHom.star_apply {S : Type _} [NonAssocSemiring S] [CommSemiring R] [StarRing R]
    (f : S →+* R) (s : S) : star f s = star (f s) :=
  rfl
#align ring_hom.star_apply RingHom.star_apply
-/

-- A more convenient name for complex conjugation
alias Complex.conj_conj := starRingEnd_self_apply
#align complex.conj_conj Complex.conj_conj

alias IsROrC.conj_conj := starRingEnd_self_apply
#align is_R_or_C.conj_conj IsROrC.conj_conj

#print star_inv' /-
@[simp]
theorem star_inv' [DivisionSemiring R] [StarRing R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| (map_inv₀ (starRingEquiv : R ≃+* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm
#align star_inv' star_inv'
-/

#print star_zpow₀ /-
@[simp]
theorem star_zpow₀ [DivisionSemiring R] [StarRing R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <| (map_zpow₀ (starRingEquiv : R ≃+* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm
#align star_zpow₀ star_zpow₀
-/

#print star_div' /-
/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div' [Semifield R] [StarRing R] (x y : R) : star (x / y) = star x / star y :=
  map_div₀ (starRingEnd R) _ _
#align star_div' star_div'
-/

#print star_bit0 /-
@[simp]
theorem star_bit0 [AddMonoid R] [StarAddMonoid R] (r : R) : star (bit0 r) = bit0 (star r) := by
  simp [bit0]
#align star_bit0 star_bit0
-/

#print star_bit1 /-
@[simp]
theorem star_bit1 [Semiring R] [StarRing R] (r : R) : star (bit1 r) = bit1 (star r) := by
  simp [bit1]
#align star_bit1 star_bit1
-/

#print starRingOfComm /-
/-- Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def starRingOfComm {R : Type _} [CommSemiring R] : StarRing R :=
  { starSemigroupOfComm with
    unit := id
    star_add := fun x y => rfl }
#align star_ring_of_comm starRingOfComm
-/

#print StarModule /-
/-- A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_smul R A]`.

If used as `[comm_ring R] [star_ring R] [semiring A] [star_ring A] [algebra R A]`, this represents a
star algebra.
-/
class StarModule (R : Type u) (A : Type v) [Star R] [Star A] [SMul R A] : Prop where
  star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a
#align star_module StarModule
-/

export StarModule (star_smul)

attribute [simp] star_smul

#print StarSemigroup.to_starModule /-
/-- A commutative star monoid is a star module over itself via `monoid.to_mul_action`. -/
instance StarSemigroup.to_starModule [CommMonoid R] [StarSemigroup R] : StarModule R R :=
  ⟨star_mul'⟩
#align star_semigroup.to_star_module StarSemigroup.to_starModule
-/

namespace RingHomInvPair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance [CommSemiring R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

section

#print StarHomClass /-
/-- `star_hom_class F R S` states that `F` is a type of `star`-preserving maps from `R` to `S`. -/
class StarHomClass (F : Type _) (R S : outParam (Type _)) [Star R] [Star S] extends
    FunLike F R fun _ => S where
  map_star : ∀ (f : F) (r : R), f (star r) = star (f r)
#align star_hom_class StarHomClass
-/

export StarHomClass (map_star)

end

/-! ### Instances -/


namespace Units

variable [Monoid R] [StarSemigroup R]

instance : StarSemigroup Rˣ
    where
  unit u :=
    { val := star u
      inv := star ↑u⁻¹
      val_inv := (star_hMul _ _).symm.trans <| (congr_arg star u.inv_val).trans <| star_one _
      inv_val := (star_hMul _ _).symm.trans <| (congr_arg star u.val_inv).trans <| star_one _ }
  star_involutive u := Units.ext (star_involutive _)
  star_hMul u v := Units.ext (star_hMul _ _)

#print Units.coe_star /-
@[simp]
theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) :=
  rfl
#align units.coe_star Units.coe_star
-/

#print Units.coe_star_inv /-
@[simp]
theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) :=
  rfl
#align units.coe_star_inv Units.coe_star_inv
-/

instance {A : Type _} [Star A] [SMul R A] [StarModule R A] : StarModule Rˣ A :=
  ⟨fun u a => (star_smul (↑u) a : _)⟩

end Units

#print IsUnit.star /-
theorem IsUnit.star [Monoid R] [StarSemigroup R] {a : R} : IsUnit a → IsUnit (star a)
  | ⟨u, hu⟩ => ⟨star u, hu ▸ rfl⟩
#align is_unit.star IsUnit.star
-/

#print isUnit_star /-
@[simp]
theorem isUnit_star [Monoid R] [StarSemigroup R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.unit, IsUnit.star⟩
#align is_unit_star isUnit_star
-/

#print Ring.inverse_star /-
theorem Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
    Ring.inverse (star a) = star (Ring.inverse a) :=
  by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit, ← Units.coe_star, Ring.inverse_unit, ← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ (mt is_unit_star.mp ha), star_zero]
#align ring.inverse_star Ring.inverse_star
-/

#print Invertible.star /-
instance Invertible.star {R : Type _} [Monoid R] [StarSemigroup R] (r : R) [Invertible r] :
    Invertible (star r) where
  invOf := star (⅟ r)
  invOf_hMul_self := by rw [← star_mul, mul_invOf_self, star_one]
  hMul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]
#align invertible.star Invertible.star
-/

#print star_invOf /-
theorem star_invOf {R : Type _} [Monoid R] [StarSemigroup R] (r : R) [Invertible r]
    [Invertible (star r)] : star (⅟ r) = ⅟ (star r) := by letI := Invertible.star r;
  convert (rfl : star (⅟ r) = _)
#align star_inv_of star_invOf
-/

namespace MulOpposite

/-- The opposite type carries the same star operation. -/
instance [Star R] : Star Rᵐᵒᵖ where unit r := op (star r.unop)

#print MulOpposite.unop_star /-
@[simp]
theorem unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) :=
  rfl
#align mul_opposite.unop_star MulOpposite.unop_star
-/

#print MulOpposite.op_star /-
@[simp]
theorem op_star [Star R] (r : R) : op (star r) = star (op r) :=
  rfl
#align mul_opposite.op_star MulOpposite.op_star
-/

instance [InvolutiveStar R] : InvolutiveStar Rᵐᵒᵖ
    where star_involutive r := unop_injective (star_star r.unop)

instance [Monoid R] [StarSemigroup R] : StarSemigroup Rᵐᵒᵖ
    where star_hMul x y := unop_injective (star_hMul y.unop x.unop)

instance [AddMonoid R] [StarAddMonoid R] : StarAddMonoid Rᵐᵒᵖ
    where star_add x y := unop_injective (star_add x.unop y.unop)

instance [Semiring R] [StarRing R] : StarRing Rᵐᵒᵖ :=
  { MulOpposite.starAddMonoid with }

end MulOpposite

#print StarSemigroup.toOpposite_starModule /-
/-- A commutative star monoid is a star module over its opposite via
`monoid.to_opposite_mul_action`. -/
instance StarSemigroup.toOpposite_starModule [CommMonoid R] [StarSemigroup R] : StarModule Rᵐᵒᵖ R :=
  ⟨fun r s => star_mul' s r.unop⟩
#align star_semigroup.to_opposite_star_module StarSemigroup.toOpposite_starModule
-/

