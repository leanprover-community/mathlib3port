import Mathbin.Algebra.Algebra.Basic 
import Mathbin.Algebra.Field.Basic 
import Mathbin.Algebra.Group.TypeTags 
import Mathbin.RingTheory.Ideal.LocalRing 
import Mathbin.Data.Equiv.Basic

/-!
# Transfer algebraic structures across `equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

## Tags

equiv, group, ring, field, module, algebra
-/


universe u v

variable {α : Type u} {β : Type v}

namespace Equivₓ

section Instances

variable (e : α ≃ β)

/-- Transfer `has_one` across an `equiv` -/
@[toAdditive "Transfer `has_zero` across an `equiv`"]
protected def HasOne [HasOne β] : HasOne α :=
  ⟨e.symm 1⟩

@[toAdditive]
theorem one_def [HasOne β] : @HasOne.one _ (Equivₓ.hasOne e) = e.symm 1 :=
  rfl

/-- Transfer `has_mul` across an `equiv` -/
@[toAdditive "Transfer `has_add` across an `equiv`"]
protected def Mul [Mul β] : Mul α :=
  ⟨fun x y => e.symm (e x*e y)⟩

@[toAdditive]
theorem mul_def [Mul β] (x y : α) : @Mul.mul _ (Equivₓ.hasMul e) x y = e.symm (e x*e y) :=
  rfl

/-- Transfer `has_div` across an `equiv` -/
@[toAdditive "Transfer `has_sub` across an `equiv`"]
protected def Div [Div β] : Div α :=
  ⟨fun x y => e.symm (e x / e y)⟩

@[toAdditive]
theorem div_def [Div β] (x y : α) : @Div.div _ (Equivₓ.hasDiv e) x y = e.symm (e x / e y) :=
  rfl

/-- Transfer `has_inv` across an `equiv` -/
@[toAdditive "Transfer `has_neg` across an `equiv`"]
protected def HasInv [HasInv β] : HasInv α :=
  ⟨fun x => e.symm (e x⁻¹)⟩

@[toAdditive]
theorem inv_def [HasInv β] (x : α) : @HasInv.inv _ (Equivₓ.hasInv e) x = e.symm (e x⁻¹) :=
  rfl

/-- Transfer `has_scalar` across an `equiv` -/
protected def HasScalar {R : Type _} [HasScalar R β] : HasScalar R α :=
  ⟨fun r x => e.symm (r • e x)⟩

theorem smul_def {R : Type _} [HasScalar R β] (r : R) (x : α) :
  @HasScalar.smul _ _ (Equivₓ.hasScalar e) r x = e.symm (r • e x) :=
  rfl

/--
An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β`
where the multiplicative structure on `α` is
the one obtained by transporting a multiplicative structure on `β` back along `e`.
-/
@[toAdditive
      "An equivalence `e : α ≃ β` gives a additive equivalence `α ≃+ β`\nwhere the additive structure on `α` is\nthe one obtained by transporting an additive structure on `β` back along `e`."]
def MulEquiv (e : α ≃ β) [Mul β] :
  by 
    let this' := Equivₓ.hasMul e 
    exact α ≃* β :=
  by 
    intros 
    exact
      { e with
        map_mul' :=
          fun x y =>
            by 
              apply e.symm.injective 
              simp 
              rfl }

@[simp, toAdditive]
theorem mul_equiv_apply (e : α ≃ β) [Mul β] (a : α) : (MulEquiv e) a = e a :=
  rfl

@[toAdditive]
theorem mul_equiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
  by 
    let this' := Equivₓ.hasMul e 
    exact (MulEquiv e).symm b = e.symm b :=
  by 
    intros 
    rfl

/--
An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def RingEquiv (e : α ≃ β) [Add β] [Mul β] :
  by 
    let this' := Equivₓ.hasAdd e 
    let this' := Equivₓ.hasMul e 
    exact α ≃+* β :=
  by 
    intros 
    exact
      { e with
        map_add' :=
          fun x y =>
            by 
              apply e.symm.injective 
              simp 
              rfl,
        map_mul' :=
          fun x y =>
            by 
              apply e.symm.injective 
              simp 
              rfl }

@[simp]
theorem ring_equiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : (RingEquiv e) a = e a :=
  rfl

theorem ring_equiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) :
  by 
    let this' := Equivₓ.hasAdd e 
    let this' := Equivₓ.hasMul e 
    exact (RingEquiv e).symm b = e.symm b :=
  by 
    intros 
    rfl

/-- Transfer `semigroup` across an `equiv` -/
@[toAdditive "Transfer `add_semigroup` across an `equiv`"]
protected def Semigroupₓ [Semigroupₓ β] : Semigroupₓ α :=
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.semigroup _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `semigroup_with_zero` across an `equiv` -/
protected def SemigroupWithZero [SemigroupWithZero β] : SemigroupWithZero α :=
  let mul := e.has_mul 
  let zero := e.has_zero 
  by 
    skip <;> apply e.injective.semigroup_with_zero _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_semigroup` across an `equiv` -/
@[toAdditive "Transfer `add_comm_semigroup` across an `equiv`"]
protected def CommSemigroupₓ [CommSemigroupₓ β] : CommSemigroupₓ α :=
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.comm_semigroup _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `mul_zero_class` across an `equiv` -/
protected def MulZeroClass [MulZeroClass β] : MulZeroClass α :=
  let zero := e.has_zero 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.mul_zero_class _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `mul_one_class` across an `equiv` -/
@[toAdditive "Transfer `add_zero_class` across an `equiv`"]
protected def MulOneClass [MulOneClass β] : MulOneClass α :=
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.mul_one_class _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `mul_zero_one_class` across an `equiv` -/
protected def MulZeroOneClass [MulZeroOneClass β] : MulZeroOneClass α :=
  let zero := e.has_zero 
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.mul_zero_one_class _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `monoid` across an `equiv` -/
@[toAdditive "Transfer `add_monoid` across an `equiv`"]
protected def Monoidₓ [Monoidₓ β] : Monoidₓ α :=
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.monoid _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_monoid` across an `equiv` -/
@[toAdditive "Transfer `add_comm_monoid` across an `equiv`"]
protected def CommMonoidₓ [CommMonoidₓ β] : CommMonoidₓ α :=
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.comm_monoid _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `group` across an `equiv` -/
@[toAdditive "Transfer `add_group` across an `equiv`"]
protected def Groupₓ [Groupₓ β] : Groupₓ α :=
  let one := e.has_one 
  let mul := e.has_mul 
  let inv := e.has_inv 
  let div := e.has_div 
  by 
    skip <;> apply e.injective.group _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_group` across an `equiv` -/
@[toAdditive "Transfer `add_comm_group` across an `equiv`"]
protected def CommGroupₓ [CommGroupₓ β] : CommGroupₓ α :=
  let one := e.has_one 
  let mul := e.has_mul 
  let inv := e.has_inv 
  let div := e.has_div 
  by 
    skip <;> apply e.injective.comm_group _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_non_assoc_semiring` across an `equiv` -/
protected def NonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.non_unital_non_assoc_semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `non_unital_semiring` across an `equiv` -/
protected def NonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.non_unital_semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `non_assoc_semiring` across an `equiv` -/
protected def NonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.non_assoc_semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `semiring` across an `equiv` -/
protected def Semiringₓ [Semiringₓ β] : Semiringₓ α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_semiring` across an `equiv` -/
protected def CommSemiringₓ [CommSemiringₓ β] : CommSemiringₓ α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  by 
    skip <;> apply e.injective.comm_semiring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `ring` across an `equiv` -/
protected def Ringₓ [Ringₓ β] : Ringₓ α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  let neg := e.has_neg 
  let sub := e.has_sub 
  by 
    skip <;> apply e.injective.ring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `comm_ring` across an `equiv` -/
protected def CommRingₓ [CommRingₓ β] : CommRingₓ α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  let neg := e.has_neg 
  let sub := e.has_sub 
  by 
    skip <;> apply e.injective.comm_ring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `nonzero` across an `equiv` -/
protected theorem Nontrivial [Nontrivial β] : Nontrivial α :=
  e.surjective.nontrivial

/-- Transfer `is_domain` across an `equiv` -/
protected theorem IsDomain [Ringₓ α] [Ringₓ β] [IsDomain β] (e : α ≃+* β) : IsDomain α :=
  Function.Injective.is_domain e.to_ring_hom e.injective

/-- Transfer `division_ring` across an `equiv` -/
protected def DivisionRing [DivisionRing β] : DivisionRing α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  let neg := e.has_neg 
  let sub := e.has_sub 
  let inv := e.has_inv 
  let div := e.has_div 
  by 
    skip <;> apply e.injective.division_ring _ <;> intros  <;> exact e.apply_symm_apply _

/-- Transfer `field` across an `equiv` -/
protected def Field [Field β] : Field α :=
  let zero := e.has_zero 
  let add := e.has_add 
  let one := e.has_one 
  let mul := e.has_mul 
  let neg := e.has_neg 
  let sub := e.has_sub 
  let inv := e.has_inv 
  let div := e.has_div 
  by 
    skip <;> apply e.injective.field _ <;> intros  <;> exact e.apply_symm_apply _

section R

variable (R : Type _)

include R

section 

variable [Monoidₓ R]

/-- Transfer `mul_action` across an `equiv` -/
protected def MulAction (e : α ≃ β) [MulAction R β] : MulAction R α :=
  { Equivₓ.hasScalar e with
    one_smul :=
      by 
        simp [smul_def],
    mul_smul :=
      by 
        simp [smul_def, mul_smul] }

/-- Transfer `distrib_mul_action` across an `equiv` -/
protected def DistribMulAction (e : α ≃ β) [AddCommMonoidₓ β] :
  by 
    let this' := Equivₓ.addCommMonoid e 
    exact ∀ [DistribMulAction R β], DistribMulAction R α :=
  by 
    intros 
    let this' := Equivₓ.addCommMonoid e 
    exact
      ({ Equivₓ.mulAction R e with
        smul_zero :=
          by 
            simp [zero_def, smul_def],
        smul_add :=
          by 
            simp [add_def, smul_def, smul_add] } :
      DistribMulAction R α)

end 

section 

variable [Semiringₓ R]

/-- Transfer `module` across an `equiv` -/
protected def Module (e : α ≃ β) [AddCommMonoidₓ β] :
  by 
    let this' := Equivₓ.addCommMonoid e 
    exact ∀ [Module R β], Module R α :=
  by 
    intros 
    exact
      ({ Equivₓ.distribMulAction R e with
        zero_smul :=
          by 
            simp [zero_def, smul_def],
        add_smul :=
          by 
            simp [add_def, smul_def, add_smul] } :
      Module R α)

/--
An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def LinearEquiv (e : α ≃ β) [AddCommMonoidₓ β] [Module R β] :
  by 
    let this' := Equivₓ.addCommMonoid e 
    let this' := Equivₓ.module R e 
    exact α ≃ₗ[R] β :=
  by 
    intros 
    exact
      { Equivₓ.addEquiv e with
        map_smul' :=
          fun r x =>
            by 
              apply e.symm.injective 
              simp 
              rfl }

end 

section 

variable [CommSemiringₓ R]

/-- Transfer `algebra` across an `equiv` -/
protected def Algebra (e : α ≃ β) [Semiringₓ β] :
  by 
    let this' := Equivₓ.semiring e 
    exact ∀ [Algebra R β], Algebra R α :=
  by 
    intros 
    fapply RingHom.toAlgebra'
    ·
      exact ((RingEquiv e).symm : β →+* α).comp (algebraMap R β)
    ·
      intro r x 
      simp only [Function.comp_app, RingHom.coe_comp]
      have p := ring_equiv_symm_apply e 
      dsimp  at p 
      erw [p]
      clear p 
      apply (RingEquiv e).Injective 
      simp only [(RingEquiv e).map_mul]
      simp [Algebra.commutes]

/--
An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def AlgEquiv (e : α ≃ β) [Semiringₓ β] [Algebra R β] :
  by 
    let this' := Equivₓ.semiring e 
    let this' := Equivₓ.algebra R e 
    exact α ≃ₐ[R] β :=
  by 
    intros 
    exact
      { Equivₓ.ringEquiv e with
        commutes' :=
          fun r =>
            by 
              apply e.symm.injective 
              simp 
              rfl }

end 

end R

end Instances

end Equivₓ

namespace RingEquiv

protected theorem LocalRing {A B : Type _} [CommRingₓ A] [LocalRing A] [CommRingₓ B] (e : A ≃+* B) : LocalRing B :=
  by 
    have  := e.symm.to_equiv.nontrivial 
    refine' @local_of_surjective A B _ _ _ _ e e.to_equiv.surjective

end RingEquiv

