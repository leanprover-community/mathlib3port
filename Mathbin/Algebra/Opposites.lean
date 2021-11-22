import Mathbin.Data.Opposite 
import Mathbin.Algebra.Field 
import Mathbin.Algebra.Group.Commute 
import Mathbin.GroupTheory.GroupAction.Defs 
import Mathbin.Data.Equiv.MulAdd

/-!
# Algebraic operations on `αᵒᵖ`

This file records several basic facts about the opposite of an algebraic structure, e.g. the
opposite of a ring is a ring (with multiplication `x * y = yx`). Use is made of the identity
functions `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`.
-/


namespace Opposite

universe u

variable(α : Type u)

instance  [HasZero α] : HasZero (Opposite α) :=
  { zero := op 0 }

instance  [HasOne α] : HasOne (Opposite α) :=
  { one := op 1 }

instance  [Add α] : Add (Opposite α) :=
  { add := fun x y => op (unop x+unop y) }

instance  [Sub α] : Sub (Opposite α) :=
  { sub := fun x y => op (unop x - unop y) }

instance  [Neg α] : Neg (Opposite α) :=
  { neg := fun x => op$ -unop x }

instance  [Mul α] : Mul (Opposite α) :=
  { mul := fun x y => op (unop y*unop x) }

instance  [HasInv α] : HasInv (Opposite α) :=
  { inv := fun x => op$ unop x⁻¹ }

instance  (R : Type _) [HasScalar R α] : HasScalar R (Opposite α) :=
  { smul := fun c x => op (c • unop x) }

section 

variable(α)

@[simp]
theorem op_zero [HasZero α] : op (0 : α) = 0 :=
  rfl

@[simp]
theorem unop_zero [HasZero α] : unop (0 : «expr ᵒᵖ» α) = 0 :=
  rfl

@[simp]
theorem op_one [HasOne α] : op (1 : α) = 1 :=
  rfl

@[simp]
theorem unop_one [HasOne α] : unop (1 : «expr ᵒᵖ» α) = 1 :=
  rfl

variable{α}

@[simp]
theorem op_add [Add α] (x y : α) : op (x+y) = op x+op y :=
  rfl

@[simp]
theorem unop_add [Add α] (x y : «expr ᵒᵖ» α) : unop (x+y) = unop x+unop y :=
  rfl

@[simp]
theorem op_neg [Neg α] (x : α) : op (-x) = -op x :=
  rfl

@[simp]
theorem unop_neg [Neg α] (x : «expr ᵒᵖ» α) : unop (-x) = -unop x :=
  rfl

@[simp]
theorem op_mul [Mul α] (x y : α) : op (x*y) = op y*op x :=
  rfl

@[simp]
theorem unop_mul [Mul α] (x y : «expr ᵒᵖ» α) : unop (x*y) = unop y*unop x :=
  rfl

@[simp]
theorem op_inv [HasInv α] (x : α) : op (x⁻¹) = op x⁻¹ :=
  rfl

@[simp]
theorem unop_inv [HasInv α] (x : «expr ᵒᵖ» α) : unop (x⁻¹) = unop x⁻¹ :=
  rfl

@[simp]
theorem op_sub [Sub α] (x y : α) : op (x - y) = op x - op y :=
  rfl

@[simp]
theorem unop_sub [Sub α] (x y : «expr ᵒᵖ» α) : unop (x - y) = unop x - unop y :=
  rfl

@[simp]
theorem op_smul {R : Type _} [HasScalar R α] (c : R) (a : α) : op (c • a) = c • op a :=
  rfl

@[simp]
theorem unop_smul {R : Type _} [HasScalar R α] (c : R) (a : «expr ᵒᵖ» α) : unop (c • a) = c • unop a :=
  rfl

end 

instance  [AddSemigroupₓ α] : AddSemigroupₓ («expr ᵒᵖ» α) :=
  unop_injective.AddSemigroup _ fun x y => rfl

instance  [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup (Opposite α) :=
  unop_injective.AddLeftCancelSemigroup _ fun x y => rfl

instance  [AddRightCancelSemigroup α] : AddRightCancelSemigroup (Opposite α) :=
  unop_injective.AddRightCancelSemigroup _ fun x y => rfl

instance  [AddCommSemigroupₓ α] : AddCommSemigroupₓ (Opposite α) :=
  { Opposite.addSemigroup α with add_comm := fun x y => unop_injective$ add_commₓ (unop x) (unop y) }

instance  [Nontrivial α] : Nontrivial (Opposite α) :=
  op_injective.Nontrivial

@[simp]
theorem unop_eq_zero_iff {α} [HasZero α] (a : «expr ᵒᵖ» α) : a.unop = (0 : α) ↔ a = (0 : «expr ᵒᵖ» α) :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_zero_iff {α} [HasZero α] (a : α) : op a = (0 : «expr ᵒᵖ» α) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl

theorem unop_ne_zero_iff {α} [HasZero α] (a : «expr ᵒᵖ» α) : a.unop ≠ (0 : α) ↔ a ≠ (0 : «expr ᵒᵖ» α) :=
  not_congr$ unop_eq_zero_iff a

theorem op_ne_zero_iff {α} [HasZero α] (a : α) : op a ≠ (0 : «expr ᵒᵖ» α) ↔ a ≠ (0 : α) :=
  not_congr$ op_eq_zero_iff a

instance  [AddZeroClass α] : AddZeroClass (Opposite α) :=
  unop_injective.AddZeroClass _ rfl fun x y => rfl

instance  [AddMonoidₓ α] : AddMonoidₓ (Opposite α) :=
  unop_injective.addMonoidSmul _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance  [AddCommMonoidₓ α] : AddCommMonoidₓ (Opposite α) :=
  { Opposite.addMonoid α, Opposite.addCommSemigroup α with  }

instance  [SubNegMonoidₓ α] : SubNegMonoidₓ (Opposite α) :=
  unop_injective.subNegMonoidSmul _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance  [AddGroupₓ α] : AddGroupₓ (Opposite α) :=
  unop_injective.addGroupSmul _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance  [AddCommGroupₓ α] : AddCommGroupₓ (Opposite α) :=
  { Opposite.addGroup α, Opposite.addCommMonoid α with  }

instance  [Semigroupₓ α] : Semigroupₓ (Opposite α) :=
  { Opposite.hasMul α with mul_assoc := fun x y z => unop_injective$ Eq.symm$ mul_assocₓ (unop z) (unop y) (unop x) }

instance  [RightCancelSemigroup α] : LeftCancelSemigroup (Opposite α) :=
  { Opposite.semigroup α with mul_left_cancel := fun x y z H => unop_injective$ mul_right_cancelₓ$ op_injective H }

instance  [LeftCancelSemigroup α] : RightCancelSemigroup (Opposite α) :=
  { Opposite.semigroup α with mul_right_cancel := fun x y z H => unop_injective$ mul_left_cancelₓ$ op_injective H }

instance  [CommSemigroupₓ α] : CommSemigroupₓ (Opposite α) :=
  { Opposite.semigroup α with mul_comm := fun x y => unop_injective$ mul_commₓ (unop y) (unop x) }

section 

attribute [local semireducible] Opposite

@[simp]
theorem unop_eq_one_iff {α} [HasOne α] (a : «expr ᵒᵖ» α) : a.unop = 1 ↔ a = 1 :=
  Iff.refl _

@[simp]
theorem op_eq_one_iff {α} [HasOne α] (a : α) : op a = 1 ↔ a = 1 :=
  Iff.refl _

end 

instance  [MulOneClass α] : MulOneClass (Opposite α) :=
  { Opposite.hasMul α, Opposite.hasOne α with one_mul := fun x => unop_injective$ mul_oneₓ$ unop x,
    mul_one := fun x => unop_injective$ one_mulₓ$ unop x }

instance  [Monoidₓ α] : Monoidₓ (Opposite α) :=
  { Opposite.semigroup α, Opposite.mulOneClass α with npow := fun n x => op$ x.unop ^ n,
    npow_zero' := fun x => unop_injective$ Monoidₓ.npow_zero' x.unop,
    npow_succ' := fun n x => unop_injective$ pow_succ'ₓ x.unop n }

instance  [RightCancelMonoid α] : LeftCancelMonoid (Opposite α) :=
  { Opposite.leftCancelSemigroup α, Opposite.monoid α with  }

instance  [LeftCancelMonoid α] : RightCancelMonoid (Opposite α) :=
  { Opposite.rightCancelSemigroup α, Opposite.monoid α with  }

instance  [CancelMonoid α] : CancelMonoid (Opposite α) :=
  { Opposite.rightCancelMonoid α, Opposite.leftCancelMonoid α with  }

instance  [CommMonoidₓ α] : CommMonoidₓ (Opposite α) :=
  { Opposite.monoid α, Opposite.commSemigroup α with  }

instance  [CancelCommMonoid α] : CancelCommMonoid (Opposite α) :=
  { Opposite.cancelMonoid α, Opposite.commMonoid α with  }

instance  [DivInvMonoidₓ α] : DivInvMonoidₓ (Opposite α) :=
  { Opposite.monoid α, Opposite.hasInv α with zpow := fun n x => op$ x.unop ^ n,
    zpow_zero' := fun x => unop_injective$ DivInvMonoidₓ.zpow_zero' x.unop,
    zpow_succ' :=
      fun n x =>
        unop_injective$
          by 
            rw [unop_op, zpow_of_nat, zpow_of_nat, pow_succ'ₓ, unop_mul, unop_op],
    zpow_neg' := fun z x => unop_injective$ DivInvMonoidₓ.zpow_neg' z x.unop }

instance  [Groupₓ α] : Groupₓ (Opposite α) :=
  { Opposite.divInvMonoid α with mul_left_inv := fun x => unop_injective$ mul_inv_selfₓ$ unop x }

instance  [CommGroupₓ α] : CommGroupₓ (Opposite α) :=
  { Opposite.group α, Opposite.commMonoid α with  }

instance  [Distrib α] : Distrib (Opposite α) :=
  { Opposite.hasAdd α, Opposite.hasMul α with
    left_distrib := fun x y z => unop_injective$ add_mulₓ (unop y) (unop z) (unop x),
    right_distrib := fun x y z => unop_injective$ mul_addₓ (unop z) (unop x) (unop y) }

instance  [MulZeroClass α] : MulZeroClass (Opposite α) :=
  { zero := 0, mul := ·*·, zero_mul := fun x => unop_injective$ mul_zero$ unop x,
    mul_zero := fun x => unop_injective$ zero_mul$ unop x }

instance  [MulZeroOneClass α] : MulZeroOneClass (Opposite α) :=
  { Opposite.mulZeroClass α, Opposite.mulOneClass α with  }

instance  [SemigroupWithZero α] : SemigroupWithZero (Opposite α) :=
  { Opposite.semigroup α, Opposite.mulZeroClass α with  }

instance  [MonoidWithZeroₓ α] : MonoidWithZeroₓ (Opposite α) :=
  { Opposite.monoid α, Opposite.mulZeroOneClass α with  }

instance  [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Opposite α) :=
  { Opposite.addCommMonoid α, Opposite.mulZeroClass α, Opposite.distrib α with  }

instance  [NonUnitalSemiring α] : NonUnitalSemiring (Opposite α) :=
  { Opposite.semigroupWithZero α, Opposite.nonUnitalNonAssocSemiring α with  }

instance  [NonAssocSemiring α] : NonAssocSemiring (Opposite α) :=
  { Opposite.mulZeroOneClass α, Opposite.nonUnitalNonAssocSemiring α with  }

instance  [Semiringₓ α] : Semiringₓ (Opposite α) :=
  { Opposite.nonUnitalSemiring α, Opposite.nonAssocSemiring α, Opposite.monoidWithZero α with  }

instance  [CommSemiringₓ α] : CommSemiringₓ (Opposite α) :=
  { Opposite.semiring α, Opposite.commSemigroup α with  }

instance  [Ringₓ α] : Ringₓ (Opposite α) :=
  { Opposite.addCommGroup α, Opposite.monoid α, Opposite.semiring α with  }

instance  [CommRingₓ α] : CommRingₓ (Opposite α) :=
  { Opposite.ring α, Opposite.commSemiring α with  }

instance  [HasZero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Opposite α) :=
  { eq_zero_or_eq_zero_of_mul_eq_zero :=
      fun x y H : op (_*_) = op (0 : α) =>
        Or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero$ op_injective H) (fun hy => Or.inr$ unop_injective$ hy)
          fun hx => Or.inl$ unop_injective$ hx }

instance  [Ringₓ α] [IsDomain α] : IsDomain (Opposite α) :=
  { Opposite.no_zero_divisors α, Opposite.ring α, Opposite.nontrivial α with  }

instance  [GroupWithZeroₓ α] : GroupWithZeroₓ (Opposite α) :=
  { Opposite.monoidWithZero α, Opposite.divInvMonoid α, Opposite.nontrivial α with
    mul_inv_cancel := fun x hx => unop_injective$ inv_mul_cancel$ unop_injective.Ne hx,
    inv_zero := unop_injective inv_zero }

instance  [DivisionRing α] : DivisionRing (Opposite α) :=
  { Opposite.groupWithZero α, Opposite.ring α with  }

instance  [Field α] : Field (Opposite α) :=
  { Opposite.divisionRing α, Opposite.commRing α with  }

instance  (R : Type _) [Monoidₓ R] [MulAction R α] : MulAction R (Opposite α) :=
  { Opposite.hasScalar α R with one_smul := fun x => unop_injective$ one_smul R (unop x),
    mul_smul := fun r₁ r₂ x => unop_injective$ mul_smul r₁ r₂ (unop x) }

instance  (R : Type _) [Monoidₓ R] [AddMonoidₓ α] [DistribMulAction R α] : DistribMulAction R (Opposite α) :=
  { Opposite.mulAction α R with smul_add := fun r x₁ x₂ => unop_injective$ smul_add r (unop x₁) (unop x₂),
    smul_zero := fun r => unop_injective$ smul_zero r }

instance  (R : Type _) [Monoidₓ R] [Monoidₓ α] [MulDistribMulAction R α] : MulDistribMulAction R (Opposite α) :=
  { Opposite.mulAction α R with smul_mul := fun r x₁ x₂ => unop_injective$ smul_mul' r (unop x₂) (unop x₁),
    smul_one := fun r => unop_injective$ smul_one r }

instance  {M N} [HasScalar M N] [HasScalar M α] [HasScalar N α] [IsScalarTower M N α] :
  IsScalarTower M N («expr ᵒᵖ» α) :=
  ⟨fun x y z => unop_injective$ smul_assoc _ _ _⟩

instance  {M N} [HasScalar M α] [HasScalar N α] [SmulCommClass M N α] : SmulCommClass M N («expr ᵒᵖ» α) :=
  ⟨fun x y z => unop_injective$ smul_comm _ _ _⟩

/-- Like `has_mul.to_has_scalar`, but multiplies on the right.

See also `monoid.to_opposite_mul_action` and `monoid_with_zero.to_opposite_mul_action`. -/
instance _root_.has_mul.to_has_opposite_scalar [Mul α] : HasScalar (Opposite α) α :=
  { smul := fun c x => x*c.unop }

@[simp]
theorem op_smul_eq_mul [Mul α] {a a' : α} : op a • a' = a'*a :=
  rfl

/-- The right regular action of a group on itself is transitive. -/
instance _root_.mul_action.opposite_regular.is_pretransitive {G : Type _} [Groupₓ G] :
  MulAction.IsPretransitive («expr ᵒᵖ» G) G :=
  ⟨fun x y => ⟨op (x⁻¹*y), mul_inv_cancel_left _ _⟩⟩

instance _root_.semigroup.opposite_smul_comm_class [Semigroupₓ α] : SmulCommClass (Opposite α) α α :=
  { smul_comm := fun x y z => mul_assocₓ _ _ _ }

instance _root_.semigroup.opposite_smul_comm_class' [Semigroupₓ α] : SmulCommClass α (Opposite α) α :=
  { smul_comm := fun x y z => (mul_assocₓ _ _ _).symm }

/-- Like `monoid.to_mul_action`, but multiplies on the right. -/
instance _root_.monoid.to_opposite_mul_action [Monoidₓ α] : MulAction (Opposite α) α :=
  { smul := · • ·, one_smul := mul_oneₓ, mul_smul := fun x y r => (mul_assocₓ _ _ _).symm }

instance _root_.is_scalar_tower.opposite_mid {M N} [Monoidₓ N] [HasScalar M N] [SmulCommClass M N N] :
  IsScalarTower M («expr ᵒᵖ» N) N :=
  ⟨fun x y z => mul_smul_comm _ _ _⟩

instance _root_.smul_comm_class.opposite_mid {M N} [Monoidₓ N] [HasScalar M N] [IsScalarTower M N N] :
  SmulCommClass M («expr ᵒᵖ» N) N :=
  ⟨fun x y z =>
      by 
        induction y using Opposite.rec 
        simp [smul_mul_assoc]⟩

example  [Monoidₓ α] : Monoidₓ.toMulAction (Opposite α) = Opposite.mulAction α (Opposite α) :=
  rfl

/-- `monoid.to_opposite_mul_action` is faithful on cancellative monoids. -/
instance _root_.left_cancel_monoid.to_has_faithful_opposite_scalar [LeftCancelMonoid α] :
  HasFaithfulScalar (Opposite α) α :=
  ⟨fun x y h => unop_injective$ mul_left_cancelₓ (h 1)⟩

/-- `monoid.to_opposite_mul_action` is faithful on nontrivial cancellative monoids with zero. -/
instance _root_.cancel_monoid_with_zero.to_has_faithful_opposite_scalar [CancelMonoidWithZero α] [Nontrivial α] :
  HasFaithfulScalar (Opposite α) α :=
  ⟨fun x y h => unop_injective$ mul_left_cancel₀ one_ne_zero (h 1)⟩

variable{α}

theorem semiconj_by.op [Mul α] {a x y : α} (h : SemiconjBy a x y) : SemiconjBy (op a) (op y) (op x) :=
  by 
    dunfold SemiconjBy 
    rw [←op_mul, ←op_mul, h.eq]

theorem semiconj_by.unop [Mul α] {a x y : «expr ᵒᵖ» α} (h : SemiconjBy a x y) : SemiconjBy (unop a) (unop y) (unop x) :=
  by 
    dunfold SemiconjBy 
    rw [←unop_mul, ←unop_mul, h.eq]

@[simp]
theorem semiconj_by_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y :=
  by 
    split 
    ·
      intro h 
      rw [←unop_op a, ←unop_op x, ←unop_op y]
      exact semiconj_by.unop h
    ·
      intro h 
      exact semiconj_by.op h

@[simp]
theorem semiconj_by_unop [Mul α] {a x y : «expr ᵒᵖ» α} : SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y :=
  by 
    convRHS => rw [←op_unop a, ←op_unop x, ←op_unop y, semiconj_by_op]

theorem commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  by 
    dunfold Commute  at h⊢
    exact semiconj_by.op h

theorem commute.unop [Mul α] {x y : «expr ᵒᵖ» α} (h : Commute x y) : Commute (unop x) (unop y) :=
  by 
    dunfold Commute  at h⊢
    exact semiconj_by.unop h

@[simp]
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  by 
    dunfold Commute 
    rw [semiconj_by_op]

@[simp]
theorem commute_unop [Mul α] {x y : «expr ᵒᵖ» α} : Commute (unop x) (unop y) ↔ Commute x y :=
  by 
    dunfold Commute 
    rw [semiconj_by_unop]

/-- The function `op` is an additive equivalence. -/
def op_add_equiv [Add α] : α ≃+ «expr ᵒᵖ» α :=
  { equiv_to_opposite with map_add' := fun a b => rfl }

@[simp]
theorem coe_op_add_equiv [Add α] : (op_add_equiv : α → «expr ᵒᵖ» α) = op :=
  rfl

@[simp]
theorem coe_op_add_equiv_symm [Add α] : (op_add_equiv.symm : «expr ᵒᵖ» α → α) = unop :=
  rfl

@[simp]
theorem op_add_equiv_to_equiv [Add α] : (op_add_equiv : α ≃+ «expr ᵒᵖ» α).toEquiv = equiv_to_opposite :=
  rfl

end Opposite

open Opposite

/-- Inversion on a group is a `mul_equiv` to the opposite group. When `G` is commutative, there is
`mul_equiv.inv`. -/
@[simps (config := { fullyApplied := ff })]
def MulEquiv.inv' (G : Type _) [Groupₓ G] : G ≃* «expr ᵒᵖ» G :=
  { (Equiv.inv G).trans equiv_to_opposite with toFun := Opposite.op ∘ HasInv.inv, invFun := HasInv.inv ∘ Opposite.unop,
    map_mul' := fun x y => unop_injective$ mul_inv_rev x y }

/-- A monoid homomorphism `f : R →* S` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Sᵒᵖ`. -/
@[simps (config := { fullyApplied := ff })]
def MonoidHom.toOpposite {R S : Type _} [MulOneClass R] [MulOneClass S] (f : R →* S) (hf : ∀ x y, Commute (f x) (f y)) :
  R →* «expr ᵒᵖ» S :=
  { toFun := Opposite.op ∘ f, map_one' := congr_argₓ op f.map_one,
    map_mul' :=
      fun x y =>
        by 
          simp [(hf x y).Eq] }

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵒᵖ`. -/
@[simps (config := { fullyApplied := ff })]
def RingHom.toOpposite {R S : Type _} [Semiringₓ R] [Semiringₓ S] (f : R →+* S) (hf : ∀ x y, Commute (f x) (f y)) :
  R →+* «expr ᵒᵖ» S :=
  { ((Opposite.opAddEquiv : S ≃+ «expr ᵒᵖ» S).toAddMonoidHom.comp («expr↑ » f) : R →+ «expr ᵒᵖ» S),
    f.to_monoid_hom.to_opposite hf with toFun := Opposite.op ∘ f }

/-- The units of the opposites are equivalent to the opposites of the units. -/
def Units.opEquiv {R} [Monoidₓ R] : Units («expr ᵒᵖ» R) ≃* «expr ᵒᵖ» (Units R) :=
  { toFun := fun u => op ⟨unop u, unop («expr↑ » (u⁻¹)), op_injective u.4, op_injective u.3⟩,
    invFun := Opposite.rec$ fun u => ⟨op («expr↑ » u), op («expr↑ » (u⁻¹)), unop_injective$ u.4, unop_injective u.3⟩,
    map_mul' := fun x y => unop_injective$ Units.ext$ rfl, left_inv := fun x => Units.ext$ rfl,
    right_inv := fun x => unop_injective$ Units.ext$ rfl }

@[simp]
theorem Units.coe_unop_op_equiv {R} [Monoidₓ R] (u : Units («expr ᵒᵖ» R)) :
  ((Units.opEquiv u).unop : R) = unop (u : «expr ᵒᵖ» R) :=
  rfl

@[simp]
theorem Units.coe_op_equiv_symm {R} [Monoidₓ R] (u : «expr ᵒᵖ» (Units R)) :
  (Units.opEquiv.symm u : «expr ᵒᵖ» R) = op (u.unop : R) :=
  rfl

/-- A hom `α →* β` can equivalently be viewed as a hom `αᵒᵖ →* βᵒᵖ`. This is the action of the
(fully faithful) `ᵒᵖ`-functor on morphisms. -/
@[simps]
def MonoidHom.op {α β} [MulOneClass α] [MulOneClass β] : (α →* β) ≃ («expr ᵒᵖ» α →* «expr ᵒᵖ» β) :=
  { toFun :=
      fun f =>
        { toFun := op ∘ f ∘ unop, map_one' := unop_injective f.map_one,
          map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) },
    invFun :=
      fun f =>
        { toFun := unop ∘ f ∘ op, map_one' := congr_argₓ unop f.map_one,
          map_mul' := fun x y => congr_argₓ unop (f.map_mul (op y) (op x)) },
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rfl }

/-- The 'unopposite' of a monoid hom `αᵒᵖ →* βᵒᵖ`. Inverse to `monoid_hom.op`. -/
@[simp]
def MonoidHom.unop {α β} [MulOneClass α] [MulOneClass β] : («expr ᵒᵖ» α →* «expr ᵒᵖ» β) ≃ (α →* β) :=
  MonoidHom.op.symm

/-- A hom `α →+ β` can equivalently be viewed as a hom `αᵒᵖ →+ βᵒᵖ`. This is the action of the
(fully faithful) `ᵒᵖ`-functor on morphisms. -/
@[simps]
def AddMonoidHom.op {α β} [AddZeroClass α] [AddZeroClass β] : (α →+ β) ≃ («expr ᵒᵖ» α →+ «expr ᵒᵖ» β) :=
  { toFun :=
      fun f =>
        { toFun := op ∘ f ∘ unop, map_zero' := unop_injective f.map_zero,
          map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) },
    invFun :=
      fun f =>
        { toFun := unop ∘ f ∘ op, map_zero' := congr_argₓ unop f.map_zero,
          map_add' := fun x y => congr_argₓ unop (f.map_add (op x) (op y)) },
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rfl }

/-- The 'unopposite' of an additive monoid hom `αᵒᵖ →+ βᵒᵖ`. Inverse to `add_monoid_hom.op`. -/
@[simp]
def AddMonoidHom.unop {α β} [AddZeroClass α] [AddZeroClass β] : («expr ᵒᵖ» α →+ «expr ᵒᵖ» β) ≃ (α →+ β) :=
  AddMonoidHom.op.symm

/-- A ring hom `α →+* β` can equivalently be viewed as a ring hom `αᵒᵖ →+* βᵒᵖ`. This is the action
of the (fully faithful) `ᵒᵖ`-functor on morphisms. -/
@[simps]
def RingHom.op {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (α →+* β) ≃ («expr ᵒᵖ» α →+* «expr ᵒᵖ» β) :=
  { toFun := fun f => { f.to_add_monoid_hom.op, f.to_monoid_hom.op with  },
    invFun := fun f => { f.to_add_monoid_hom.unop, f.to_monoid_hom.unop with  },
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rfl }

/-- The 'unopposite' of a ring hom `αᵒᵖ →+* βᵒᵖ`. Inverse to `ring_hom.op`. -/
@[simp]
def RingHom.unop {α β} [NonAssocSemiring α] [NonAssocSemiring β] : («expr ᵒᵖ» α →+* «expr ᵒᵖ» β) ≃ (α →+* β) :=
  RingHom.op.symm

/-- A iso `α ≃+ β` can equivalently be viewed as an iso `αᵒᵖ ≃+ βᵒᵖ`. -/
@[simps]
def AddEquiv.op {α β} [Add α] [Add β] : α ≃+ β ≃ («expr ᵒᵖ» α ≃+ «expr ᵒᵖ» β) :=
  { toFun := fun f => op_add_equiv.symm.trans (f.trans op_add_equiv),
    invFun := fun f => op_add_equiv.trans (f.trans op_add_equiv.symm),
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rfl }

/-- The 'unopposite' of an iso `αᵒᵖ ≃+ βᵒᵖ`. Inverse to `add_equiv.op`. -/
@[simp]
def AddEquiv.unop {α β} [Add α] [Add β] : «expr ᵒᵖ» α ≃+ «expr ᵒᵖ» β ≃ (α ≃+ β) :=
  AddEquiv.op.symm

/-- A iso `α ≃* β` can equivalently be viewed as an iso `αᵒᵖ ≃+ βᵒᵖ`. -/
@[simps]
def MulEquiv.op {α β} [Mul α] [Mul β] : α ≃* β ≃ («expr ᵒᵖ» α ≃* «expr ᵒᵖ» β) :=
  { toFun :=
      fun f =>
        { toFun := op ∘ f ∘ unop, invFun := op ∘ f.symm ∘ unop,
          left_inv := fun x => unop_injective (f.symm_apply_apply x.unop),
          right_inv := fun x => unop_injective (f.apply_symm_apply x.unop),
          map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) },
    invFun :=
      fun f =>
        { toFun := unop ∘ f ∘ op, invFun := unop ∘ f.symm ∘ op,
          left_inv := fun x => op_injective (f.symm_apply_apply (op x)),
          right_inv := fun x => op_injective (f.apply_symm_apply (op x)),
          map_mul' := fun x y => congr_argₓ unop (f.map_mul (op y) (op x)) },
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rfl }

/-- The 'unopposite' of an iso `αᵒᵖ ≃* βᵒᵖ`. Inverse to `mul_equiv.op`. -/
@[simp]
def MulEquiv.unop {α β} [Mul α] [Mul β] : «expr ᵒᵖ» α ≃* «expr ᵒᵖ» β ≃ (α ≃* β) :=
  MulEquiv.op.symm

section Ext

/-- This ext lemma change equalities on `αᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `finsupp.add_hom_ext'`. -/
@[ext]
theorem AddMonoidHom.op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : «expr ᵒᵖ» α →+ β)
  (h :
    f.comp (op_add_equiv : α ≃+ «expr ᵒᵖ» α).toAddMonoidHom = g.comp (op_add_equiv : α ≃+ «expr ᵒᵖ» α).toAddMonoidHom) :
  f = g :=
  AddMonoidHom.ext$ fun x => (AddMonoidHom.congr_fun h : _) x.unop

end Ext

