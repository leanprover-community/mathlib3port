import Mathbin.Algebra.Group.Commute 
import Mathbin.Algebra.Ring.Basic 
import Mathbin.Data.Equiv.MulAdd

/-!
# Multiplicative opposite and algebraic operations on it

In this file we define `mul_opposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It
inherits all additive algebraic structures on `α`, and reverses the order of multipliers in
multiplicative structures, i.e., `op (x * y) = op x * op y`, where `mul_opposite.op` is the
canonical map from `α` to `αᵐᵒᵖ`.

## Notation

`αᵐᵒᵖ = mul_opposite α`
-/


universe u v

open Function

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication.-/
def MulOpposite (α : Type u) : Type u :=
  α

-- error in Algebra.Opposites: ././Mathport/Syntax/Translate/Basic.lean:265:9: unsupported: advanced prec syntax
postfix `ᵐᵒᵖ`:std.prec.max_plus := mul_opposite

namespace MulOpposite

variable {α : Type u}

/-- The element of `mul_opposite α` that represents `x : α`. -/
@[pp_nodot]
def op : α → «expr ᵐᵒᵖ» α :=
  id

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[pp_nodot]
def unop : «expr ᵐᵒᵖ» α → α :=
  id

@[simp]
theorem unop_op (x : α) : unop (op x) = x :=
  rfl

@[simp]
theorem op_unop (x : «expr ᵐᵒᵖ» α) : op (unop x) = x :=
  rfl

@[simp]
theorem op_comp_unop : (op : α → «expr ᵐᵒᵖ» α) ∘ unop = id :=
  rfl

@[simp]
theorem unop_comp_op : (unop : «expr ᵐᵒᵖ» α → α) ∘ op = id :=
  rfl

attribute [irreducible] MulOpposite

/-- A recursor for `opposite`. Use as `induction x using mul_opposite.rec`. -/
@[simp]
protected def rec {F : ∀ X : «expr ᵐᵒᵖ» α, Sort v} (h : ∀ X, F (op X)) : ∀ X, F X :=
  fun X => h (unop X)

/-- The canonical bijection between `αᵐᵒᵖ` and `α`. -/
@[simps (config := { fullyApplied := ff }) apply symmApply]
def op_equiv : α ≃ «expr ᵐᵒᵖ» α :=
  ⟨op, unop, unop_op, op_unop⟩

theorem op_bijective : bijective (op : α → «expr ᵐᵒᵖ» α) :=
  op_equiv.Bijective

theorem unop_bijective : bijective (unop : «expr ᵐᵒᵖ» α → α) :=
  op_equiv.symm.Bijective

theorem op_injective : injective (op : α → «expr ᵐᵒᵖ» α) :=
  op_bijective.Injective

theorem op_surjective : surjective (op : α → «expr ᵐᵒᵖ» α) :=
  op_bijective.Surjective

theorem unop_injective : injective (unop : «expr ᵐᵒᵖ» α → α) :=
  unop_bijective.Injective

theorem unop_surjective : surjective (unop : «expr ᵐᵒᵖ» α → α) :=
  unop_bijective.Surjective

@[simp]
theorem op_inj {x y : α} : op x = op y ↔ x = y :=
  op_injective.eq_iff

@[simp]
theorem unop_inj {x y : «expr ᵐᵒᵖ» α} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

variable (α)

instance [Nontrivial α] : Nontrivial («expr ᵐᵒᵖ» α) :=
  op_injective.Nontrivial

instance [Inhabited α] : Inhabited («expr ᵐᵒᵖ» α) :=
  ⟨op (default α)⟩

instance [Subsingleton α] : Subsingleton («expr ᵐᵒᵖ» α) :=
  unop_injective.Subsingleton

instance [Unique α] : Unique («expr ᵐᵒᵖ» α) :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty («expr ᵐᵒᵖ» α) :=
  Function.is_empty unop

instance [HasZero α] : HasZero («expr ᵐᵒᵖ» α) :=
  { zero := op 0 }

instance [HasOne α] : HasOne («expr ᵐᵒᵖ» α) :=
  { one := op 1 }

instance [Add α] : Add («expr ᵐᵒᵖ» α) :=
  { add := fun x y => op (unop x+unop y) }

instance [Sub α] : Sub («expr ᵐᵒᵖ» α) :=
  { sub := fun x y => op (unop x - unop y) }

instance [Neg α] : Neg («expr ᵐᵒᵖ» α) :=
  { neg := fun x => op$ -unop x }

instance [Mul α] : Mul («expr ᵐᵒᵖ» α) :=
  { mul := fun x y => op (unop y*unop x) }

instance [HasInv α] : HasInv («expr ᵐᵒᵖ» α) :=
  { inv := fun x => op$ unop x⁻¹ }

instance (R : Type _) [HasScalar R α] : HasScalar R («expr ᵐᵒᵖ» α) :=
  { smul := fun c x => op (c • unop x) }

section 

variable (α)

@[simp]
theorem op_zero [HasZero α] : op (0 : α) = 0 :=
  rfl

@[simp]
theorem unop_zero [HasZero α] : unop (0 : «expr ᵐᵒᵖ» α) = 0 :=
  rfl

@[simp]
theorem op_one [HasOne α] : op (1 : α) = 1 :=
  rfl

@[simp]
theorem unop_one [HasOne α] : unop (1 : «expr ᵐᵒᵖ» α) = 1 :=
  rfl

variable {α}

@[simp]
theorem op_add [Add α] (x y : α) : op (x+y) = op x+op y :=
  rfl

@[simp]
theorem unop_add [Add α] (x y : «expr ᵐᵒᵖ» α) : unop (x+y) = unop x+unop y :=
  rfl

@[simp]
theorem op_neg [Neg α] (x : α) : op (-x) = -op x :=
  rfl

@[simp]
theorem unop_neg [Neg α] (x : «expr ᵐᵒᵖ» α) : unop (-x) = -unop x :=
  rfl

@[simp]
theorem op_mul [Mul α] (x y : α) : op (x*y) = op y*op x :=
  rfl

@[simp]
theorem unop_mul [Mul α] (x y : «expr ᵐᵒᵖ» α) : unop (x*y) = unop y*unop x :=
  rfl

@[simp]
theorem op_inv [HasInv α] (x : α) : op (x⁻¹) = op x⁻¹ :=
  rfl

@[simp]
theorem unop_inv [HasInv α] (x : «expr ᵐᵒᵖ» α) : unop (x⁻¹) = unop x⁻¹ :=
  rfl

@[simp]
theorem op_sub [Sub α] (x y : α) : op (x - y) = op x - op y :=
  rfl

@[simp]
theorem unop_sub [Sub α] (x y : «expr ᵐᵒᵖ» α) : unop (x - y) = unop x - unop y :=
  rfl

@[simp]
theorem op_smul {R : Type _} [HasScalar R α] (c : R) (a : α) : op (c • a) = c • op a :=
  rfl

@[simp]
theorem unop_smul {R : Type _} [HasScalar R α] (c : R) (a : «expr ᵐᵒᵖ» α) : unop (c • a) = c • unop a :=
  rfl

end 

instance [AddSemigroupₓ α] : AddSemigroupₓ («expr ᵐᵒᵖ» α) :=
  unop_injective.AddSemigroup _ fun x y => rfl

instance [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup («expr ᵐᵒᵖ» α) :=
  unop_injective.AddLeftCancelSemigroup _ fun x y => rfl

instance [AddRightCancelSemigroup α] : AddRightCancelSemigroup («expr ᵐᵒᵖ» α) :=
  unop_injective.AddRightCancelSemigroup _ fun x y => rfl

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.addSemigroup α with add_comm := fun x y => unop_injective$ add_commₓ (unop x) (unop y) }

@[simp]
theorem unop_eq_zero_iff {α} [HasZero α] (a : «expr ᵐᵒᵖ» α) : a.unop = (0 : α) ↔ a = (0 : «expr ᵐᵒᵖ» α) :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_zero_iff {α} [HasZero α] (a : α) : op a = (0 : «expr ᵐᵒᵖ» α) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl

theorem unop_ne_zero_iff {α} [HasZero α] (a : «expr ᵐᵒᵖ» α) : a.unop ≠ (0 : α) ↔ a ≠ (0 : «expr ᵐᵒᵖ» α) :=
  not_congr$ unop_eq_zero_iff a

theorem op_ne_zero_iff {α} [HasZero α] (a : α) : op a ≠ (0 : «expr ᵐᵒᵖ» α) ↔ a ≠ (0 : α) :=
  not_congr$ op_eq_zero_iff a

instance [AddZeroClass α] : AddZeroClass («expr ᵐᵒᵖ» α) :=
  unop_injective.AddZeroClass _ rfl fun x y => rfl

instance [AddMonoidₓ α] : AddMonoidₓ («expr ᵐᵒᵖ» α) :=
  unop_injective.addMonoidSmul _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [AddCommMonoidₓ α] : AddCommMonoidₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.addMonoid α, MulOpposite.addCommSemigroup α with  }

instance [SubNegMonoidₓ α] : SubNegMonoidₓ («expr ᵐᵒᵖ» α) :=
  unop_injective.subNegMonoidSmul _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [AddGroupₓ α] : AddGroupₓ («expr ᵐᵒᵖ» α) :=
  unop_injective.addGroupSmul _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [AddCommGroupₓ α] : AddCommGroupₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.addGroup α, MulOpposite.addCommMonoid α with  }

instance [Semigroupₓ α] : Semigroupₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.hasMul α with mul_assoc := fun x y z => unop_injective$ Eq.symm$ mul_assocₓ (unop z) (unop y) (unop x) }

instance [RightCancelSemigroup α] : LeftCancelSemigroup («expr ᵐᵒᵖ» α) :=
  { MulOpposite.semigroup α with mul_left_cancel := fun x y z H => unop_injective$ mul_right_cancelₓ$ op_injective H }

instance [LeftCancelSemigroup α] : RightCancelSemigroup («expr ᵐᵒᵖ» α) :=
  { MulOpposite.semigroup α with mul_right_cancel := fun x y z H => unop_injective$ mul_left_cancelₓ$ op_injective H }

instance [CommSemigroupₓ α] : CommSemigroupₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.semigroup α with mul_comm := fun x y => unop_injective$ mul_commₓ (unop y) (unop x) }

@[simp]
theorem unop_eq_one_iff {α} [HasOne α] (a : «expr ᵐᵒᵖ» α) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_one_iff {α} [HasOne α] (a : α) : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' rfl

instance [MulOneClass α] : MulOneClass («expr ᵐᵒᵖ» α) :=
  { MulOpposite.hasMul α, MulOpposite.hasOne α with one_mul := fun x => unop_injective$ mul_oneₓ$ unop x,
    mul_one := fun x => unop_injective$ one_mulₓ$ unop x }

instance [Monoidₓ α] : Monoidₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.semigroup α, MulOpposite.mulOneClass α with npow := fun n x => op$ x.unop ^ n,
    npow_zero' := fun x => unop_injective$ Monoidₓ.npow_zero' x.unop,
    npow_succ' := fun n x => unop_injective$ pow_succ'ₓ x.unop n }

instance [RightCancelMonoid α] : LeftCancelMonoid («expr ᵐᵒᵖ» α) :=
  { MulOpposite.leftCancelSemigroup α, MulOpposite.monoid α with  }

instance [LeftCancelMonoid α] : RightCancelMonoid («expr ᵐᵒᵖ» α) :=
  { MulOpposite.rightCancelSemigroup α, MulOpposite.monoid α with  }

instance [CancelMonoid α] : CancelMonoid («expr ᵐᵒᵖ» α) :=
  { MulOpposite.rightCancelMonoid α, MulOpposite.leftCancelMonoid α with  }

instance [CommMonoidₓ α] : CommMonoidₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.monoid α, MulOpposite.commSemigroup α with  }

instance [CancelCommMonoid α] : CancelCommMonoid («expr ᵐᵒᵖ» α) :=
  { MulOpposite.cancelMonoid α, MulOpposite.commMonoid α with  }

instance [DivInvMonoidₓ α] : DivInvMonoidₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.monoid α, MulOpposite.hasInv α with zpow := fun n x => op$ x.unop ^ n,
    zpow_zero' := fun x => unop_injective$ DivInvMonoidₓ.zpow_zero' x.unop,
    zpow_succ' :=
      fun n x =>
        unop_injective$
          by 
            rw [unop_op, zpow_of_nat, zpow_of_nat, pow_succ'ₓ, unop_mul, unop_op],
    zpow_neg' := fun z x => unop_injective$ DivInvMonoidₓ.zpow_neg' z x.unop }

instance [Groupₓ α] : Groupₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.divInvMonoid α with mul_left_inv := fun x => unop_injective$ mul_inv_selfₓ$ unop x }

instance [CommGroupₓ α] : CommGroupₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.group α, MulOpposite.commMonoid α with  }

instance [Distrib α] : Distrib («expr ᵐᵒᵖ» α) :=
  { MulOpposite.hasAdd α, MulOpposite.hasMul α with
    left_distrib := fun x y z => unop_injective$ add_mulₓ (unop y) (unop z) (unop x),
    right_distrib := fun x y z => unop_injective$ mul_addₓ (unop z) (unop x) (unop y) }

instance [MulZeroClass α] : MulZeroClass («expr ᵐᵒᵖ» α) :=
  { zero := 0, mul := ·*·, zero_mul := fun x => unop_injective$ mul_zero$ unop x,
    mul_zero := fun x => unop_injective$ zero_mul$ unop x }

instance [MulZeroOneClass α] : MulZeroOneClass («expr ᵐᵒᵖ» α) :=
  { MulOpposite.mulZeroClass α, MulOpposite.mulOneClass α with  }

instance [SemigroupWithZero α] : SemigroupWithZero («expr ᵐᵒᵖ» α) :=
  { MulOpposite.semigroup α, MulOpposite.mulZeroClass α with  }

instance [MonoidWithZeroₓ α] : MonoidWithZeroₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.monoid α, MulOpposite.mulZeroOneClass α with  }

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring («expr ᵐᵒᵖ» α) :=
  { MulOpposite.addCommMonoid α, MulOpposite.mulZeroClass α, MulOpposite.distrib α with  }

instance [NonUnitalSemiring α] : NonUnitalSemiring («expr ᵐᵒᵖ» α) :=
  { MulOpposite.semigroupWithZero α, MulOpposite.nonUnitalNonAssocSemiring α with  }

instance [NonAssocSemiring α] : NonAssocSemiring («expr ᵐᵒᵖ» α) :=
  { MulOpposite.mulZeroOneClass α, MulOpposite.nonUnitalNonAssocSemiring α with  }

instance [Semiringₓ α] : Semiringₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.nonUnitalSemiring α, MulOpposite.nonAssocSemiring α, MulOpposite.monoidWithZero α with  }

instance [CommSemiringₓ α] : CommSemiringₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.semiring α, MulOpposite.commSemigroup α with  }

instance [Ringₓ α] : Ringₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.addCommGroup α, MulOpposite.monoid α, MulOpposite.semiring α with  }

instance [CommRingₓ α] : CommRingₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.ring α, MulOpposite.commSemiring α with  }

instance [HasZero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors («expr ᵐᵒᵖ» α) :=
  { eq_zero_or_eq_zero_of_mul_eq_zero :=
      fun x y H : op (_*_) = op (0 : α) =>
        Or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero$ op_injective H) (fun hy => Or.inr$ unop_injective$ hy)
          fun hx => Or.inl$ unop_injective$ hx }

instance [Ringₓ α] [IsDomain α] : IsDomain («expr ᵐᵒᵖ» α) :=
  { MulOpposite.no_zero_divisors α, MulOpposite.ring α, MulOpposite.nontrivial α with  }

instance [GroupWithZeroₓ α] : GroupWithZeroₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.monoidWithZero α, MulOpposite.divInvMonoid α, MulOpposite.nontrivial α with
    mul_inv_cancel := fun x hx => unop_injective$ inv_mul_cancel$ unop_injective.Ne hx,
    inv_zero := unop_injective inv_zero }

variable {α}

theorem semiconj_by.op [Mul α] {a x y : α} (h : SemiconjBy a x y) : SemiconjBy (op a) (op y) (op x) :=
  by 
    dunfold SemiconjBy 
    rw [←op_mul, ←op_mul, h.eq]

theorem semiconj_by.unop [Mul α] {a x y : «expr ᵐᵒᵖ» α} (h : SemiconjBy a x y) :
  SemiconjBy (unop a) (unop y) (unop x) :=
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
theorem semiconj_by_unop [Mul α] {a x y : «expr ᵐᵒᵖ» α} : SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y :=
  by 
    convRHS => rw [←op_unop a, ←op_unop x, ←op_unop y, semiconj_by_op]

theorem commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  by 
    dunfold Commute  at h⊢
    exact semiconj_by.op h

theorem commute.unop [Mul α] {x y : «expr ᵐᵒᵖ» α} (h : Commute x y) : Commute (unop x) (unop y) :=
  by 
    dunfold Commute  at h⊢
    exact semiconj_by.unop h

@[simp]
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  by 
    dunfold Commute 
    rw [semiconj_by_op]

@[simp]
theorem commute_unop [Mul α] {x y : «expr ᵐᵒᵖ» α} : Commute (unop x) (unop y) ↔ Commute x y :=
  by 
    dunfold Commute 
    rw [semiconj_by_unop]

/-- The function `unop` is an additive equivalence. -/
@[simps (config := { fullyApplied := ff, simpRhs := tt })]
def op_add_equiv [Add α] : α ≃+ «expr ᵐᵒᵖ» α :=
  { op_equiv with map_add' := fun a b => rfl }

@[simp]
theorem op_add_equiv_to_equiv [Add α] : (op_add_equiv : α ≃+ «expr ᵐᵒᵖ» α).toEquiv = op_equiv :=
  rfl

end MulOpposite

open MulOpposite

/-- Inversion on a group is a `mul_equiv` to the opposite group. When `G` is commutative, there is
`mul_equiv.inv`. -/
@[simps (config := { fullyApplied := ff, simpRhs := tt })]
def MulEquiv.inv' (G : Type _) [Groupₓ G] : G ≃* «expr ᵐᵒᵖ» G :=
  { (Equiv.inv G).trans op_equiv with map_mul' := fun x y => unop_injective$ mul_inv_rev x y }

/-- A monoid homomorphism `f : R →* S` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := ff })]
def MonoidHom.toOpposite {R S : Type _} [MulOneClass R] [MulOneClass S] (f : R →* S) (hf : ∀ x y, Commute (f x) (f y)) :
  R →* «expr ᵐᵒᵖ» S :=
  { toFun := MulOpposite.op ∘ f, map_one' := congr_argₓ op f.map_one,
    map_mul' :=
      fun x y =>
        by 
          simp [(hf x y).Eq] }

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := ff })]
def RingHom.toOpposite {R S : Type _} [Semiringₓ R] [Semiringₓ S] (f : R →+* S) (hf : ∀ x y, Commute (f x) (f y)) :
  R →+* «expr ᵐᵒᵖ» S :=
  { ((op_add_equiv : S ≃+ «expr ᵐᵒᵖ» S).toAddMonoidHom.comp («expr↑ » f) : R →+ «expr ᵐᵒᵖ» S),
    f.to_monoid_hom.to_opposite hf with toFun := MulOpposite.op ∘ f }

/-- The units of the opposites are equivalent to the opposites of the units. -/
def Units.opEquiv {R} [Monoidₓ R] : Units («expr ᵐᵒᵖ» R) ≃* «expr ᵐᵒᵖ» (Units R) :=
  { toFun := fun u => op ⟨unop u, unop («expr↑ » (u⁻¹)), op_injective u.4, op_injective u.3⟩,
    invFun := MulOpposite.rec$ fun u => ⟨op («expr↑ » u), op («expr↑ » (u⁻¹)), unop_injective$ u.4, unop_injective u.3⟩,
    map_mul' := fun x y => unop_injective$ Units.ext$ rfl,
    left_inv :=
      fun x =>
        Units.ext$
          by 
            simp ,
    right_inv := fun x => unop_injective$ Units.ext$ rfl }

@[simp]
theorem Units.coe_unop_op_equiv {R} [Monoidₓ R] (u : Units («expr ᵐᵒᵖ» R)) :
  ((Units.opEquiv u).unop : R) = unop (u : «expr ᵐᵒᵖ» R) :=
  rfl

@[simp]
theorem Units.coe_op_equiv_symm {R} [Monoidₓ R] (u : «expr ᵐᵒᵖ» (Units R)) :
  (Units.opEquiv.symm u : «expr ᵐᵒᵖ» R) = op (u.unop : R) :=
  rfl

/-- A hom `α →* β` can equivalently be viewed as a hom `αᵐᵒᵖ →* βᵐᵒᵖ`. This is the action of the
(fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def MonoidHom.op {α β} [MulOneClass α] [MulOneClass β] : (α →* β) ≃ («expr ᵐᵒᵖ» α →* «expr ᵐᵒᵖ» β) :=
  { toFun :=
      fun f =>
        { toFun := op ∘ f ∘ unop, map_one' := congr_argₓ op f.map_one,
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
          ext x 
          simp  }

/-- The 'unopposite' of a monoid hom `αᵐᵒᵖ →* βᵐᵒᵖ`. Inverse to `monoid_hom.op`. -/
@[simp]
def MonoidHom.unop {α β} [MulOneClass α] [MulOneClass β] : («expr ᵐᵒᵖ» α →* «expr ᵐᵒᵖ» β) ≃ (α →* β) :=
  MonoidHom.op.symm

/-- A hom `α →+ β` can equivalently be viewed as a hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. This is the action of the
(fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def AddMonoidHom.op {α β} [AddZeroClass α] [AddZeroClass β] : (α →+ β) ≃ («expr ᵐᵒᵖ» α →+ «expr ᵐᵒᵖ» β) :=
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
          simp  }

/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to `add_monoid_hom.op`. -/
@[simp]
def AddMonoidHom.unop {α β} [AddZeroClass α] [AddZeroClass β] : («expr ᵐᵒᵖ» α →+ «expr ᵐᵒᵖ» β) ≃ (α →+ β) :=
  AddMonoidHom.op.symm

/-- A ring hom `α →+* β` can equivalently be viewed as a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def RingHom.op {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (α →+* β) ≃ («expr ᵐᵒᵖ» α →+* «expr ᵐᵒᵖ» β) :=
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
          simp  }

/-- The 'unopposite' of a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. Inverse to `ring_hom.op`. -/
@[simp]
def RingHom.unop {α β} [NonAssocSemiring α] [NonAssocSemiring β] : («expr ᵐᵒᵖ» α →+* «expr ᵐᵒᵖ» β) ≃ (α →+* β) :=
  RingHom.op.symm

/-- A iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def AddEquiv.op {α β} [Add α] [Add β] : α ≃+ β ≃ («expr ᵐᵒᵖ» α ≃+ «expr ᵐᵒᵖ» β) :=
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
          simp  }

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `add_equiv.op`. -/
@[simp]
def AddEquiv.unop {α β} [Add α] [Add β] : «expr ᵐᵒᵖ» α ≃+ «expr ᵐᵒᵖ» β ≃ (α ≃+ β) :=
  AddEquiv.op.symm

/-- A iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def MulEquiv.op {α β} [Mul α] [Mul β] : α ≃* β ≃ («expr ᵐᵒᵖ» α ≃* «expr ᵐᵒᵖ» β) :=
  { toFun :=
      fun f =>
        { toFun := op ∘ f ∘ unop, invFun := op ∘ f.symm ∘ unop,
          left_inv := fun x => unop_injective (f.symm_apply_apply x.unop),
          right_inv := fun x => unop_injective (f.apply_symm_apply x.unop),
          map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) },
    invFun :=
      fun f =>
        { toFun := unop ∘ f ∘ op, invFun := unop ∘ f.symm ∘ op,
          left_inv :=
            fun x =>
              by 
                simp ,
          right_inv :=
            fun x =>
              by 
                simp ,
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
          simp  }

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. Inverse to `mul_equiv.op`. -/
@[simp]
def MulEquiv.unop {α β} [Mul α] [Mul β] : «expr ᵐᵒᵖ» α ≃* «expr ᵐᵒᵖ» β ≃ (α ≃* β) :=
  MulEquiv.op.symm

section Ext

/-- This ext lemma change equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `finsupp.add_hom_ext'`. -/
@[ext]
theorem AddMonoidHom.op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : «expr ᵐᵒᵖ» α →+ β)
  (h :
    f.comp (op_add_equiv : α ≃+ «expr ᵐᵒᵖ» α).toAddMonoidHom =
      g.comp (op_add_equiv : α ≃+ «expr ᵐᵒᵖ» α).toAddMonoidHom) :
  f = g :=
  AddMonoidHom.ext$ MulOpposite.rec$ fun x => (AddMonoidHom.congr_fun h : _) x

end Ext

