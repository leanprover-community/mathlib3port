import Mathbin.Algebra.Group.InjSurj 
import Mathbin.Algebra.Group.Commute 
import Mathbin.Algebra.Opposites 
import Mathbin.Data.Equiv.MulAdd

/-!
# Group structures on the multiplicative opposite
-/


universe u v

variable (α : Type u)

namespace MulOpposite

instance [AddSemigroupₓ α] : AddSemigroupₓ («expr ᵐᵒᵖ» α) :=
  unop_injective.AddSemigroup _ fun x y => rfl

instance [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup («expr ᵐᵒᵖ» α) :=
  unop_injective.AddLeftCancelSemigroup _ fun x y => rfl

instance [AddRightCancelSemigroup α] : AddRightCancelSemigroup («expr ᵐᵒᵖ» α) :=
  unop_injective.AddRightCancelSemigroup _ fun x y => rfl

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ («expr ᵐᵒᵖ» α) :=
  { MulOpposite.addSemigroup α with add_comm := fun x y => unop_injective$ add_commₓ (unop x) (unop y) }

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

