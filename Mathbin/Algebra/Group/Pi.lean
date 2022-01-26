import Mathbin.Data.Pi
import Mathbin.Data.Set.Function
import Mathbin.Tactic.PiInstances
import Mathbin.Algebra.Group.HomInstances

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/


universe u v w

variable {I : Type u}

variable {f : I → Type v}

variable (x y : ∀ i, f i) (i : I)

namespace Pi

@[to_additive]
instance Semigroupₓ [∀ i, Semigroupₓ <| f i] : Semigroupₓ (∀ i : I, f i) := by
  refine_struct { mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance SemigroupWithZero [∀ i, SemigroupWithZero <| f i] : SemigroupWithZero (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance CommSemigroupₓ [∀ i, CommSemigroupₓ <| f i] : CommSemigroupₓ (∀ i : I, f i) := by
  refine_struct { mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance MulOneClass [∀ i, MulOneClass <| f i] : MulOneClass (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance Monoidₓ [∀ i, Monoidₓ <| f i] : Monoidₓ (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := · * ·, npow := fun n x i => x i ^ n } <;>
    run_tac
      tactic.pi_instance_derive_field

@[simp]
theorem pow_apply [∀ i, Monoidₓ <| f i] (n : ℕ) : (x ^ n) i = x i ^ n :=
  rfl

@[to_additive]
instance CommMonoidₓ [∀ i, CommMonoidₓ <| f i] : CommMonoidₓ (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := · * ·, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance DivInvMonoidₓ [∀ i, DivInvMonoidₓ <| f i] : DivInvMonoidₓ (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i), mul := · * ·, inv := Inv.inv, div := Div.div, npow := Monoidₓ.npow,
        zpow := fun z x i => x i ^ z } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance Groupₓ [∀ i, Groupₓ <| f i] : Groupₓ (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i), mul := · * ·, inv := Inv.inv, div := Div.div, npow := Monoidₓ.npow,
        zpow := DivInvMonoidₓ.zpow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance CommGroupₓ [∀ i, CommGroupₓ <| f i] : CommGroupₓ (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i), mul := · * ·, inv := Inv.inv, div := Div.div, npow := Monoidₓ.npow,
        zpow := DivInvMonoidₓ.zpow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddLeftCancelSemigroup]
instance LeftCancelSemigroup [∀ i, LeftCancelSemigroup <| f i] : LeftCancelSemigroup (∀ i : I, f i) := by
  refine_struct { mul := · * · } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddRightCancelSemigroup]
instance RightCancelSemigroup [∀ i, RightCancelSemigroup <| f i] : RightCancelSemigroup (∀ i : I, f i) := by
  refine_struct { mul := · * · } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddLeftCancelMonoid]
instance LeftCancelMonoid [∀ i, LeftCancelMonoid <| f i] : LeftCancelMonoid (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := · * ·, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddRightCancelMonoid]
instance RightCancelMonoid [∀ i, RightCancelMonoid <| f i] : RightCancelMonoid (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := · * ·, npow := Monoidₓ.npow, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddCancelMonoid]
instance CancelMonoid [∀ i, CancelMonoid <| f i] : CancelMonoid (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := · * ·, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddCancelCommMonoid]
instance CancelCommMonoid [∀ i, CancelCommMonoid <| f i] : CancelCommMonoid (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := · * ·, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance MulZeroClass [∀ i, MulZeroClass <| f i] : MulZeroClass (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance MulZeroOneClass [∀ i, MulZeroOneClass <| f i] : MulZeroOneClass (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), one := (1 : ∀ i, f i), mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance MonoidWithZeroₓ [∀ i, MonoidWithZeroₓ <| f i] : MonoidWithZeroₓ (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), one := (1 : ∀ i, f i), mul := · * ·, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance CommMonoidWithZero [∀ i, CommMonoidWithZero <| f i] : CommMonoidWithZero (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), one := (1 : ∀ i, f i), mul := · * ·, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

end Pi

section MonoidHom

variable (f) [∀ i, MulOneClass (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `function.eval i` as a `monoid_hom`. -/
@[to_additive
      "Evaluation of functions into an indexed collection of additive monoids at a\npoint is an additive monoid homomorphism.\nThis is `function.eval i` as an `add_monoid_hom`.",
  simps]
def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i where
  toFun := fun g => g i
  map_one' := Pi.one_apply i
  map_mul' := fun x y => Pi.mul_apply _ _ i

/-- `function.const` as a `monoid_hom`. -/
@[to_additive "`function.const` as an `add_monoid_hom`.", simps]
def Pi.constMonoidHom (α β : Type _) [MulOneClass β] : β →* α → β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- Coercion of a `monoid_hom` into a function is itself a `monoid_hom`.

See also `monoid_hom.eval`. -/
@[to_additive
      "Coercion of an `add_monoid_hom` into a function is itself a `add_monoid_hom`.\n\nSee also `add_monoid_hom.eval`. ",
  simps]
def MonoidHom.coeFn (α β : Type _) [MulOneClass α] [CommMonoidₓ β] : (α →* β) →* α → β where
  toFun := fun g => g
  map_one' := rfl
  map_mul' := fun x y => rfl

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive
      "Additive monoid homomorphism between the function spaces `I → α` and `I → β`,\ninduced by an additive monoid homomorphism `f` between `α` and `β`",
  simps]
protected def MonoidHom.compLeft {α β : Type _} [MulOneClass α] [MulOneClass β] (f : α →* β) (I : Type _) :
    (I → α) →* I → β where
  toFun := fun h => f ∘ h
  map_one' := by
    ext <;> simp
  map_mul' := fun _ _ => by
    ext <;> simp

end MonoidHom

section Single

variable [DecidableEq I]

open Pi

variable (f)

/-- The zero-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `zero_hom` version of `pi.single`. -/
@[simps]
def ZeroHom.single [∀ i, Zero <| f i] (i : I) : ZeroHom (f i) (∀ i, f i) where
  toFun := single i
  map_zero' := single_zero i

/-- The additive monoid homomorphism including a single additive monoid
into a dependent family of additive monoids, as functions supported at a point.

This is the `add_monoid_hom` version of `pi.single`. -/
@[simps]
def AddMonoidHom.single [∀ i, AddZeroClass <| f i] (i : I) : f i →+ ∀ i, f i :=
  { ZeroHom.single f i with toFun := single i, map_add' := single_op₂ (fun _ => · + ·) (fun _ => zero_addₓ _) _ }

/-- The multiplicative homomorphism including a single `mul_zero_class`
into a dependent family of `mul_zero_class`es, as functions supported at a point.

This is the `mul_hom` version of `pi.single`. -/
@[simps]
def MulHom.single [∀ i, MulZeroClass <| f i] (i : I) : MulHom (f i) (∀ i, f i) where
  toFun := single i
  map_mul' := single_op₂ (fun _ => · * ·) (fun _ => zero_mul _) _

variable {f}

theorem Pi.single_add [∀ i, AddZeroClass <| f i] (i : I) (x y : f i) : single i (x + y) = single i x + single i y :=
  (AddMonoidHom.single f i).map_add x y

theorem Pi.single_neg [∀ i, AddGroupₓ <| f i] (i : I) (x : f i) : single i (-x) = -single i x :=
  (AddMonoidHom.single f i).map_neg x

theorem Pi.single_sub [∀ i, AddGroupₓ <| f i] (i : I) (x y : f i) : single i (x - y) = single i x - single i y :=
  (AddMonoidHom.single f i).map_sub x y

theorem Pi.single_mul [∀ i, MulZeroClass <| f i] (i : I) (x y : f i) : single i (x * y) = single i x * single i y :=
  (MulHom.single f i).map_mul x y

theorem Pi.update_eq_sub_add_single [∀ i, AddGroupₓ <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g - single i (g i) + single i x := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
    
  · simp [Function.update_noteq h.symm, h]
    

end Single

namespace Function

@[simp, to_additive]
theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : update (1 : ∀ i, f i) i 1 = 1 :=
  update_eq_self i 1

@[to_additive]
theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i) (x₂ : f i) :
    update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun i => · * ·) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]
theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun i => Inv.inv) f₁ i x₁ j).symm

@[to_additive]
theorem update_div [∀ i, Div (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i) (x₂ : f i) :
    update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun i => · / ·) f₁ f₂ i x₁ x₂ j).symm

end Function

section Piecewise

@[to_additive]
theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ _ _ _ _ fun _ => · * ·

@[to_additive]
theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹

@[to_additive]
theorem Set.piecewise_div [∀ i, Div (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ _ _ _ _ fun _ => · / ·

end Piecewise

section Extend

variable {ι : Type u} {η : Type v} (R : Type w) (s : ι → η)

/-- `function.extend s f 1` as a bundled hom. -/
@[to_additive Function.ExtendByZero.hom "`function.extend s f 0` as a bundled hom.", simps]
noncomputable def Function.ExtendByOne.hom [MulOneClass R] : (ι → R) →* η → R where
  toFun := fun f => Function.extendₓ s f 1
  map_one' := Function.extend_one s
  map_mul' := fun f g => by
    simpa using Function.extend_mul s f g 1 1

end Extend

