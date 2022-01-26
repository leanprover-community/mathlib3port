import Mathbin.Tactic.PiInstances
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Ring.Basic

/-!
# Pi instances for ring

This file defines instances for ring, semiring and related structures on Pi Types
-/


namespace Pi

universe u v w

variable {I : Type u}

variable {f : I → Type v}

variable (x y : ∀ i, f i) (i : I)

instance Distrib [∀ i, Distrib <| f i] : Distrib (∀ i : I, f i) := by
  refine_struct { add := · + ·, mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonUnitalNonAssocSemiring [∀ i, NonUnitalNonAssocSemiring <| f i] : NonUnitalNonAssocSemiring (∀ i : I, f i) :=
  by
  refine_struct { zero := (0 : ∀ i, f i), add := · + ·, mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonUnitalSemiring [∀ i, NonUnitalSemiring <| f i] : NonUnitalSemiring (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), add := · + ·, mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonAssocSemiring [∀ i, NonAssocSemiring <| f i] : NonAssocSemiring (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), one := 1, add := · + ·, mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance Semiringₓ [∀ i, Semiringₓ <| f i] : Semiringₓ (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), one := 1, add := · + ·, mul := · * ·, nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance CommSemiringₓ [∀ i, CommSemiringₓ <| f i] : CommSemiringₓ (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), one := 1, add := · + ·, mul := · * ·, nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonUnitalNonAssocRing [∀ i, NonUnitalNonAssocRing <| f i] : NonUnitalNonAssocRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), add := · + ·, mul := · * ·, neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance Ringₓ [∀ i, Ringₓ <| f i] : Ringₓ (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), one := 1, add := · + ·, mul := · * ·, neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance CommRingₓ [∀ i, CommRingₓ <| f i] : CommRingₓ (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i), one := 1, add := · + ·, mul := · * ·, neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`pi.ring_hom f : γ →+* Π a, β a` given by `pi.ring_hom f x b = f b x`. -/
@[simps]
protected def RingHom {γ : Type w} [∀ i, NonAssocSemiring (f i)] [NonAssocSemiring γ] (g : ∀ i, γ →+* f i) :
    γ →+* ∀ i, f i where
  toFun := fun x b => g b x
  map_add' := fun x y => funext fun z => (g z).map_add x y
  map_mul' := fun x y => funext fun z => (g z).map_mul x y
  map_one' := funext fun z => (g z).map_one
  map_zero' := funext fun z => (g z).map_zero

theorem ring_hom_injective {γ : Type w} [Nonempty I] [∀ i, NonAssocSemiring (f i)] [NonAssocSemiring γ]
    (g : ∀ i, γ →+* f i) (hg : ∀ i, Function.Injective (g i)) : Function.Injective (Pi.ringHom g) := fun x y h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((Function.funext_iffₓ.mp h : _) i)

end Pi

section RingHom

universe u v

variable {I : Type u}

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism. This is `function.eval` as a `ring_hom`. -/
@[simps]
def Pi.evalRingHom (f : I → Type v) [∀ i, NonAssocSemiring (f i)] (i : I) : (∀ i, f i) →+* f i :=
  { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }

/-- `function.const` as a `ring_hom`. -/
@[simps]
def Pi.constRingHom (α β : Type _) [NonAssocSemiring β] : β →+* α → β :=
  { Pi.ringHom fun _ => RingHom.id β with toFun := Function.const _ }

/-- Ring homomorphism between the function spaces `I → α` and `I → β`, induced by a ring
homomorphism `f` between `α` and `β`. -/
@[simps]
protected def RingHom.compLeft {α β : Type _} [NonAssocSemiring α] [NonAssocSemiring β] (f : α →+* β) (I : Type _) :
    (I → α) →+* I → β :=
  { f.to_monoid_hom.comp_left I, f.to_add_monoid_hom.comp_left I with toFun := fun h => f ∘ h }

end RingHom

