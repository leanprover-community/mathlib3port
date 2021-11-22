import Mathbin.Data.Equiv.MulAddAut 
import Mathbin.Data.Equiv.Ring

/-!
# Ring automorphisms

This file defines the automorphism group structure on `ring_aut R := ring_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/ring` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

ring_aut
-/


/-- The group of ring automorphisms. -/
@[reducible]
def RingAut (R : Type _) [Mul R] [Add R] :=
  RingEquiv R R

namespace RingAut

variable(R : Type _)[Mul R][Add R]

/--
The group operation on automorphisms of a ring is defined by
`λ g h, ring_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance  : Groupₓ (RingAut R) :=
  by 
    refineStruct
        { mul := fun g h => RingEquiv.trans h g, one := RingEquiv.refl R, inv := RingEquiv.symm, div := _,
          npow := @npowRec _ ⟨RingEquiv.refl R⟩ ⟨fun g h => RingEquiv.trans h g⟩,
          zpow := @zpowRec _ ⟨RingEquiv.refl R⟩ ⟨fun g h => RingEquiv.trans h g⟩ ⟨RingEquiv.symm⟩ } <;>
      intros  <;>
        ext <;>
          try 
              rfl <;>
            apply Equiv.left_inv

instance  : Inhabited (RingAut R) :=
  ⟨1⟩

/-- Monoid homomorphism from ring automorphisms to additive automorphisms. -/
def to_add_aut : RingAut R →* AddAut R :=
  by 
    refineStruct { toFun := RingEquiv.toAddEquiv } <;> intros  <;> rfl

/-- Monoid homomorphism from ring automorphisms to multiplicative automorphisms. -/
def to_mul_aut : RingAut R →* MulAut R :=
  by 
    refineStruct { toFun := RingEquiv.toMulEquiv } <;> intros  <;> rfl

/-- Monoid homomorphism from ring automorphisms to permutations. -/
def to_perm : RingAut R →* Equiv.Perm R :=
  by 
    refineStruct { toFun := RingEquiv.toEquiv } <;> intros  <;> rfl

end RingAut

