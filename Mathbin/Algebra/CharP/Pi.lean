/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.char_p.pi
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.Algebra.Ring.Pi

/-!
# Characteristic of semirings of functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v

namespace CharP

#print CharP.pi /-
instance pi (ι : Type u) [hi : Nonempty ι] (R : Type v) [Semiring R] (p : ℕ) [CharP R p] :
    CharP (ι → R) p :=
  ⟨fun x =>
    let ⟨i⟩ := hi
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          funext fun j =>
            show Pi.evalRingHom (fun _ => R) j (↑x : ι → R) = 0 by rw [map_natCast, h],
          fun h => map_natCast (Pi.evalRingHom (fun _ : ι => R) i) x ▸ by rw [h, RingHom.map_zero]⟩⟩
#align char_p.pi CharP.pi
-/

/- warning: char_p.pi' -> CharP.pi' is a dubious translation:
lean 3 declaration is
  forall (ι : Type.{u1}) [hi : Nonempty.{succ u1} ι] (R : Type.{u2}) [_inst_1 : CommRing.{u2} R] (p : Nat) [_inst_2 : CharP.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_1)))) p], CharP.{max u1 u2} (ι -> R) (Pi.addMonoidWithOne.{u1, u2} ι (fun (ᾰ : ι) => R) (fun (a : ι) => AddGroupWithOne.toAddMonoidWithOne.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_1))))) p
but is expected to have type
  forall (ι : Type.{u1}) [hi : Nonempty.{succ u1} ι] (R : Type.{u2}) [_inst_1 : CommRing.{u2} R] (p : Nat) [_inst_2 : CharP.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R (CommRing.toRing.{u2} R _inst_1))) p], CharP.{max u1 u2} (ι -> R) (Pi.addMonoidWithOne.{u1, u2} ι (fun (ᾰ : ι) => R) (fun (a : ι) => AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R (CommRing.toRing.{u2} R _inst_1)))) p
Case conversion may be inaccurate. Consider using '#align char_p.pi' CharP.pi'ₓ'. -/
-- diamonds
instance pi' (ι : Type u) [hi : Nonempty ι] (R : Type v) [CommRing R] (p : ℕ) [CharP R p] :
    CharP (ι → R) p :=
  CharP.pi ι R p
#align char_p.pi' CharP.pi'

end CharP

