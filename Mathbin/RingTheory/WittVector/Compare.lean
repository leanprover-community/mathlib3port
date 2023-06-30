/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis

! This file was ported from Lean 3 source module ring_theory.witt_vector.compare
! leanprover-community/mathlib commit 9240e8be927a0955b9a82c6c85ef499ee3a626b8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.WittVector.Truncated
import Mathbin.RingTheory.WittVector.Identities
import Mathbin.NumberTheory.Padics.RingHoms

/-!

# Comparison isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct a ring isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`.
This isomorphism follows from the fact that both satisfy the universal property
of the inverse limit of `zmod (p^n)`.

## Main declarations

* `witt_vector.to_zmod_pow`: a family of compatible ring homs `𝕎 (zmod p) → zmod (p^k)`
* `witt_vector.equiv`: the isomorphism

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

namespace TruncatedWittVector

variable (p) (n : ℕ) (R : Type _) [CommRing R]

#print TruncatedWittVector.eq_of_le_of_cast_pow_eq_zero /-
theorem eq_of_le_of_cast_pow_eq_zero [CharP R p] (i : ℕ) (hin : i ≤ n)
    (hpi : (p ^ i : TruncatedWittVector p n R) = 0) : i = n :=
  by
  contrapose! hpi
  replace hin := lt_of_le_of_ne hin hpi; clear hpi
  have : (↑p ^ i : TruncatedWittVector p n R) = WittVector.truncate n (↑p ^ i) := by
    rw [RingHom.map_pow, map_natCast]
  rw [this, ext_iff, not_forall]; clear this
  use ⟨i, hin⟩
  rw [WittVector.coeff_truncate, coeff_zero, Fin.val_mk, WittVector.coeff_p_pow]
  haveI : Nontrivial R := CharP.nontrivial_of_char_ne_one hp.1.ne_one
  exact one_ne_zero
#align truncated_witt_vector.eq_of_le_of_cast_pow_eq_zero TruncatedWittVector.eq_of_le_of_cast_pow_eq_zero
-/

section Iso

variable (p n) {R}

#print TruncatedWittVector.card_zMod /-
theorem card_zMod : Fintype.card (TruncatedWittVector p n (ZMod p)) = p ^ n := by
  rw [card, ZMod.card]
#align truncated_witt_vector.card_zmod TruncatedWittVector.card_zMod
-/

#print TruncatedWittVector.charP_zMod /-
theorem charP_zMod : CharP (TruncatedWittVector p n (ZMod p)) (p ^ n) :=
  charP_of_prime_pow_injective _ _ _ (card_zMod _ _) (eq_of_le_of_cast_pow_eq_zero p n (ZMod p))
#align truncated_witt_vector.char_p_zmod TruncatedWittVector.charP_zMod
-/

attribute [local instance] char_p_zmod

#print TruncatedWittVector.zmodEquivTrunc /-
/-- The unique isomorphism between `zmod p^n` and `truncated_witt_vector p n (zmod p)`.

This isomorphism exists, because `truncated_witt_vector p n (zmod p)` is a finite ring
with characteristic and cardinality `p^n`.
-/
def zmodEquivTrunc : ZMod (p ^ n) ≃+* TruncatedWittVector p n (ZMod p) :=
  ZMod.ringEquiv (TruncatedWittVector p n (ZMod p)) (card_zMod _ _)
#align truncated_witt_vector.zmod_equiv_trunc TruncatedWittVector.zmodEquivTrunc
-/

#print TruncatedWittVector.zmodEquivTrunc_apply /-
theorem zmodEquivTrunc_apply {x : ZMod (p ^ n)} :
    zmodEquivTrunc p n x = ZMod.castHom (by rfl) (TruncatedWittVector p n (ZMod p)) x :=
  rfl
#align truncated_witt_vector.zmod_equiv_trunc_apply TruncatedWittVector.zmodEquivTrunc_apply
-/

#print TruncatedWittVector.commutes /-
/-- The following diagram commutes:
```text
          zmod (p^n) ----------------------------> zmod (p^m)
            |                                        |
            |                                        |
            v                                        v
truncated_witt_vector p n (zmod p) ----> truncated_witt_vector p m (zmod p)
```
Here the vertical arrows are `truncated_witt_vector.zmod_equiv_trunc`,
the horizontal arrow at the top is `zmod.cast_hom`,
and the horizontal arrow at the bottom is `truncated_witt_vector.truncate`.
-/
theorem commutes {m : ℕ} (hm : n ≤ m) :
    (truncate hm).comp (zmodEquivTrunc p m).toRingHom =
      (zmodEquivTrunc p n).toRingHom.comp (ZMod.castHom (pow_dvd_pow p hm) _) :=
  RingHom.ext_zmod _ _
#align truncated_witt_vector.commutes TruncatedWittVector.commutes
-/

#print TruncatedWittVector.commutes' /-
theorem commutes' {m : ℕ} (hm : n ≤ m) (x : ZMod (p ^ m)) :
    truncate hm (zmodEquivTrunc p m x) = zmodEquivTrunc p n (ZMod.castHom (pow_dvd_pow p hm) _ x) :=
  show (truncate hm).comp (zmodEquivTrunc p m).toRingHom x = _ by rw [commutes _ _ hm] <;> rfl
#align truncated_witt_vector.commutes' TruncatedWittVector.commutes'
-/

#print TruncatedWittVector.commutes_symm' /-
theorem commutes_symm' {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m (ZMod p)) :
    (zmodEquivTrunc p n).symm (truncate hm x) =
      ZMod.castHom (pow_dvd_pow p hm) _ ((zmodEquivTrunc p m).symm x) :=
  by
  apply (zmod_equiv_trunc p n).Injective
  rw [← commutes']
  simp
#align truncated_witt_vector.commutes_symm' TruncatedWittVector.commutes_symm'
-/

#print TruncatedWittVector.commutes_symm /-
/-- The following diagram commutes:
```text
truncated_witt_vector p n (zmod p) ----> truncated_witt_vector p m (zmod p)
            |                                        |
            |                                        |
            v                                        v
          zmod (p^n) ----------------------------> zmod (p^m)
```
Here the vertical arrows are `(truncated_witt_vector.zmod_equiv_trunc p _).symm`,
the horizontal arrow at the top is `zmod.cast_hom`,
and the horizontal arrow at the bottom is `truncated_witt_vector.truncate`.
-/
theorem commutes_symm {m : ℕ} (hm : n ≤ m) :
    (zmodEquivTrunc p n).symm.toRingHom.comp (truncate hm) =
      (ZMod.castHom (pow_dvd_pow p hm) _).comp (zmodEquivTrunc p m).symm.toRingHom :=
  by ext <;> apply commutes_symm'
#align truncated_witt_vector.commutes_symm TruncatedWittVector.commutes_symm
-/

end Iso

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (p)

#print WittVector.toZmodPow /-
/-- `to_zmod_pow` is a family of compatible ring homs. We get this family by composing
`truncated_witt_vector.zmod_equiv_trunc` (in right-to-left direction)
with `witt_vector.truncate`.
-/
def toZmodPow (k : ℕ) : 𝕎 (ZMod p) →+* ZMod (p ^ k) :=
  (zmodEquivTrunc p k).symm.toRingHom.comp (truncate k)
#align witt_vector.to_zmod_pow WittVector.toZmodPow
-/

#print WittVector.toZmodPow_compat /-
theorem toZmodPow_compat (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (toZmodPow p n) = toZmodPow p m :=
  calc
    (ZMod.castHom _ (ZMod (p ^ m))).comp ((zmodEquivTrunc p n).symm.toRingHom.comp (truncate n)) =
        ((zmodEquivTrunc p m).symm.toRingHom.comp (TruncatedWittVector.truncate h)).comp
          (truncate n) :=
      by rw [commutes_symm, RingHom.comp_assoc]
    _ = (zmodEquivTrunc p m).symm.toRingHom.comp (truncate m) := by
      rw [RingHom.comp_assoc, truncate_comp_witt_vector_truncate]
#align witt_vector.to_zmod_pow_compat WittVector.toZmodPow_compat
-/

#print WittVector.toPadicInt /-
/-- `to_padic_int` lifts `to_zmod_pow : 𝕎 (zmod p) →+* zmod (p ^ k)` to a ring hom to `ℤ_[p]`
using `padic_int.lift`, the universal property of `ℤ_[p]`.
-/
def toPadicInt : 𝕎 (ZMod p) →+* ℤ_[p] :=
  PadicInt.lift <| toZmodPow_compat p
#align witt_vector.to_padic_int WittVector.toPadicInt
-/

#print WittVector.zmodEquivTrunc_compat /-
theorem zmodEquivTrunc_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (TruncatedWittVector.truncate hk).comp
        ((zmodEquivTrunc p k₂).toRingHom.comp (PadicInt.toZModPow k₂)) =
      (zmodEquivTrunc p k₁).toRingHom.comp (PadicInt.toZModPow k₁) :=
  by rw [← RingHom.comp_assoc, commutes, RingHom.comp_assoc, PadicInt.zmod_cast_comp_toZModPow]
#align witt_vector.zmod_equiv_trunc_compat WittVector.zmodEquivTrunc_compat
-/

#print WittVector.fromPadicInt /-
/-- `from_padic_int` uses `witt_vector.lift` to lift `truncated_witt_vector.zmod_equiv_trunc`
composed with `padic_int.to_zmod_pow` to a ring hom `ℤ_[p] →+* 𝕎 (zmod p)`.
-/
def fromPadicInt : ℤ_[p] →+* 𝕎 (ZMod p) :=
  (WittVector.lift fun k => (zmodEquivTrunc p k).toRingHom.comp (PadicInt.toZModPow k)) <|
    zmodEquivTrunc_compat _
#align witt_vector.from_padic_int WittVector.fromPadicInt
-/

#print WittVector.toPadicInt_comp_fromPadicInt /-
theorem toPadicInt_comp_fromPadicInt : (toPadicInt p).comp (fromPadicInt p) = RingHom.id ℤ_[p] :=
  by
  rw [← PadicInt.toZModPow_eq_iff_ext]
  intro n
  rw [← RingHom.comp_assoc, to_padic_int, PadicInt.lift_spec]
  simp only [from_padic_int, to_zmod_pow, RingHom.comp_id]
  rw [RingHom.comp_assoc, truncate_comp_lift, ← RingHom.comp_assoc]
  simp only [RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]
#align witt_vector.to_padic_int_comp_from_padic_int WittVector.toPadicInt_comp_fromPadicInt
-/

#print WittVector.toPadicInt_comp_fromPadicInt_ext /-
theorem toPadicInt_comp_fromPadicInt_ext (x) :
    (toPadicInt p).comp (fromPadicInt p) x = RingHom.id ℤ_[p] x := by
  rw [to_padic_int_comp_from_padic_int]
#align witt_vector.to_padic_int_comp_from_padic_int_ext WittVector.toPadicInt_comp_fromPadicInt_ext
-/

#print WittVector.fromPadicInt_comp_toPadicInt /-
theorem fromPadicInt_comp_toPadicInt :
    (fromPadicInt p).comp (toPadicInt p) = RingHom.id (𝕎 (ZMod p)) :=
  by
  apply WittVector.hom_ext
  intro n
  rw [from_padic_int, ← RingHom.comp_assoc, truncate_comp_lift, RingHom.comp_assoc]
  simp only [to_padic_int, to_zmod_pow, RingHom.comp_id, PadicInt.lift_spec, RingHom.id_comp, ←
    RingHom.comp_assoc, RingEquiv.toRingHom_comp_symm_toRingHom]
#align witt_vector.from_padic_int_comp_to_padic_int WittVector.fromPadicInt_comp_toPadicInt
-/

#print WittVector.fromPadicInt_comp_toPadicInt_ext /-
theorem fromPadicInt_comp_toPadicInt_ext (x) :
    (fromPadicInt p).comp (toPadicInt p) x = RingHom.id (𝕎 (ZMod p)) x := by
  rw [from_padic_int_comp_to_padic_int]
#align witt_vector.from_padic_int_comp_to_padic_int_ext WittVector.fromPadicInt_comp_toPadicInt_ext
-/

#print WittVector.equiv /-
/-- The ring of Witt vectors over `zmod p` is isomorphic to the ring of `p`-adic integers. This
equivalence is witnessed by `witt_vector.to_padic_int` with inverse `witt_vector.from_padic_int`.
-/
def equiv : 𝕎 (ZMod p) ≃+* ℤ_[p] where
  toFun := toPadicInt p
  invFun := fromPadicInt p
  left_inv := fromPadicInt_comp_toPadicInt_ext _
  right_inv := toPadicInt_comp_fromPadicInt_ext _
  map_mul' := RingHom.map_mul _
  map_add' := RingHom.map_add _
#align witt_vector.equiv WittVector.equiv
-/

end WittVector

