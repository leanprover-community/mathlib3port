/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.GroupWithZero.Units

/-!
# Additive and multiplicative equivalences associated to `multiplicative` and `additive`.
-/


variable {G H : Type _}

/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] : G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) where
  toFun f := ⟨f.toAddMonoidHom.toMultiplicative, f.symm.toAddMonoidHom.toMultiplicative, f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] : G ≃* H ≃ (Additive G ≃+ Additive H) where
  toFun f := ⟨f.toMonoidHom.toAdditive, f.symm.toMonoidHom.toAdditive, f.3, f.4, f.5⟩
  invFun f := ⟨f.toAddMonoidHom, f.symm.toAddMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] : Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f := ⟨f.toAddMonoidHom.toMultiplicative', f.symm.toAddMonoidHom.toMultiplicative'', f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
def MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] : G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm

/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] : G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f := ⟨f.toAddMonoidHom.toMultiplicative'', f.symm.toAddMonoidHom.toMultiplicative', f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
def MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] : Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm

section

variable (G) (H)

/-- `additive (multiplicative G)` is just `G`. -/
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditive'' (MulEquiv.refl (Multiplicative G))

/-- `multiplicative (additive H)` is just `H`. -/
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicative'' (AddEquiv.refl (Additive H))

end

