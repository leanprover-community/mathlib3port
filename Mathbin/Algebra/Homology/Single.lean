/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.single
! leanprover-community/mathlib commit 8eb9c42d4d34c77f6ee84ea766ae4070233a973c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Homology

/-!
# Chain complexes supported in a single degree

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `single V j c : V ⥤ homological_complex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

Similarly `single₀ V : V ⥤ chain_complex V ℕ` is the special case for
`ℕ`-indexed chain complexes, with the object supported in degree `0`,
but with better definitional properties.

In `to_single₀_equiv` we characterize chain maps to a `ℕ`-indexed complex concentrated in degree 0;
they are equivalent to `{ f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }`.
(This is useful translating between a projective resolution and
an augmented exact complex of projectives.)
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

namespace HomologicalComplex

variable {ι : Type _} [DecidableEq ι] (c : ComplexShape ι)

attribute [local instance] has_zero_object.has_zero

#print HomologicalComplex.single /-
/-- The functor `V ⥤ homological_complex V c` creating a chain complex supported in a single degree.

See also `chain_complex.single₀ : V ⥤ chain_complex V ℕ`,
which has better definitional properties,
if you are working with `ℕ`-indexed complexes.
-/
@[simps]
def single (j : ι) : V ⥤ HomologicalComplex V c
    where
  obj A :=
    { pt := fun i => if i = j then A else 0
      d := fun i j => 0 }
  map A B f :=
    {
      f := fun i =>
        if h : i = j then eqToHom (by dsimp; rw [if_pos h]) ≫ f ≫ eqToHom (by dsimp; rw [if_pos h])
        else 0 }
  map_id' A := by
    ext
    dsimp
    split_ifs with h
    · subst h; simp
    · rw [if_neg h]; simp
  map_comp' A B C f g := by
    ext
    dsimp
    split_ifs with h
    · subst h; simp
    · simp
#align homological_complex.single HomologicalComplex.single
-/

/-- The object in degree `j` of `(single V c h).obj A` is just `A`.
-/
@[simps]
def singleObjXSelf (j : ι) (A : V) : ((single V c j).obj A).pt j ≅ A :=
  eqToIso (by simp)
#align homological_complex.single_obj_X_self HomologicalComplex.singleObjXSelf

@[simp]
theorem single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
    ((single V c j).map f).f j = (singleObjXSelf V c j A).Hom ≫ f ≫ (singleObjXSelf V c j B).inv :=
  by simp; rfl
#align homological_complex.single_map_f_self HomologicalComplex.single_map_f_self

instance (j : ι) : Faithful (single V c j)
    where map_injective' X Y f g w := by
    have := congr_hom w j
    dsimp at this 
    simp only [dif_pos] at this 
    rw [← is_iso.inv_comp_eq, inv_eq_to_hom, eq_to_hom_trans_assoc, eq_to_hom_refl,
      category.id_comp, ← is_iso.comp_inv_eq, category.assoc, inv_eq_to_hom, eq_to_hom_trans,
      eq_to_hom_refl, category.comp_id] at this 
    exact this

instance (j : ι) : Full (single V c j)
    where
  preimage X Y f := eqToHom (by simp) ≫ f.f j ≫ eqToHom (by simp)
  witness' X Y f := by
    ext i
    dsimp
    split_ifs
    · subst h; simp
    · symm
      apply zero_of_target_iso_zero
      dsimp
      rw [if_neg h]

end HomologicalComplex

open HomologicalComplex

namespace ChainComplex

attribute [local instance] has_zero_object.has_zero

#print ChainComplex.single₀ /-
/-- `chain_complex.single₀ V` is the embedding of `V` into `chain_complex V ℕ`
as chain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ ChainComplex V ℕ
    where
  obj X :=
    { pt := fun n =>
        match n with
        | 0 => X
        | n + 1 => 0
      d := fun i j => 0 }
  map X Y f :=
    {
      f := fun n =>
        match n with
        | 0 => f
        | n + 1 => 0 }
  map_id' X := by ext n; cases n; rfl; dsimp; unfold_aux; simp
  map_comp' X Y Z f g := by ext n; cases n; rfl; dsimp; unfold_aux; simp
#align chain_complex.single₀ ChainComplex.single₀
-/

@[simp]
theorem single₀_obj_X_0 (X : V) : ((single₀ V).obj X).pt 0 = X :=
  rfl
#align chain_complex.single₀_obj_X_0 ChainComplex.single₀_obj_X_0

@[simp]
theorem single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).pt (n + 1) = 0 :=
  rfl
#align chain_complex.single₀_obj_X_succ ChainComplex.single₀_obj_X_succ

@[simp]
theorem single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 :=
  rfl
#align chain_complex.single₀_obj_X_d ChainComplex.single₀_obj_X_d

@[simp]
theorem single₀_obj_X_dTo (X : V) (j : ℕ) : ((single₀ V).obj X).dTo j = 0 := by
  rw [d_to_eq ((single₀ V).obj X) rfl]; simp
#align chain_complex.single₀_obj_X_d_to ChainComplex.single₀_obj_X_dTo

@[simp]
theorem single₀_obj_x_dFrom (X : V) (i : ℕ) : ((single₀ V).obj X).dFrom i = 0 :=
  by
  cases i
  · rw [d_from_eq_zero]; simp
  · rw [d_from_eq ((single₀ V).obj X) rfl]; simp
#align chain_complex.single₀_obj_X_d_from ChainComplex.single₀_obj_x_dFrom

@[simp]
theorem single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f :=
  rfl
#align chain_complex.single₀_map_f_0 ChainComplex.single₀_map_f_0

@[simp]
theorem single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) : ((single₀ V).map f).f (n + 1) = 0 :=
  rfl
#align chain_complex.single₀_map_f_succ ChainComplex.single₀_map_f_succ

section

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

#print ChainComplex.homologyFunctor0Single₀ /-
/-- Sending objects to chain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homologyFunctor0Single₀ : single₀ V ⋙ homologyFunctor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents (fun X => homology.congr _ _ (by simp) (by simp) ≪≫ homologyZeroZero)
    fun X Y f => by ext; dsimp [homologyFunctor]; simp
#align chain_complex.homology_functor_0_single₀ ChainComplex.homologyFunctor0Single₀
-/

#print ChainComplex.homologyFunctorSuccSingle₀ /-
/-- Sending objects to chain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homologyFunctorSuccSingle₀ (n : ℕ) :
    single₀ V ⋙ homologyFunctor V _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology.congr _ _ (by simp) (by simp) ≪≫
        homologyZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun X Y f => (functor.zero_obj _).eq_of_tgt _ _
#align chain_complex.homology_functor_succ_single₀ ChainComplex.homologyFunctorSuccSingle₀
-/

end

variable {V}

/-- Morphisms from a `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
@[simps]
def toSingle₀Equiv (C : ChainComplex V ℕ) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ { f : C.pt 0 ⟶ X // C.d 1 0 ≫ f = 0 }
    where
  toFun f := ⟨f.f 0, by rw [← f.comm 1 0]; simp⟩
  invFun f :=
    { f := fun i =>
        match i with
        | 0 => f.1
        | n + 1 => 0
      comm' := fun i j h =>
        by
        rcases i with (_ | _ | i) <;> cases j <;> unfold_aux <;>
          simp only [comp_zero, zero_comp, single₀_obj_X_d]
        · rw [C.shape, zero_comp]; simp
        · exact f.2.symm
        · rw [C.shape, zero_comp]; simp [i.succ_succ_ne_one.symm] }
  left_inv f := by
    ext i
    rcases i with ⟨⟩
    · rfl
    · ext
  right_inv := by tidy
#align chain_complex.to_single₀_equiv ChainComplex.toSingle₀Equiv

@[ext]
theorem to_single₀_ext {C : ChainComplex V ℕ} {X : V} (f g : C ⟶ (single₀ V).obj X)
    (h : f.f 0 = g.f 0) : f = g :=
  (toSingle₀Equiv C X).Injective (by ext; exact h)
#align chain_complex.to_single₀_ext ChainComplex.to_single₀_ext

/-- Morphisms from a single object chain complex with `X` concentrated in degree 0
to a `ℕ`-indexed chain complex `C` are the same as morphisms `f : X → C.X`.
-/
@[simps]
def fromSingle₀Equiv (C : ChainComplex V ℕ) (X : V) : ((single₀ V).obj X ⟶ C) ≃ (X ⟶ C.pt 0)
    where
  toFun f := f.f 0
  invFun f :=
    { f := fun i =>
        match i with
        | 0 => f
        | n + 1 => 0
      comm' := fun i j h => by
        cases i <;> cases j <;> unfold_aux <;>
          simp only [shape, ComplexShape.down_Rel, Nat.one_ne_zero, not_false_iff, comp_zero,
            zero_comp, Nat.succ_ne_zero, single₀_obj_X_d] }
  left_inv f := by
    ext i
    cases i
    · rfl
    · ext
  right_inv g := rfl
#align chain_complex.from_single₀_equiv ChainComplex.fromSingle₀Equiv

variable (V)

/-- `single₀` is the same as `single V _ 0`. -/
def single₀IsoSingle : single₀ V ≅ single V _ 0 :=
  NatIso.ofComponents
    (fun X =>
      { Hom := { f := fun i => by cases i <;> simpa using 𝟙 _ }
        inv := { f := fun i => by cases i <;> simpa using 𝟙 _ }
        hom_inv_id' := by ext (_ | i) <;> · dsimp; simp
        inv_hom_id' := by
          ext (_ | i)
          · apply category.id_comp
          · apply has_zero_object.to_zero_ext })
    fun X Y f => by ext (_ | i) <;> · dsimp; simp
#align chain_complex.single₀_iso_single ChainComplex.single₀IsoSingle

instance : Faithful (single₀ V) :=
  Faithful.of_iso (single₀IsoSingle V).symm

instance : Full (single₀ V) :=
  Full.ofIso (single₀IsoSingle V).symm

end ChainComplex

namespace CochainComplex

attribute [local instance] has_zero_object.has_zero

#print CochainComplex.single₀ /-
/-- `cochain_complex.single₀ V` is the embedding of `V` into `cochain_complex V ℕ`
as cochain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ CochainComplex V ℕ
    where
  obj X :=
    { pt := fun n =>
        match n with
        | 0 => X
        | n + 1 => 0
      d := fun i j => 0 }
  map X Y f :=
    {
      f := fun n =>
        match n with
        | 0 => f
        | n + 1 => 0 }
  map_id' X := by ext n; cases n; rfl; dsimp; unfold_aux; simp
  map_comp' X Y Z f g := by ext n; cases n; rfl; dsimp; unfold_aux; simp
#align cochain_complex.single₀ CochainComplex.single₀
-/

@[simp]
theorem single₀_obj_X_0 (X : V) : ((single₀ V).obj X).pt 0 = X :=
  rfl
#align cochain_complex.single₀_obj_X_0 CochainComplex.single₀_obj_X_0

@[simp]
theorem single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).pt (n + 1) = 0 :=
  rfl
#align cochain_complex.single₀_obj_X_succ CochainComplex.single₀_obj_X_succ

@[simp]
theorem single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 :=
  rfl
#align cochain_complex.single₀_obj_X_d CochainComplex.single₀_obj_X_d

@[simp]
theorem single₀_obj_x_dFrom (X : V) (j : ℕ) : ((single₀ V).obj X).dFrom j = 0 := by
  rw [d_from_eq ((single₀ V).obj X) rfl]; simp
#align cochain_complex.single₀_obj_X_d_from CochainComplex.single₀_obj_x_dFrom

@[simp]
theorem single₀_obj_x_dTo (X : V) (i : ℕ) : ((single₀ V).obj X).dTo i = 0 :=
  by
  cases i
  · rw [d_to_eq_zero]; simp
  · rw [d_to_eq ((single₀ V).obj X) rfl]; simp
#align cochain_complex.single₀_obj_X_d_to CochainComplex.single₀_obj_x_dTo

@[simp]
theorem single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f :=
  rfl
#align cochain_complex.single₀_map_f_0 CochainComplex.single₀_map_f_0

@[simp]
theorem single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) : ((single₀ V).map f).f (n + 1) = 0 :=
  rfl
#align cochain_complex.single₀_map_f_succ CochainComplex.single₀_map_f_succ

section

variable [HasEqualizers V] [HasCokernels V] [HasImages V] [HasImageMaps V]

#print CochainComplex.homologyFunctor0Single₀ /-
/-- Sending objects to cochain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homologyFunctor0Single₀ : single₀ V ⋙ homologyFunctor V _ 0 ≅ 𝟭 V :=
  NatIso.ofComponents (fun X => homology.congr _ _ (by simp) (by simp) ≪≫ homologyZeroZero)
    fun X Y f => by ext; dsimp [homologyFunctor]; simp
#align cochain_complex.homology_functor_0_single₀ CochainComplex.homologyFunctor0Single₀
-/

#print CochainComplex.homologyFunctorSuccSingle₀ /-
/-- Sending objects to cochain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homologyFunctorSuccSingle₀ (n : ℕ) :
    single₀ V ⋙ homologyFunctor V _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology.congr _ _ (by simp) (by simp) ≪≫
        homologyZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun X Y f => (functor.zero_obj _).eq_of_tgt _ _
#align cochain_complex.homology_functor_succ_single₀ CochainComplex.homologyFunctorSuccSingle₀
-/

end

variable {V}

/-- Morphisms from a single object cochain complex with `X` concentrated in degree 0
to a `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`.
-/
def fromSingle₀Equiv (C : CochainComplex V ℕ) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ { f : X ⟶ C.pt 0 // f ≫ C.d 0 1 = 0 }
    where
  toFun f := ⟨f.f 0, by rw [f.comm 0 1]; simp⟩
  invFun f :=
    { f := fun i =>
        match i with
        | 0 => f.1
        | n + 1 => 0
      comm' := fun i j h =>
        by
        rcases j with (_ | _ | j) <;> cases i <;> unfold_aux <;>
          simp only [comp_zero, zero_comp, single₀_obj_X_d]
        · convert comp_zero; rw [C.shape]; simp
        · exact f.2
        · convert comp_zero; rw [C.shape]; simp only [ComplexShape.up_Rel, zero_add]
          exact (Nat.one_lt_succ_succ j).Ne }
  left_inv f := by
    ext i
    rcases i with ⟨⟩
    · rfl
    · ext
  right_inv := by tidy
#align cochain_complex.from_single₀_equiv CochainComplex.fromSingle₀Equiv

variable (V)

/-- `single₀` is the same as `single V _ 0`. -/
def single₀IsoSingle : single₀ V ≅ single V _ 0 :=
  NatIso.ofComponents
    (fun X =>
      { Hom := { f := fun i => by cases i <;> simpa using 𝟙 _ }
        inv := { f := fun i => by cases i <;> simpa using 𝟙 _ }
        hom_inv_id' := by ext (_ | i) <;> · dsimp; simp
        inv_hom_id' := by
          ext (_ | i)
          · apply category.id_comp
          · apply has_zero_object.to_zero_ext })
    fun X Y f => by ext (_ | i) <;> · dsimp; simp
#align cochain_complex.single₀_iso_single CochainComplex.single₀IsoSingle

instance : Faithful (single₀ V) :=
  Faithful.of_iso (single₀IsoSingle V).symm

instance : Full (single₀ V) :=
  Full.ofIso (single₀IsoSingle V).symm

end CochainComplex

