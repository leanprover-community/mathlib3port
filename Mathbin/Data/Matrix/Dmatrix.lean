/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.matrix.dmatrix
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.Data.Fintype.Basic

/-!
# Matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u u' v w z

#print DMatrix /-
/-- `dmatrix m n` is the type of dependently typed matrices
whose rows are indexed by the fintype `m` and
whose columns are indexed by the fintype `n`. -/
@[nolint unused_arguments]
def DMatrix (m : Type u) (n : Type u') [Fintype m] [Fintype n] (α : m → n → Type v) :
    Type max u u' v :=
  ∀ i j, α i j
#align dmatrix DMatrix
-/

variable {l m n o : Type _} [Fintype l] [Fintype m] [Fintype n] [Fintype o]

variable {α : m → n → Type v}

namespace DMatrix

section Ext

variable {M N : DMatrix m n α}

/- warning: dmatrix.ext_iff -> DMatrix.ext_iff is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u3} n] {α : m -> n -> Type.{u1}} {M : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α} {N : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α}, Iff (forall (i : m) (j : n), Eq.{succ u1} (α i j) (M i j) (N i j)) (Eq.{succ (max u2 u3 u1)} (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) M N)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} {M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α} {N : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α}, Iff (forall (i : m) (j : n), Eq.{succ u3} (α i j) (M i j) (N i j)) (Eq.{max (max (succ u3) (succ u2)) (succ u1)} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) M N)
Case conversion may be inaccurate. Consider using '#align dmatrix.ext_iff DMatrix.ext_iffₓ'. -/
theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩
#align dmatrix.ext_iff DMatrix.ext_iff

/- warning: dmatrix.ext -> DMatrix.ext is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u3} n] {α : m -> n -> Type.{u1}} {M : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α} {N : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α}, (forall (i : m) (j : n), Eq.{succ u1} (α i j) (M i j) (N i j)) -> (Eq.{succ (max u2 u3 u1)} (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) M N)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} {M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α} {N : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α}, (forall (i : m) (j : n), Eq.{succ u3} (α i j) (M i j) (N i j)) -> (Eq.{max (max (succ u3) (succ u2)) (succ u1)} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) M N)
Case conversion may be inaccurate. Consider using '#align dmatrix.ext DMatrix.extₓ'. -/
@[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp
#align dmatrix.ext DMatrix.ext

end Ext

#print DMatrix.map /-
/-- `M.map f` is the dmatrix obtained by applying `f` to each entry of the matrix `M`. -/
def map (M : DMatrix m n α) {β : m → n → Type w} (f : ∀ ⦃i j⦄, α i j → β i j) : DMatrix m n β :=
  fun i j => f (M i j)
#align dmatrix.map DMatrix.map
-/

/- warning: dmatrix.map_apply -> DMatrix.map_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} [_inst_2 : Fintype.{u3} m] [_inst_3 : Fintype.{u4} n] {α : m -> n -> Type.{u1}} {M : DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α} {β : m -> n -> Type.{u2}} {f : forall {{i : m}} {{j : n}}, (α i j) -> (β i j)} {i : m} {j : n}, Eq.{succ u2} (β i j) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) f i j) (f i j (M i j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} {M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α} {β : m -> n -> Type.{u4}} {f : forall {{i : m}} {{j : n}}, (α i j) -> (β i j)} {i : m} {j : n}, Eq.{succ u4} (β i j) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) f i j) (f i j (M i j))
Case conversion may be inaccurate. Consider using '#align dmatrix.map_apply DMatrix.map_applyₓ'. -/
@[simp]
theorem map_apply {M : DMatrix m n α} {β : m → n → Type w} {f : ∀ ⦃i j⦄, α i j → β i j} {i : m}
    {j : n} : M.map f i j = f (M i j) :=
  rfl
#align dmatrix.map_apply DMatrix.map_apply

/- warning: dmatrix.map_map -> DMatrix.map_map is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u4}} {n : Type.{u5}} [_inst_2 : Fintype.{u4} m] [_inst_3 : Fintype.{u5} n] {α : m -> n -> Type.{u1}} {M : DMatrix.{u4, u5, u1} m n _inst_2 _inst_3 α} {β : m -> n -> Type.{u2}} {γ : m -> n -> Type.{u3}} {f : forall {{i : m}} {{j : n}}, (α i j) -> (β i j)} {g : forall {{i : m}} {{j : n}}, (β i j) -> (γ i j)}, Eq.{succ (max u4 u5 u3)} (DMatrix.{u4, u5, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => γ i j)) (DMatrix.map.{u2, u3, u4, u5} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (DMatrix.map.{u1, u2, u4, u5} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) f) (fun (i : m) (j : n) => γ i j) g) (DMatrix.map.{u1, u3, u4, u5} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => γ i j) (fun (i : m) (j : n) (x : α i j) => g i j (f i j x)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} {M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α} {β : m -> n -> Type.{u4}} {γ : m -> n -> Type.{u5}} {f : forall {{i : m}} {{j : n}}, (α i j) -> (β i j)} {g : forall {{i : m}} {{j : n}}, (β i j) -> (γ i j)}, Eq.{max (max (succ u5) (succ u2)) (succ u1)} (DMatrix.{u2, u1, u5} m n _inst_2 _inst_3 (fun (i : m) (j : n) => γ i j)) (DMatrix.map.{u4, u5, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) f) (fun (i : m) (j : n) => γ i j) g) (DMatrix.map.{u3, u5, u2, u1} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => γ i j) (fun (i : m) (j : n) (x : α i j) => g i j (f i j x)))
Case conversion may be inaccurate. Consider using '#align dmatrix.map_map DMatrix.map_mapₓ'. -/
@[simp]
theorem map_map {M : DMatrix m n α} {β : m → n → Type w} {γ : m → n → Type z}
    {f : ∀ ⦃i j⦄, α i j → β i j} {g : ∀ ⦃i j⦄, β i j → γ i j} :
    (M.map f).map g = M.map fun i j x => g (f x) :=
  by
  ext
  simp
#align dmatrix.map_map DMatrix.map_map

#print DMatrix.transpose /-
/-- The transpose of a dmatrix. -/
def transpose (M : DMatrix m n α) : DMatrix n m fun j i => α i j
  | x, y => M y x
#align dmatrix.transpose DMatrix.transpose
-/

-- mathport name: dmatrix.transpose
scoped postfix:1024 "ᵀ" => DMatrix.transpose

#print DMatrix.col /-
/-- `dmatrix.col u` is the column matrix whose entries are given by `u`. -/
def col {α : m → Type v} (w : ∀ i, α i) : DMatrix m Unit fun i j => α i
  | x, y => w x
#align dmatrix.col DMatrix.col
-/

#print DMatrix.row /-
/-- `dmatrix.row u` is the row matrix whose entries are given by `u`. -/
def row {α : n → Type v} (v : ∀ j, α j) : DMatrix Unit n fun i j => α j
  | x, y => v y
#align dmatrix.row DMatrix.row
-/

instance [∀ i j, Inhabited (α i j)] : Inhabited (DMatrix m n α) :=
  Pi.inhabited _

instance [∀ i j, Add (α i j)] : Add (DMatrix m n α) :=
  Pi.instAdd

instance [∀ i j, AddSemigroup (α i j)] : AddSemigroup (DMatrix m n α) :=
  Pi.addSemigroup

instance [∀ i j, AddCommSemigroup (α i j)] : AddCommSemigroup (DMatrix m n α) :=
  Pi.addCommSemigroup

instance [∀ i j, Zero (α i j)] : Zero (DMatrix m n α) :=
  Pi.instZero

instance [∀ i j, AddMonoid (α i j)] : AddMonoid (DMatrix m n α) :=
  Pi.addMonoid

instance [∀ i j, AddCommMonoid (α i j)] : AddCommMonoid (DMatrix m n α) :=
  Pi.addCommMonoid

instance [∀ i j, Neg (α i j)] : Neg (DMatrix m n α) :=
  Pi.instNeg

instance [∀ i j, Sub (α i j)] : Sub (DMatrix m n α) :=
  Pi.instSub

instance [∀ i j, AddGroup (α i j)] : AddGroup (DMatrix m n α) :=
  Pi.addGroup

instance [∀ i j, AddCommGroup (α i j)] : AddCommGroup (DMatrix m n α) :=
  Pi.addCommGroup

instance [∀ i j, Unique (α i j)] : Unique (DMatrix m n α) :=
  Pi.unique

instance [∀ i j, Subsingleton (α i j)] : Subsingleton (DMatrix m n α) :=
  Pi.subsingleton

/- warning: dmatrix.zero_apply -> DMatrix.zero_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u3} n] {α : m -> n -> Type.{u1}} [_inst_5 : forall (i : m) (j : n), Zero.{u1} (α i j)] (i : m) (j : n), Eq.{succ u1} (α i j) (Zero.zero.{max u2 u3 u1} (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (DMatrix.hasZero.{u1, u2, u3} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j)) i j) (OfNat.ofNat.{u1} (α i j) 0 (OfNat.mk.{u1} (α i j) 0 (Zero.zero.{u1} (α i j) (_inst_5 i j))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} [_inst_5 : forall (i : m) (j : n), Zero.{u3} (α i j)] (i : m) (j : n), Eq.{succ u3} (α i j) (OfNat.ofNat.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.instZeroDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j))) i j) (OfNat.ofNat.{u3} (α i j) 0 (Zero.toOfNat0.{u3} (α i j) (_inst_5 i j)))
Case conversion may be inaccurate. Consider using '#align dmatrix.zero_apply DMatrix.zero_applyₓ'. -/
@[simp]
theorem zero_apply [∀ i j, Zero (α i j)] (i j) : (0 : DMatrix m n α) i j = 0 :=
  rfl
#align dmatrix.zero_apply DMatrix.zero_apply

/- warning: dmatrix.neg_apply -> DMatrix.neg_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u3} n] {α : m -> n -> Type.{u1}} [_inst_5 : forall (i : m) (j : n), Neg.{u1} (α i j)] (M : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (i : m) (j : n), Eq.{succ u1} (α i j) (Neg.neg.{max u2 u3 u1} (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (DMatrix.hasNeg.{u1, u2, u3} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j)) M i j) (Neg.neg.{u1} (α i j) (_inst_5 i j) (M i j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} [_inst_5 : forall (i : m) (j : n), Neg.{u3} (α i j)] (M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (i : m) (j : n), Eq.{succ u3} (α i j) (Neg.neg.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.instNegDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j)) M i j) (Neg.neg.{u3} (α i j) (_inst_5 i j) (M i j))
Case conversion may be inaccurate. Consider using '#align dmatrix.neg_apply DMatrix.neg_applyₓ'. -/
@[simp]
theorem neg_apply [∀ i j, Neg (α i j)] (M : DMatrix m n α) (i j) : (-M) i j = -M i j :=
  rfl
#align dmatrix.neg_apply DMatrix.neg_apply

/- warning: dmatrix.add_apply -> DMatrix.add_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u3} n] {α : m -> n -> Type.{u1}} [_inst_5 : forall (i : m) (j : n), Add.{u1} (α i j)] (M : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (N : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (i : m) (j : n), Eq.{succ u1} (α i j) (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (instHAdd.{max u2 u3 u1} (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (DMatrix.hasAdd.{u1, u2, u3} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j))) M N i j) (HAdd.hAdd.{u1, u1, u1} (α i j) (α i j) (α i j) (instHAdd.{u1} (α i j) (_inst_5 i j)) (M i j) (N i j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} [_inst_5 : forall (i : m) (j : n), Add.{u3} (α i j)] (M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (N : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (i : m) (j : n), Eq.{succ u3} (α i j) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (instHAdd.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.instAddDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j))) M N i j) (HAdd.hAdd.{u3, u3, u3} (α i j) (α i j) (α i j) (instHAdd.{u3} (α i j) (_inst_5 i j)) (M i j) (N i j))
Case conversion may be inaccurate. Consider using '#align dmatrix.add_apply DMatrix.add_applyₓ'. -/
@[simp]
theorem add_apply [∀ i j, Add (α i j)] (M N : DMatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
  rfl
#align dmatrix.add_apply DMatrix.add_apply

/- warning: dmatrix.sub_apply -> DMatrix.sub_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u3} n] {α : m -> n -> Type.{u1}} [_inst_5 : forall (i : m) (j : n), Sub.{u1} (α i j)] (M : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (N : DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (i : m) (j : n), Eq.{succ u1} (α i j) (HSub.hSub.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (instHSub.{max u2 u3 u1} (DMatrix.{u2, u3, u1} m n _inst_2 _inst_3 α) (DMatrix.hasSub.{u1, u2, u3} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j))) M N i j) (HSub.hSub.{u1, u1, u1} (α i j) (α i j) (α i j) (instHSub.{u1} (α i j) (_inst_5 i j)) (M i j) (N i j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} [_inst_5 : forall (i : m) (j : n), Sub.{u3} (α i j)] (M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (N : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (i : m) (j : n), Eq.{succ u3} (α i j) (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (instHSub.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.instSubDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j))) M N i j) (HSub.hSub.{u3, u3, u3} (α i j) (α i j) (α i j) (instHSub.{u3} (α i j) (_inst_5 i j)) (M i j) (N i j))
Case conversion may be inaccurate. Consider using '#align dmatrix.sub_apply DMatrix.sub_applyₓ'. -/
@[simp]
theorem sub_apply [∀ i j, Sub (α i j)] (M N : DMatrix m n α) (i j) : (M - N) i j = M i j - N i j :=
  rfl
#align dmatrix.sub_apply DMatrix.sub_apply

/- warning: dmatrix.map_zero -> DMatrix.map_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} [_inst_2 : Fintype.{u3} m] [_inst_3 : Fintype.{u4} n] {α : m -> n -> Type.{u1}} [_inst_5 : forall (i : m) (j : n), Zero.{u1} (α i j)] {β : m -> n -> Type.{u2}} [_inst_6 : forall (i : m) (j : n), Zero.{u2} (β i j)] {f : forall {{i : m}} {{j : n}}, (α i j) -> (β i j)}, (forall (i : m) (j : n), Eq.{succ u2} (β i j) (f i j (OfNat.ofNat.{u1} (α i j) 0 (OfNat.mk.{u1} (α i j) 0 (Zero.zero.{u1} (α i j) (_inst_5 i j))))) (OfNat.ofNat.{u2} (β i j) 0 (OfNat.mk.{u2} (β i j) 0 (Zero.zero.{u2} (β i j) (_inst_6 i j))))) -> (Eq.{succ (max u3 u4 u2)} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α (OfNat.ofNat.{max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) 0 (OfNat.mk.{max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) 0 (Zero.zero.{max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (DMatrix.hasZero.{u1, u3, u4} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j))))) (fun (i : m) (j : n) => β i j) f) (OfNat.ofNat.{max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) 0 (OfNat.mk.{max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) 0 (Zero.zero.{max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.hasZero.{u2, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j))))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} [_inst_5 : forall (i : m) (j : n), Zero.{u3} (α i j)] {β : m -> n -> Type.{u4}} [_inst_6 : forall (i : m) (j : n), Zero.{u4} (β i j)] {f : forall {{i : m}} {{j : n}}, (α i j) -> (β i j)}, (forall (i : m) (j : n), Eq.{succ u4} (β i j) (f i j (OfNat.ofNat.{u3} (α i j) 0 (Zero.toOfNat0.{u3} (α i j) (_inst_5 i j)))) (OfNat.ofNat.{u4} (β i j) 0 (Zero.toOfNat0.{u4} (β i j) (_inst_6 i j)))) -> (Eq.{max (max (succ u4) (succ u2)) (succ u1)} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α (OfNat.ofNat.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.instZeroDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => _inst_5 i j)))) (fun (i : m) (j : n) => β i j) f) (OfNat.ofNat.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) 0 (Zero.toOfNat0.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instZeroDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j)))))
Case conversion may be inaccurate. Consider using '#align dmatrix.map_zero DMatrix.map_zeroₓ'. -/
@[simp]
theorem map_zero [∀ i j, Zero (α i j)] {β : m → n → Type w} [∀ i j, Zero (β i j)]
    {f : ∀ ⦃i j⦄, α i j → β i j} (h : ∀ i j, f (0 : α i j) = 0) : (0 : DMatrix m n α).map f = 0 :=
  by
  ext
  simp [h]
#align dmatrix.map_zero DMatrix.map_zero

/- warning: dmatrix.map_add -> DMatrix.map_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} [_inst_2 : Fintype.{u3} m] [_inst_3 : Fintype.{u4} n] {α : m -> n -> Type.{u1}} [_inst_5 : forall (i : m) (j : n), AddMonoid.{u1} (α i j)] {β : m -> n -> Type.{u2}} [_inst_6 : forall (i : m) (j : n), AddMonoid.{u2} (β i j)] (f : forall {{i : m}} {{j : n}}, AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (M : DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (N : DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α), Eq.{succ (max u3 u4 u2)} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α (HAdd.hAdd.{max u3 u4 u1, max u3 u4 u1, max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (instHAdd.{max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (DMatrix.hasAdd.{u1, u3, u4} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => AddZeroClass.toHasAdd.{u1} (α i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j))))) M N) (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (fun (_x : AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) => (α i j) -> (β i j)) (AddMonoidHom.hasCoeToFun.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (f i j))) (HAdd.hAdd.{max u3 u4 u2, max u3 u4 u2, max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (instHAdd.{max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.hasAdd.{u2, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => AddZeroClass.toHasAdd.{u2} (β i j) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))))) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (fun (_x : AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) => (α i j) -> (β i j)) (AddMonoidHom.hasCoeToFun.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (f i j))) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α N (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (fun (_x : AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) => (α i j) -> (β i j)) (AddMonoidHom.hasCoeToFun.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (f i j))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} [_inst_5 : forall (i : m) (j : n), AddMonoid.{u3} (α i j)] {β : m -> n -> Type.{u4}} [_inst_6 : forall (i : m) (j : n), AddMonoid.{u4} (β i j)] (f : forall {{i : m}} {{j : n}}, AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (N : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (instHAdd.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.instAddDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => AddZeroClass.toAdd.{u3} (α i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j))))) M N) (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (fun (_x : α i j) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α i j) => β i j) _x) (AddHomClass.toFunLike.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (β i j) (AddZeroClass.toAdd.{u3} (α i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j))) (AddZeroClass.toAdd.{u4} (β i j) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (AddMonoidHomClass.toAddHomClass.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j)) (AddMonoidHom.addMonoidHomClass.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))))) (f i j))) (HAdd.hAdd.{max (max u4 u2) u1, max (max u4 u2) u1, max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (instHAdd.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instAddDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => AddZeroClass.toAdd.{u4} (β i j) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))))) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (fun (_x : α i j) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α i j) => β i j) _x) (AddHomClass.toFunLike.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (β i j) (AddZeroClass.toAdd.{u3} (α i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j))) (AddZeroClass.toAdd.{u4} (β i j) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (AddMonoidHomClass.toAddHomClass.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j)) (AddMonoidHom.addMonoidHomClass.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))))) (f i j))) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α N (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (fun (_x : α i j) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α i j) => β i j) _x) (AddHomClass.toFunLike.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (β i j) (AddZeroClass.toAdd.{u3} (α i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j))) (AddZeroClass.toAdd.{u4} (β i j) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (AddMonoidHomClass.toAddHomClass.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j)) (AddMonoidHom.addMonoidHomClass.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))))) (f i j))))
Case conversion may be inaccurate. Consider using '#align dmatrix.map_add DMatrix.map_addₓ'. -/
theorem map_add [∀ i j, AddMonoid (α i j)] {β : m → n → Type w} [∀ i j, AddMonoid (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : DMatrix m n α) :
    ((M + N).map fun i j => @f i j) = (M.map fun i j => @f i j) + N.map fun i j => @f i j :=
  by
  ext
  simp
#align dmatrix.map_add DMatrix.map_add

/- warning: dmatrix.map_sub -> DMatrix.map_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} [_inst_2 : Fintype.{u3} m] [_inst_3 : Fintype.{u4} n] {α : m -> n -> Type.{u1}} [_inst_5 : forall (i : m) (j : n), AddGroup.{u1} (α i j)] {β : m -> n -> Type.{u2}} [_inst_6 : forall (i : m) (j : n), AddGroup.{u2} (β i j)] (f : forall {{i : m}} {{j : n}}, AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) (M : DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (N : DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α), Eq.{succ (max u3 u4 u2)} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α (HSub.hSub.{max u3 u4 u1, max u3 u4 u1, max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (instHSub.{max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α) (DMatrix.hasSub.{u1, u3, u4} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => SubNegMonoid.toHasSub.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j))))) M N) (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) (fun (_x : AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) => (α i j) -> (β i j)) (AddMonoidHom.hasCoeToFun.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) (f i j))) (HSub.hSub.{max u3 u4 u2, max u3 u4 u2, max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (instHSub.{max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.hasSub.{u2, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => SubNegMonoid.toHasSub.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) (fun (_x : AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) => (α i j) -> (β i j)) (AddMonoidHom.hasCoeToFun.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) (f i j))) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α N (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) (fun (_x : AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) => (α i j) -> (β i j)) (AddMonoidHom.hasCoeToFun.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (SubNegMonoid.toAddMonoid.{u1} (α i j) (AddGroup.toSubNegMonoid.{u1} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u2} (β i j) (SubNegMonoid.toAddMonoid.{u2} (β i j) (AddGroup.toSubNegMonoid.{u2} (β i j) (_inst_6 i j))))) (f i j))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} [_inst_5 : forall (i : m) (j : n), AddGroup.{u3} (α i j)] {β : m -> n -> Type.{u4}} [_inst_6 : forall (i : m) (j : n), AddGroup.{u4} (β i j)] (f : forall {{i : m}} {{j : n}}, AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (N : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (instHSub.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α) (DMatrix.instSubDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 α (fun (i : m) (j : n) => SubNegMonoid.toSub.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j))))) M N) (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (fun (_x : α i j) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α i j) => β i j) _x) (AddHomClass.toFunLike.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (β i j) (AddZeroClass.toAdd.{u3} (α i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j))))) (AddZeroClass.toAdd.{u4} (β i j) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (AddMonoidHomClass.toAddHomClass.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j)))) (AddMonoidHom.addMonoidHomClass.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))))) (f i j))) (HSub.hSub.{max (max u4 u2) u1, max (max u4 u2) u1, max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (instHSub.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instSubDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => SubNegMonoid.toSub.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (fun (_x : α i j) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α i j) => β i j) _x) (AddHomClass.toFunLike.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (β i j) (AddZeroClass.toAdd.{u3} (α i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j))))) (AddZeroClass.toAdd.{u4} (β i j) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (AddMonoidHomClass.toAddHomClass.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j)))) (AddMonoidHom.addMonoidHomClass.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))))) (f i j))) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α N (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (fun (_x : α i j) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α i j) => β i j) _x) (AddHomClass.toFunLike.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (β i j) (AddZeroClass.toAdd.{u3} (α i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j))))) (AddZeroClass.toAdd.{u4} (β i j) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (AddMonoidHomClass.toAddHomClass.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))) (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j)))) (AddMonoidHom.addMonoidHomClass.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (SubNegMonoid.toAddMonoid.{u3} (α i j) (AddGroup.toSubNegMonoid.{u3} (α i j) (_inst_5 i j)))) (AddMonoid.toAddZeroClass.{u4} (β i j) (SubNegMonoid.toAddMonoid.{u4} (β i j) (AddGroup.toSubNegMonoid.{u4} (β i j) (_inst_6 i j))))))) (f i j))))
Case conversion may be inaccurate. Consider using '#align dmatrix.map_sub DMatrix.map_subₓ'. -/
theorem map_sub [∀ i j, AddGroup (α i j)] {β : m → n → Type w} [∀ i j, AddGroup (β i j)]
    (f : ∀ ⦃i j⦄, α i j →+ β i j) (M N : DMatrix m n α) :
    ((M - N).map fun i j => @f i j) = (M.map fun i j => @f i j) - N.map fun i j => @f i j :=
  by
  ext
  simp
#align dmatrix.map_sub DMatrix.map_sub

#print DMatrix.subsingleton_of_empty_left /-
instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (DMatrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim i⟩
#align dmatrix.subsingleton_of_empty_left DMatrix.subsingleton_of_empty_left
-/

#print DMatrix.subsingleton_of_empty_right /-
instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (DMatrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim j⟩
#align dmatrix.subsingleton_of_empty_right DMatrix.subsingleton_of_empty_right
-/

end DMatrix

#print AddMonoidHom.mapDMatrix /-
/-- The `add_monoid_hom` between spaces of dependently typed matrices
induced by an `add_monoid_hom` between their coefficients. -/
def AddMonoidHom.mapDMatrix [∀ i j, AddMonoid (α i j)] {β : m → n → Type w}
    [∀ i j, AddMonoid (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j) : DMatrix m n α →+ DMatrix m n β
    where
  toFun M := M.map fun i j => @f i j
  map_zero' := by simp
  map_add' := DMatrix.map_add f
#align add_monoid_hom.map_dmatrix AddMonoidHom.mapDMatrix
-/

/- warning: add_monoid_hom.map_dmatrix_apply -> AddMonoidHom.mapDMatrix_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} [_inst_2 : Fintype.{u3} m] [_inst_3 : Fintype.{u4} n] {α : m -> n -> Type.{u1}} [_inst_5 : forall (i : m) (j : n), AddMonoid.{u1} (α i j)] {β : m -> n -> Type.{u2}} [_inst_6 : forall (i : m) (j : n), AddMonoid.{u2} (β i j)] (f : forall {{i : m}} {{j : n}}, AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (M : DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 α), Eq.{succ (max u3 u4 u2)} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (coeFn.{max (succ (max u3 u4 u2)) (succ (max u3 u4 u1)), max (succ (max u3 u4 u1)) (succ (max u3 u4 u2))} (AddMonoidHom.{max u3 u4 u1, max u3 u4 u2} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.addMonoid.{u1, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => (fun (i : m) (j : n) => _inst_5 i j) i j))) (AddMonoid.toAddZeroClass.{max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.addMonoid.{u2, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => (fun (i : m) (j : n) => _inst_6 i j) i j)))) (fun (_x : AddMonoidHom.{max u3 u4 u1, max u3 u4 u2} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.addMonoid.{u1, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => (fun (i : m) (j : n) => _inst_5 i j) i j))) (AddMonoid.toAddZeroClass.{max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.addMonoid.{u2, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => (fun (i : m) (j : n) => _inst_6 i j) i j)))) => (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) -> (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j))) (AddMonoidHom.hasCoeToFun.{max u3 u4 u1, max u3 u4 u2} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max u3 u4 u1} (DMatrix.{u3, u4, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.addMonoid.{u1, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => (fun (i : m) (j : n) => _inst_5 i j) i j))) (AddMonoid.toAddZeroClass.{max u3 u4 u2} (DMatrix.{u3, u4, u2} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.addMonoid.{u2, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => (fun (i : m) (j : n) => _inst_6 i j) i j)))) (AddMonoidHom.mapDMatrix.{u1, u2, u3, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => _inst_5 i j) (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j) f) M) (DMatrix.map.{u1, u2, u3, u4} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (fun (_x : AddMonoidHom.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) => (α i j) -> (β i j)) (AddMonoidHom.hasCoeToFun.{u1, u2} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u1} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u2} (β i j) (_inst_6 i j))) (f i j)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u1} n] {α : m -> n -> Type.{u3}} [_inst_5 : forall (i : m) (j : n), AddMonoid.{u3} (α i j)] {β : m -> n -> Type.{u4}} [_inst_6 : forall (i : m) (j : n), AddMonoid.{u4} (β i j)] (f : forall {{i : m}} {{j : n}}, AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (M : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) => DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) M) (FunLike.coe.{max (max (max (succ u3) (succ u4)) (succ u2)) (succ u1), max (max (succ u3) (succ u2)) (succ u1), max (max (succ u4) (succ u2)) (succ u1)} (AddMonoidHom.{max (max u3 u1) u2, max (max u4 u1) u2} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.instAddMonoidDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => _inst_5 i j))) (AddMonoid.toAddZeroClass.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instAddMonoidDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j)))) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (fun (_x : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) => DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) _x) (AddHomClass.toFunLike.{max (max (max u3 u4) u2) u1, max (max u3 u2) u1, max (max u4 u2) u1} (AddMonoidHom.{max (max u3 u1) u2, max (max u4 u1) u2} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.instAddMonoidDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => _inst_5 i j))) (AddMonoid.toAddZeroClass.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instAddMonoidDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j)))) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddZeroClass.toAdd.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (AddMonoid.toAddZeroClass.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.instAddMonoidDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => _inst_5 i j)))) (AddZeroClass.toAdd.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instAddMonoidDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j)))) (AddMonoidHomClass.toAddHomClass.{max (max (max u3 u4) u2) u1, max (max u3 u2) u1, max (max u4 u2) u1} (AddMonoidHom.{max (max u3 u1) u2, max (max u4 u1) u2} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.instAddMonoidDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => _inst_5 i j))) (AddMonoid.toAddZeroClass.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instAddMonoidDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j)))) (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.instAddMonoidDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => _inst_5 i j))) (AddMonoid.toAddZeroClass.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instAddMonoidDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j))) (AddMonoidHom.addMonoidHomClass.{max (max u3 u2) u1, max (max u4 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (AddMonoid.toAddZeroClass.{max (max u3 u2) u1} (DMatrix.{u2, u1, u3} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j)) (DMatrix.instAddMonoidDMatrix.{u3, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => _inst_5 i j))) (AddMonoid.toAddZeroClass.{max (max u4 u2) u1} (DMatrix.{u2, u1, u4} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j)) (DMatrix.instAddMonoidDMatrix.{u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j)))))) (AddMonoidHom.mapDMatrix.{u3, u4, u2, u1} m n _inst_2 _inst_3 (fun (i : m) (j : n) => α i j) (fun (i : m) (j : n) => _inst_5 i j) (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => _inst_6 i j) f) M) (DMatrix.map.{u3, u4, u2, u1} m n _inst_2 _inst_3 α M (fun (i : m) (j : n) => β i j) (fun (i : m) (j : n) => FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (fun (_x : α i j) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α i j) => β i j) _x) (AddHomClass.toFunLike.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (β i j) (AddZeroClass.toAdd.{u3} (α i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j))) (AddZeroClass.toAdd.{u4} (β i j) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (AddMonoidHomClass.toAddHomClass.{max u3 u4, u3, u4} (AddMonoidHom.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))) (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j)) (AddMonoidHom.addMonoidHomClass.{u3, u4} (α i j) (β i j) (AddMonoid.toAddZeroClass.{u3} (α i j) (_inst_5 i j)) (AddMonoid.toAddZeroClass.{u4} (β i j) (_inst_6 i j))))) (f i j)))
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.map_dmatrix_apply AddMonoidHom.mapDMatrix_applyₓ'. -/
@[simp]
theorem AddMonoidHom.mapDMatrix_apply [∀ i j, AddMonoid (α i j)] {β : m → n → Type w}
    [∀ i j, AddMonoid (β i j)] (f : ∀ ⦃i j⦄, α i j →+ β i j) (M : DMatrix m n α) :
    AddMonoidHom.mapDMatrix f M = M.map fun i j => @f i j :=
  rfl
#align add_monoid_hom.map_dmatrix_apply AddMonoidHom.mapDMatrix_apply

