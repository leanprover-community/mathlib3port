/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang

! This file was ported from Lean 3 source module data.matrix.basic
! leanprover-community/mathlib commit 3e068ece210655b7b9a9477c3aff38a492400aa1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Pi
import Mathbin.Algebra.BigOperators.Pi
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.BigOperators.RingEquiv
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.Module.Pi
import Mathbin.Algebra.Star.BigOperators
import Mathbin.Algebra.Star.Module
import Mathbin.Algebra.Star.Pi
import Mathbin.Data.Fintype.BigOperators

/-!
# Matrices

This file defines basic properties of matrices.

Matrices with rows indexed by `m`, columns indexed by `n`, and entries of type `α` are represented
with `matrix m n α`. For the typical approach of counting rows and columns,
`matrix (fin m) (fin n) α` can be used.

## Notation

The locale `matrix` gives the following notation:

* `⬝ᵥ` for `matrix.dot_product`
* `⬝` for `matrix.mul`
* `ᵀ` for `matrix.transpose`
* `ᴴ` for `matrix.conj_transpose`

## Implementation notes

For convenience, `matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `λ i j, _` or even `(λ i j, _ : matrix m n α)`, as these are not recognized by lean as having
the right type. Instead, `matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/


universe u u' v w

open BigOperators

#print Matrix /-
/-- `matrix m n R` is the type of matrices with entries in `R`, whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m → n → α
#align matrix Matrix
-/

variable {l m n o : Type _} {m' : o → Type _} {n' : o → Type _}

variable {R : Type _} {S : Type _} {α : Type v} {β : Type w} {γ : Type _}

namespace Matrix

section Ext

variable {M N : Matrix m n α}

/- warning: matrix.ext_iff -> Matrix.ext_iff is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {N : Matrix.{u2, u3, u1} m n α}, Iff (forall (i : m) (j : n), Eq.{succ u1} α (M i j) (N i j)) (Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) M N)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {M : Matrix.{u2, u1, u3} m n α} {N : Matrix.{u2, u1, u3} m n α}, Iff (forall (i : m) (j : n), Eq.{succ u3} α (M i j) (N i j)) (Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) M N)
Case conversion may be inaccurate. Consider using '#align matrix.ext_iff Matrix.ext_iffₓ'. -/
theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩
#align matrix.ext_iff Matrix.ext_iff

/- warning: matrix.ext -> Matrix.ext is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {N : Matrix.{u2, u3, u1} m n α}, (forall (i : m) (j : n), Eq.{succ u1} α (M i j) (N i j)) -> (Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) M N)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {M : Matrix.{u2, u1, u3} m n α} {N : Matrix.{u2, u1, u3} m n α}, (forall (i : m) (j : n), Eq.{succ u3} α (M i j) (N i j)) -> (Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) M N)
Case conversion may be inaccurate. Consider using '#align matrix.ext Matrix.extₓ'. -/
@[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp
#align matrix.ext Matrix.ext

end Ext

#print Matrix.of /-
/-- Cast a function into a matrix.

The two sides of the equivalence are definitionally equal types. We want to use an explicit cast
to distinguish the types because `matrix` has different instances to pi types (such as `pi.has_mul`,
which performs elementwise multiplication, vs `matrix.has_mul`).

If you are defining a matrix, in terms of its entries, use `of (λ i j, _)`. The
purpose of this approach is to ensure that terms of th
e form `(λ i j, _) * (λ i j, _)` do not
appear, as the type of `*` can be misleading.

Porting note: In Lean 3, it is also safe to use pattern matching in a definition as `| i j := _`,
which can only be unfolded when fully-applied. leanprover/lean4#2042 means this does not
(currently) work in Lean 4.
-/
def of : (m → n → α) ≃ Matrix m n α :=
  Equiv.refl _
#align matrix.of Matrix.of
-/

/- warning: matrix.of_apply -> Matrix.of_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} (f : m -> n -> α) (i : m) (j : n), Eq.{succ u1} α (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) f i j) (f i j)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} (f : m -> n -> α) (i : m) (j : n), Eq.{succ u3} α (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (max (succ u3) (succ u1)) (succ u2), max (max (succ u3) (succ u2)) (succ u1)} (m -> n -> α) (Matrix.{u1, u2, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u1, u2, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (m -> n -> α) (Matrix.{u1, u2, u3} m n α)) (Matrix.of.{u3, u1, u2} m n α) f i j) (f i j)
Case conversion may be inaccurate. Consider using '#align matrix.of_apply Matrix.of_applyₓ'. -/
@[simp]
theorem of_apply (f : m → n → α) (i j) : of f i j = f i j :=
  rfl
#align matrix.of_apply Matrix.of_apply

/- warning: matrix.of_symm_apply -> Matrix.of_symm_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} (f : Matrix.{u2, u3, u1} m n α) (i : m) (j : n), Eq.{succ u1} α (coeFn.{max 1 (max (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1)) (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1)), max (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1)} (Equiv.{succ (max u2 u3 u1), max (succ u2) (succ u3) (succ u1)} (Matrix.{u2, u3, u1} m n α) (m -> n -> α)) (fun (_x : Equiv.{succ (max u2 u3 u1), max (succ u2) (succ u3) (succ u1)} (Matrix.{u2, u3, u1} m n α) (m -> n -> α)) => (Matrix.{u2, u3, u1} m n α) -> m -> n -> α) (Equiv.hasCoeToFun.{succ (max u2 u3 u1), max (succ u2) (succ u3) (succ u1)} (Matrix.{u2, u3, u1} m n α) (m -> n -> α)) (Equiv.symm.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α) (Matrix.of.{u1, u2, u3} m n α)) f i j) (f i j)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} (f : Matrix.{u2, u1, u3} m n α) (i : m) (j : n), Eq.{succ u3} α (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Matrix.{u2, u1, u3} m n α) (m -> n -> α)) (Matrix.{u2, u1, u3} m n α) (fun (_x : Matrix.{u2, u1, u3} m n α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u2, u1, u3} m n α) => m -> n -> α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Matrix.{u2, u1, u3} m n α) (m -> n -> α)) (Equiv.symm.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α) (Matrix.of.{u3, u2, u1} m n α)) f i j) (f i j)
Case conversion may be inaccurate. Consider using '#align matrix.of_symm_apply Matrix.of_symm_applyₓ'. -/
@[simp]
theorem of_symm_apply (f : Matrix m n α) (i j) : of.symm f i j = f i j :=
  rfl
#align matrix.of_symm_apply Matrix.of_symm_apply

#print Matrix.map /-
/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`.

This is available in bundled forms as:
* `add_monoid_hom.map_matrix`
* `linear_map.map_matrix`
* `ring_hom.map_matrix`
* `alg_hom.map_matrix`
* `equiv.map_matrix`
* `add_equiv.map_matrix`
* `linear_equiv.map_matrix`
* `ring_equiv.map_matrix`
* `alg_equiv.map_matrix`
-/
def map (M : Matrix m n α) (f : α → β) : Matrix m n β :=
  of fun i j => f (M i j)
#align matrix.map Matrix.map
-/

/- warning: matrix.map_apply -> Matrix.map_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {M : Matrix.{u3, u4, u1} m n α} {f : α -> β} {i : m} {j : n}, Eq.{succ u2} β (Matrix.map.{u1, u2, u3, u4} m n α β M f i j) (f (M i j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} {M : Matrix.{u2, u1, u3} m n α} {f : α -> β} {i : m} {j : n}, Eq.{succ u4} β (Matrix.map.{u3, u4, u2, u1} m n α β M f i j) (f (M i j))
Case conversion may be inaccurate. Consider using '#align matrix.map_apply Matrix.map_applyₓ'. -/
@[simp]
theorem map_apply {M : Matrix m n α} {f : α → β} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl
#align matrix.map_apply Matrix.map_apply

/- warning: matrix.map_id -> Matrix.map_id is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.map.{u1, u1, u2, u3} m n α α M (id.{succ u1} α)) M
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.map.{u3, u3, u2, u1} m n α α M (id.{succ u3} α)) M
Case conversion may be inaccurate. Consider using '#align matrix.map_id Matrix.map_idₓ'. -/
@[simp]
theorem map_id (M : Matrix m n α) : M.map id = M :=
  by
  ext
  rfl
#align matrix.map_id Matrix.map_id

/- warning: matrix.map_map -> Matrix.map_map is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {β : Type.{u4}} {γ : Type.{u5}} {f : α -> β} {g : β -> γ}, Eq.{succ (max u2 u3 u5)} (Matrix.{u2, u3, u5} m n γ) (Matrix.map.{u4, u5, u2, u3} m n β γ (Matrix.map.{u1, u4, u2, u3} m n α β M f) g) (Matrix.map.{u1, u5, u2, u3} m n α γ M (Function.comp.{succ u1, succ u4, succ u5} α β γ g f))
but is expected to have type
  forall {m : Type.{u4}} {n : Type.{u3}} {α : Type.{u5}} {M : Matrix.{u4, u3, u5} m n α} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β} {g : β -> γ}, Eq.{max (max (succ u4) (succ u3)) (succ u1)} (Matrix.{u4, u3, u1} m n γ) (Matrix.map.{u2, u1, u4, u3} m n β γ (Matrix.map.{u5, u2, u4, u3} m n α β M f) g) (Matrix.map.{u5, u1, u4, u3} m n α γ M (Function.comp.{succ u5, succ u2, succ u1} α β γ g f))
Case conversion may be inaccurate. Consider using '#align matrix.map_map Matrix.map_mapₓ'. -/
@[simp]
theorem map_map {M : Matrix m n α} {β γ : Type _} {f : α → β} {g : β → γ} :
    (M.map f).map g = M.map (g ∘ f) := by
  ext
  rfl
#align matrix.map_map Matrix.map_map

/- warning: matrix.map_injective -> Matrix.map_injective is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Function.Injective.{succ (max u3 u4 u1), succ (max u3 u4 u2)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) (fun (M : Matrix.{u3, u4, u1} m n α) => Matrix.map.{u1, u2, u3, u4} m n α β M f))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} {f : α -> β}, (Function.Injective.{succ u3, succ u4} α β f) -> (Function.Injective.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u2) (succ u1)) (succ u4)} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u4} m n β) (fun (M : Matrix.{u2, u1, u3} m n α) => Matrix.map.{u3, u4, u2, u1} m n α β M f))
Case conversion may be inaccurate. Consider using '#align matrix.map_injective Matrix.map_injectiveₓ'. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective fun M : Matrix m n α => M.map f := fun M N h =>
  ext fun i j => hf <| ext_iff.mpr h i j
#align matrix.map_injective Matrix.map_injective

#print Matrix.transpose /-
/-- The transpose of a matrix. -/
def transpose (M : Matrix m n α) : Matrix n m α :=
  of fun x y => M y x
#align matrix.transpose Matrix.transpose
-/

/- warning: matrix.transpose_apply -> Matrix.transpose_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} (M : Matrix.{u2, u3, u1} m n α) (i : n) (j : m), Eq.{succ u1} α (Matrix.transpose.{u1, u2, u3} m n α M i j) (M j i)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} (M : Matrix.{u2, u1, u3} m n α) (i : n) (j : m), Eq.{succ u3} α (Matrix.transpose.{u3, u2, u1} m n α M i j) (M j i)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_apply Matrix.transpose_applyₓ'. -/
-- TODO: set as an equation lemma for `transpose`, see mathlib4#3024
@[simp]
theorem transpose_apply (M : Matrix m n α) (i j) : transpose M i j = M j i :=
  rfl
#align matrix.transpose_apply Matrix.transpose_apply

-- mathport name: matrix.transpose
scoped postfix:1024 "ᵀ" => Matrix.transpose

#print Matrix.conjTranspose /-
/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star
#align matrix.conj_transpose Matrix.conjTranspose
-/

-- mathport name: matrix.conj_transpose
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

#print Matrix.col /-
/-- `matrix.col u` is the column matrix whose entries are given by `u`. -/
def col (w : m → α) : Matrix m Unit α :=
  of fun x y => w x
#align matrix.col Matrix.col
-/

/- warning: matrix.col_apply -> Matrix.col_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} (w : m -> α) (i : m) (j : Unit), Eq.{succ u1} α (Matrix.col.{u1, u2} m α w i j) (w i)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} (w : m -> α) (i : m) (j : Unit), Eq.{succ u2} α (Matrix.col.{u2, u1} m α w i j) (w i)
Case conversion may be inaccurate. Consider using '#align matrix.col_apply Matrix.col_applyₓ'. -/
-- TODO: set as an equation lemma for `col`, see mathlib4#3024
@[simp]
theorem col_apply (w : m → α) (i j) : col w i j = w i :=
  rfl
#align matrix.col_apply Matrix.col_apply

#print Matrix.row /-
/-- `matrix.row u` is the row matrix whose entries are given by `u`. -/
def row (v : n → α) : Matrix Unit n α :=
  of fun x y => v y
#align matrix.row Matrix.row
-/

/- warning: matrix.row_apply -> Matrix.row_apply is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} (v : n -> α) (i : Unit) (j : n), Eq.{succ u1} α (Matrix.row.{u1, u2} n α v i j) (v j)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} (v : n -> α) (i : Unit) (j : n), Eq.{succ u2} α (Matrix.row.{u2, u1} n α v i j) (v j)
Case conversion may be inaccurate. Consider using '#align matrix.row_apply Matrix.row_applyₓ'. -/
-- TODO: set as an equation lemma for `row`, see mathlib4#3024
@[simp]
theorem row_apply (v : n → α) (i j) : row v i j = v j :=
  rfl
#align matrix.row_apply Matrix.row_apply

instance [Inhabited α] : Inhabited (Matrix m n α) :=
  Pi.inhabited _

instance [Add α] : Add (Matrix m n α) :=
  Pi.instAdd

instance [AddSemigroup α] : AddSemigroup (Matrix m n α) :=
  Pi.addSemigroup

instance [AddCommSemigroup α] : AddCommSemigroup (Matrix m n α) :=
  Pi.addCommSemigroup

instance [Zero α] : Zero (Matrix m n α) :=
  Pi.instZero

instance [AddZeroClass α] : AddZeroClass (Matrix m n α) :=
  Pi.addZeroClass

instance [AddMonoid α] : AddMonoid (Matrix m n α) :=
  Pi.addMonoid

instance [AddCommMonoid α] : AddCommMonoid (Matrix m n α) :=
  Pi.addCommMonoid

instance [Neg α] : Neg (Matrix m n α) :=
  Pi.instNeg

instance [Sub α] : Sub (Matrix m n α) :=
  Pi.instSub

instance [AddGroup α] : AddGroup (Matrix m n α) :=
  Pi.addGroup

instance [AddCommGroup α] : AddCommGroup (Matrix m n α) :=
  Pi.addCommGroup

instance [Unique α] : Unique (Matrix m n α) :=
  Pi.unique

instance [Subsingleton α] : Subsingleton (Matrix m n α) :=
  Pi.subsingleton

instance [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n α) :=
  Function.nontrivial

instance [SMul R α] : SMul R (Matrix m n α) :=
  Pi.instSMul

instance [SMul R α] [SMul S α] [SMulCommClass R S α] : SMulCommClass R S (Matrix m n α) :=
  Pi.smulCommClass

instance [SMul R S] [SMul R α] [SMul S α] [IsScalarTower R S α] :
    IsScalarTower R S (Matrix m n α) :=
  Pi.isScalarTower

instance [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] : IsCentralScalar R (Matrix m n α) :=
  Pi.isCentralScalar

instance [Monoid R] [MulAction R α] : MulAction R (Matrix m n α) :=
  Pi.mulAction _

instance [Monoid R] [AddMonoid α] [DistribMulAction R α] : DistribMulAction R (Matrix m n α) :=
  Pi.distribMulAction _

instance [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Matrix m n α) :=
  Pi.module _ _ _

/-! simp-normal form pulls `of` to the outside. -/


/- warning: matrix.of_zero -> Matrix.of_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α], Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) (OfNat.ofNat.{max u2 u3 u1} (m -> n -> α) 0 (OfNat.mk.{max u2 u3 u1} (m -> n -> α) 0 (Zero.zero.{max u2 u3 u1} (m -> n -> α) (Pi.instZero.{u2, max u3 u1} m (fun (ᾰ : m) => n -> α) (fun (i : m) => Pi.instZero.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_1))))))) (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α _inst_1))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) (OfNat.ofNat.{max (max u3 u2) u1} (m -> n -> α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (m -> n -> α) (Pi.instZero.{u2, max u3 u1} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.2915 : m) => n -> α) (fun (i : m) => Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.2917 : n) => α) (fun (i : n) => _inst_1)))))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) (OfNat.ofNat.{max (max u3 u2) u1} (m -> n -> α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (m -> n -> α) (Pi.instZero.{u2, max u3 u1} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.2915 : m) => n -> α) (fun (i : m) => Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.2917 : n) => α) (fun (i : n) => _inst_1)))))) (OfNat.ofNat.{max (max u3 u2) u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) (OfNat.ofNat.{max (max u3 u2) u1} (m -> n -> α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (m -> n -> α) (Pi.instZero.{u2, max u3 u1} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.2915 : m) => n -> α) (fun (i : m) => Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.2917 : n) => α) (fun (i : n) => _inst_1)))))) 0 (Zero.toOfNat0.{max (max u3 u2) u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) (OfNat.ofNat.{max (max u3 u2) u1} (m -> n -> α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (m -> n -> α) (Pi.instZero.{u2, max u3 u1} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.2915 : m) => n -> α) (fun (i : m) => Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.2917 : n) => α) (fun (i : n) => _inst_1)))))) (Matrix.zero.{u3, u2, u1} m n α _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.of_zero Matrix.of_zeroₓ'. -/
@[simp]
theorem of_zero [Zero α] : of (0 : m → n → α) = 0 :=
  rfl
#align matrix.of_zero Matrix.of_zero

/- warning: matrix.of_add_of -> Matrix.of_add_of is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Add.{u1} α] (f : m -> n -> α) (g : m -> n -> α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α _inst_1)) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) f) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) g)) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (m -> n -> α) (m -> n -> α) (m -> n -> α) (instHAdd.{max u2 u3 u1} (m -> n -> α) (Pi.instAdd.{u2, max u3 u1} m (fun (ᾰ : m) => n -> α) (fun (i : m) => Pi.instAdd.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_1)))) f g))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Add.{u3} α] (f : m -> n -> α) (g : m -> n -> α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) g) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) (instHAdd.{max (max u3 u2) u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) (Matrix.add.{u3, u2, u1} m n α _inst_1)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) f) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) g)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (m -> n -> α) (m -> n -> α) (m -> n -> α) (instHAdd.{max (max u3 u2) u1} (m -> n -> α) (Pi.instAdd.{u2, max u3 u1} m (fun (ᾰ : m) => n -> α) (fun (i : m) => Pi.instAdd.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_1)))) f g))
Case conversion may be inaccurate. Consider using '#align matrix.of_add_of Matrix.of_add_ofₓ'. -/
@[simp]
theorem of_add_of [Add α] (f g : m → n → α) : of f + of g = of (f + g) :=
  rfl
#align matrix.of_add_of Matrix.of_add_of

/- warning: matrix.of_sub_of -> Matrix.of_sub_of is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Sub.{u1} α] (f : m -> n -> α) (g : m -> n -> α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (HSub.hSub.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHSub.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasSub.{u1, u2, u3} m n α _inst_1)) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) f) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) g)) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) (HSub.hSub.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (m -> n -> α) (m -> n -> α) (m -> n -> α) (instHSub.{max u2 u3 u1} (m -> n -> α) (Pi.instSub.{u2, max u3 u1} m (fun (ᾰ : m) => n -> α) (fun (i : m) => Pi.instSub.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_1)))) f g))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Sub.{u3} α] (f : m -> n -> α) (g : m -> n -> α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) g) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) (instHSub.{max (max u3 u2) u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) (Matrix.sub.{u3, u2, u1} m n α _inst_1)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) f) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) g)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (m -> n -> α) (m -> n -> α) (m -> n -> α) (instHSub.{max (max u3 u2) u1} (m -> n -> α) (Pi.instSub.{u2, max u3 u1} m (fun (ᾰ : m) => n -> α) (fun (i : m) => Pi.instSub.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_1)))) f g))
Case conversion may be inaccurate. Consider using '#align matrix.of_sub_of Matrix.of_sub_ofₓ'. -/
@[simp]
theorem of_sub_of [Sub α] (f g : m → n → α) : of f - of g = of (f - g) :=
  rfl
#align matrix.of_sub_of Matrix.of_sub_of

/- warning: matrix.neg_of -> Matrix.neg_of is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Neg.{u1} α] (f : m -> n -> α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Neg.neg.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasNeg.{u1, u2, u3} m n α _inst_1) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) f)) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) (Neg.neg.{max u2 u3 u1} (m -> n -> α) (Pi.instNeg.{u2, max u3 u1} m (fun (ᾰ : m) => n -> α) (fun (i : m) => Pi.instNeg.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_1))) f))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Neg.{u3} α] (f : m -> n -> α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) (Neg.neg.{max (max u3 u2) u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) f) (Matrix.neg.{u3, u2, u1} m n α _inst_1) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) f)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (m -> n -> α) (Matrix.{u2, u1, u3} m n α)) (Matrix.of.{u3, u2, u1} m n α) (Neg.neg.{max (max u3 u2) u1} (m -> n -> α) (Pi.instNeg.{u2, max u3 u1} m (fun (ᾰ : m) => n -> α) (fun (i : m) => Pi.instNeg.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_1))) f))
Case conversion may be inaccurate. Consider using '#align matrix.neg_of Matrix.neg_ofₓ'. -/
@[simp]
theorem neg_of [Neg α] (f : m → n → α) : -of f = of (-f) :=
  rfl
#align matrix.neg_of Matrix.neg_of

/- warning: matrix.smul_of -> Matrix.smul_of is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : SMul.{u4, u1} R α] (r : R) (f : m -> n -> α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α _inst_1) r (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) f)) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) (SMul.smul.{u4, max u2 u3 u1} R (m -> n -> α) (Function.hasSMul.{u2, u4, max u3 u1} m R (n -> α) (Function.hasSMul.{u3, u4, u1} n R α _inst_1)) r f))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} [_inst_1 : SMul.{u3, u4} R α] (r : R) (f : m -> n -> α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u4} m n α) f) (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u4} m n α) f) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u4} m n α) f) (instHSMul.{u3, max (max u4 u2) u1} R ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u4} m n α) f) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_1)) r (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4)} (Equiv.{max (max (succ u4) (succ u2)) (succ u1), max (max (succ u4) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u4} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u4} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4)} (m -> n -> α) (Matrix.{u2, u1, u4} m n α)) (Matrix.of.{u4, u2, u1} m n α) f)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4)} (Equiv.{max (max (succ u4) (succ u2)) (succ u1), max (max (succ u4) (succ u1)) (succ u2)} (m -> n -> α) (Matrix.{u2, u1, u4} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u1, u4} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4)} (m -> n -> α) (Matrix.{u2, u1, u4} m n α)) (Matrix.of.{u4, u2, u1} m n α) (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (m -> n -> α) (m -> n -> α) (instHSMul.{u3, max (max u4 u2) u1} R (m -> n -> α) (Pi.instSMul.{u2, max u4 u1, u3} m R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.3086 : m) => n -> α) (fun (i : m) => Pi.instSMul.{u1, u4, u3} n R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.3088 : n) => α) (fun (i : n) => _inst_1)))) r f))
Case conversion may be inaccurate. Consider using '#align matrix.smul_of Matrix.smul_ofₓ'. -/
@[simp]
theorem smul_of [SMul R α] (r : R) (f : m → n → α) : r • of f = of (r • f) :=
  rfl
#align matrix.smul_of Matrix.smul_of

/- warning: matrix.map_zero -> Matrix.map_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u1} α] [_inst_2 : Zero.{u2} β] (f : α -> β), (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) -> (Eq.{succ (max u3 u4 u2)} (Matrix.{u3, u4, u2} m n β) (Matrix.map.{u1, u2, u3, u4} m n α β (OfNat.ofNat.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) 0 (OfNat.mk.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) 0 (Zero.zero.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.hasZero.{u1, u3, u4} m n α _inst_1)))) f) (OfNat.ofNat.{max u3 u4 u2} (Matrix.{u3, u4, u2} m n β) 0 (OfNat.mk.{max u3 u4 u2} (Matrix.{u3, u4, u2} m n β) 0 (Zero.zero.{max u3 u4 u2} (Matrix.{u3, u4, u2} m n β) (Matrix.hasZero.{u2, u3, u4} m n β _inst_2)))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Zero.{u3} α] [_inst_2 : Zero.{u4} β] (f : α -> β), (Eq.{succ u4} β (f (OfNat.ofNat.{u3} α 0 (Zero.toOfNat0.{u3} α _inst_1))) (OfNat.ofNat.{u4} β 0 (Zero.toOfNat0.{u4} β _inst_2))) -> (Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m n β) (Matrix.map.{u3, u4, u2, u1} m n α β (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.zero.{u3, u2, u1} m n α _inst_1))) f) (OfNat.ofNat.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} m n β) 0 (Zero.toOfNat0.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} m n β) (Matrix.zero.{u4, u2, u1} m n β _inst_2))))
Case conversion may be inaccurate. Consider using '#align matrix.map_zero Matrix.map_zeroₓ'. -/
@[simp]
protected theorem map_zero [Zero α] [Zero β] (f : α → β) (h : f 0 = 0) :
    (0 : Matrix m n α).map f = 0 := by
  ext
  simp [h]
#align matrix.map_zero Matrix.map_zero

/- warning: matrix.map_add -> Matrix.map_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Add.{u1} α] [_inst_2 : Add.{u2} β] (f : α -> β), (forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) a₁ a₂)) (HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_2) (f a₁) (f a₂))) -> (forall (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u3 u4 u2)} (Matrix.{u3, u4, u2} m n β) (Matrix.map.{u1, u2, u3, u4} m n α β (HAdd.hAdd.{max u3 u4 u1, max u3 u4 u1, max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u1} m n α) (instHAdd.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.hasAdd.{u1, u3, u4} m n α _inst_1)) M N) f) (HAdd.hAdd.{max u3 u4 u2, max u3 u4 u2, max u3 u4 u2} (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u2} m n β) (instHAdd.{max u3 u4 u2} (Matrix.{u3, u4, u2} m n β) (Matrix.hasAdd.{u2, u3, u4} m n β _inst_2)) (Matrix.map.{u1, u2, u3, u4} m n α β M f) (Matrix.map.{u1, u2, u3, u4} m n α β N f)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Add.{u3} α] [_inst_2 : Add.{u4} β] (f : α -> β), (forall (a₁ : α) (a₂ : α), Eq.{succ u4} β (f (HAdd.hAdd.{u3, u3, u3} α α α (instHAdd.{u3} α _inst_1) a₁ a₂)) (HAdd.hAdd.{u4, u4, u4} β β β (instHAdd.{u4} β _inst_2) (f a₁) (f a₂))) -> (forall (M : Matrix.{u2, u1, u3} m n α) (N : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m n β) (Matrix.map.{u3, u4, u2, u1} m n α β (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α _inst_1)) M N) f) (HAdd.hAdd.{max (max u4 u2) u1, max (max u4 u2) u1, max (max u4 u2) u1} (Matrix.{u2, u1, u4} m n β) (Matrix.{u2, u1, u4} m n β) (Matrix.{u2, u1, u4} m n β) (instHAdd.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} m n β) (Matrix.add.{u4, u2, u1} m n β _inst_2)) (Matrix.map.{u3, u4, u2, u1} m n α β M f) (Matrix.map.{u3, u4, u2, u1} m n α β N f)))
Case conversion may be inaccurate. Consider using '#align matrix.map_add Matrix.map_addₓ'. -/
protected theorem map_add [Add α] [Add β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)
    (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f :=
  ext fun _ _ => hf _ _
#align matrix.map_add Matrix.map_add

/- warning: matrix.map_sub -> Matrix.map_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sub.{u1} α] [_inst_2 : Sub.{u2} β] (f : α -> β), (forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_1) a₁ a₂)) (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β _inst_2) (f a₁) (f a₂))) -> (forall (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u3 u4 u2)} (Matrix.{u3, u4, u2} m n β) (Matrix.map.{u1, u2, u3, u4} m n α β (HSub.hSub.{max u3 u4 u1, max u3 u4 u1, max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u1} m n α) (instHSub.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.hasSub.{u1, u3, u4} m n α _inst_1)) M N) f) (HSub.hSub.{max u3 u4 u2, max u3 u4 u2, max u3 u4 u2} (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u2} m n β) (instHSub.{max u3 u4 u2} (Matrix.{u3, u4, u2} m n β) (Matrix.hasSub.{u2, u3, u4} m n β _inst_2)) (Matrix.map.{u1, u2, u3, u4} m n α β M f) (Matrix.map.{u1, u2, u3, u4} m n α β N f)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Sub.{u3} α] [_inst_2 : Sub.{u4} β] (f : α -> β), (forall (a₁ : α) (a₂ : α), Eq.{succ u4} β (f (HSub.hSub.{u3, u3, u3} α α α (instHSub.{u3} α _inst_1) a₁ a₂)) (HSub.hSub.{u4, u4, u4} β β β (instHSub.{u4} β _inst_2) (f a₁) (f a₂))) -> (forall (M : Matrix.{u2, u1, u3} m n α) (N : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m n β) (Matrix.map.{u3, u4, u2, u1} m n α β (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSub.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.sub.{u3, u2, u1} m n α _inst_1)) M N) f) (HSub.hSub.{max (max u4 u2) u1, max (max u4 u2) u1, max (max u4 u2) u1} (Matrix.{u2, u1, u4} m n β) (Matrix.{u2, u1, u4} m n β) (Matrix.{u2, u1, u4} m n β) (instHSub.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} m n β) (Matrix.sub.{u4, u2, u1} m n β _inst_2)) (Matrix.map.{u3, u4, u2, u1} m n α β M f) (Matrix.map.{u3, u4, u2, u1} m n α β N f)))
Case conversion may be inaccurate. Consider using '#align matrix.map_sub Matrix.map_subₓ'. -/
protected theorem map_sub [Sub α] [Sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
    (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f :=
  ext fun _ _ => hf _ _
#align matrix.map_sub Matrix.map_sub

/- warning: matrix.map_smul -> Matrix.map_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {R : Type.{u5}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u5, u1} R α] [_inst_2 : SMul.{u5, u2} R β] (f : α -> β) (r : R), (forall (a : α), Eq.{succ u2} β (f (SMul.smul.{u5, u1} R α _inst_1 r a)) (SMul.smul.{u5, u2} R β _inst_2 r (f a))) -> (forall (M : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u3 u4 u2)} (Matrix.{u3, u4, u2} m n β) (Matrix.map.{u1, u2, u3, u4} m n α β (SMul.smul.{u5, max u3 u4 u1} R (Matrix.{u3, u4, u1} m n α) (Matrix.hasSmul.{u1, u3, u4, u5} m n R α _inst_1) r M) f) (SMul.smul.{u5, max u3 u4 u2} R (Matrix.{u3, u4, u2} m n β) (Matrix.hasSmul.{u2, u3, u4, u5} m n R β _inst_2) r (Matrix.map.{u1, u2, u3, u4} m n α β M f)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} {β : Type.{u5}} [_inst_1 : SMul.{u3, u4} R α] [_inst_2 : SMul.{u3, u5} R β] (f : α -> β) (r : R), (forall (a : α), Eq.{succ u5} β (f (HSMul.hSMul.{u3, u4, u4} R α α (instHSMul.{u3, u4} R α _inst_1) r a)) (HSMul.hSMul.{u3, u5, u5} R β β (instHSMul.{u3, u5} R β _inst_2) r (f a))) -> (forall (M : Matrix.{u2, u1, u4} m n α), Eq.{max (max (succ u5) (succ u2)) (succ u1)} (Matrix.{u2, u1, u5} m n β) (Matrix.map.{u4, u5, u2, u1} m n α β (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_1)) r M) f) (HSMul.hSMul.{u3, max (max u2 u1) u5, max (max u5 u2) u1} R (Matrix.{u2, u1, u5} m n β) (Matrix.{u2, u1, u5} m n β) (instHSMul.{u3, max (max u5 u2) u1} R (Matrix.{u2, u1, u5} m n β) (Matrix.smul.{u5, u2, u1, u3} m n R β _inst_2)) r (Matrix.map.{u4, u5, u2, u1} m n α β M f)))
Case conversion may be inaccurate. Consider using '#align matrix.map_smul Matrix.map_smulₓ'. -/
theorem map_smul [SMul R α] [SMul R β] (f : α → β) (r : R) (hf : ∀ a, f (r • a) = r • f a)
    (M : Matrix m n α) : (r • M).map f = r • M.map f :=
  ext fun _ _ => hf _
#align matrix.map_smul Matrix.map_smul

/- warning: matrix.map_smul' -> Matrix.map_smul' is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] (f : α -> β) (r : α) (A : Matrix.{u3, u3, u1} n n α), (forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a₁ a₂)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_2) (f a₁) (f a₂))) -> (Eq.{succ (max u3 u2)} (Matrix.{u3, u3, u2} n n β) (Matrix.map.{u1, u2, u3, u3} n n α β (SMul.smul.{u1, max u3 u1} α (Matrix.{u3, u3, u1} n n α) (Matrix.hasSmul.{u1, u3, u3, u1} n n α α (Mul.toSMul.{u1} α _inst_1)) r A) f) (SMul.smul.{u2, max u3 u2} β (Matrix.{u3, u3, u2} n n β) (Matrix.hasSmul.{u2, u3, u3, u2} n n β β (Mul.toSMul.{u2} β _inst_2)) (f r) (Matrix.map.{u1, u2, u3, u3} n n α β A f)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Mul.{u2} α] [_inst_2 : Mul.{u3} β] (f : α -> β) (r : α) (A : Matrix.{u1, u1, u2} n n α), (forall (a₁ : α) (a₂ : α), Eq.{succ u3} β (f (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a₁ a₂)) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β _inst_2) (f a₁) (f a₂))) -> (Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} n n β) (Matrix.map.{u2, u3, u1, u1} n n α β (HSMul.hSMul.{u2, max u2 u1, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHSMul.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Matrix.smul.{u2, u1, u1, u2} n n α α (Mul.toSMul.{u2} α _inst_1))) r A) f) (HSMul.hSMul.{u3, max u1 u3, max u3 u1} β (Matrix.{u1, u1, u3} n n β) (Matrix.{u1, u1, u3} n n β) (instHSMul.{u3, max u3 u1} β (Matrix.{u1, u1, u3} n n β) (Matrix.smul.{u3, u1, u1, u3} n n β β (Mul.toSMul.{u3} β _inst_2))) (f r) (Matrix.map.{u2, u3, u1, u1} n n α β A f)))
Case conversion may be inaccurate. Consider using '#align matrix.map_smul' Matrix.map_smul'ₓ'. -/
/-- The scalar action via `has_mul.to_has_smul` is transformed by the same map as the elements
of the matrix, when `f` preserves multiplication. -/
theorem map_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α)
    (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (r • A).map f = f r • A.map f :=
  ext fun _ _ => hf _ _
#align matrix.map_smul' Matrix.map_smul'

/- warning: matrix.map_op_smul' -> Matrix.map_op_smul' is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] (f : α -> β) (r : α) (A : Matrix.{u3, u3, u1} n n α), (forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a₁ a₂)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_2) (f a₁) (f a₂))) -> (Eq.{succ (max u3 u2)} (Matrix.{u3, u3, u2} n n β) (Matrix.map.{u1, u2, u3, u3} n n α β (SMul.smul.{u1, max u3 u1} (MulOpposite.{u1} α) (Matrix.{u3, u3, u1} n n α) (Matrix.hasSmul.{u1, u3, u3, u1} n n (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α _inst_1)) (MulOpposite.op.{u1} α r) A) f) (SMul.smul.{u2, max u3 u2} (MulOpposite.{u2} β) (Matrix.{u3, u3, u2} n n β) (Matrix.hasSmul.{u2, u3, u3, u2} n n (MulOpposite.{u2} β) β (Mul.toHasOppositeSMul.{u2} β _inst_2)) (MulOpposite.op.{u2} β (f r)) (Matrix.map.{u1, u2, u3, u3} n n α β A f)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Mul.{u2} α] [_inst_2 : Mul.{u3} β] (f : α -> β) (r : α) (A : Matrix.{u1, u1, u2} n n α), (forall (a₁ : α) (a₂ : α), Eq.{succ u3} β (f (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a₁ a₂)) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β _inst_2) (f a₁) (f a₂))) -> (Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} n n β) (Matrix.map.{u2, u3, u1, u1} n n α β (HSMul.hSMul.{u2, max u2 u1, max u2 u1} (MulOpposite.{u2} α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHSMul.{u2, max u2 u1} (MulOpposite.{u2} α) (Matrix.{u1, u1, u2} n n α) (Matrix.smul.{u2, u1, u1, u2} n n (MulOpposite.{u2} α) α (Mul.toHasOppositeSMul.{u2} α _inst_1))) (MulOpposite.op.{u2} α r) A) f) (HSMul.hSMul.{u3, max u1 u3, max u3 u1} (MulOpposite.{u3} β) (Matrix.{u1, u1, u3} n n β) (Matrix.{u1, u1, u3} n n β) (instHSMul.{u3, max u3 u1} (MulOpposite.{u3} β) (Matrix.{u1, u1, u3} n n β) (Matrix.smul.{u3, u1, u1, u3} n n (MulOpposite.{u3} β) β (Mul.toHasOppositeSMul.{u3} β _inst_2))) (MulOpposite.op.{u3} β (f r)) (Matrix.map.{u2, u3, u1, u1} n n α β A f)))
Case conversion may be inaccurate. Consider using '#align matrix.map_op_smul' Matrix.map_op_smul'ₓ'. -/
/-- The scalar action via `has_mul.to_has_opposite_smul` is transformed by the same map as the
elements of the matrix, when `f` preserves multiplication. -/
theorem map_op_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α)
    (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) :
    (MulOpposite.op r • A).map f = MulOpposite.op (f r) • A.map f :=
  ext fun _ _ => hf _ _
#align matrix.map_op_smul' Matrix.map_op_smul'

/- warning: is_smul_regular.matrix -> IsSMulRegular.matrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} {S : Type.{u4}} [_inst_1 : SMul.{u3, u4} R S] {k : R}, (IsSMulRegular.{u3, u4} R S _inst_1 k) -> (IsSMulRegular.{u3, max u1 u2 u4} R (Matrix.{u1, u2, u4} m n S) (Matrix.hasSmul.{u4, u1, u2, u3} m n R S _inst_1) k)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u4}} {S : Type.{u3}} [_inst_1 : SMul.{u4, u3} R S] {k : R}, (IsSMulRegular.{u4, u3} R S _inst_1 k) -> (IsSMulRegular.{u4, max (max u3 u2) u1} R (Matrix.{u1, u2, u3} m n S) (Matrix.smul.{u3, u1, u2, u4} m n R S _inst_1) k)
Case conversion may be inaccurate. Consider using '#align is_smul_regular.matrix IsSMulRegular.matrixₓ'. -/
theorem IsSMulRegular.matrix [SMul R S] {k : R} (hk : IsSMulRegular S k) :
    IsSMulRegular (Matrix m n S) k :=
  Pi.IsSMulRegular.pi fun _ => Pi.IsSMulRegular.pi fun _ => hk
#align is_smul_regular.matrix IsSMulRegular.matrix

/- warning: is_left_regular.matrix -> IsLeftRegular.matrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {k : α}, (IsLeftRegular.{u1} α _inst_1 k) -> (IsSMulRegular.{u1, max u2 u3 u1} α (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u1} m n α α (Mul.toSMul.{u1} α _inst_1)) k)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : Mul.{u3} α] {k : α}, (IsLeftRegular.{u3} α _inst_1 k) -> (IsSMulRegular.{u3, max (max u3 u2) u1} α (Matrix.{u1, u2, u3} m n α) (Matrix.smul.{u3, u1, u2, u3} m n α α (Mul.toSMul.{u3} α _inst_1)) k)
Case conversion may be inaccurate. Consider using '#align is_left_regular.matrix IsLeftRegular.matrixₓ'. -/
theorem IsLeftRegular.matrix [Mul α] {k : α} (hk : IsLeftRegular k) :
    IsSMulRegular (Matrix m n α) k :=
  hk.IsSMulRegular.Matrix
#align is_left_regular.matrix IsLeftRegular.matrix

#print Matrix.subsingleton_of_empty_left /-
instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim i⟩
#align matrix.subsingleton_of_empty_left Matrix.subsingleton_of_empty_left
-/

#print Matrix.subsingleton_of_empty_right /-
instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim j⟩
#align matrix.subsingleton_of_empty_right Matrix.subsingleton_of_empty_right
-/

end Matrix

open Matrix

namespace Matrix

section Diagonal

variable [DecidableEq n]

#print Matrix.diagonal /-
/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`.

Note that bundled versions exist as:
* `matrix.diagonal_add_monoid_hom`
* `matrix.diagonal_linear_map`
* `matrix.diagonal_ring_hom`
* `matrix.diagonal_alg_hom`
-/
def diagonal [Zero α] (d : n → α) : Matrix n n α :=
  of fun i j => if i = j then d i else 0
#align matrix.diagonal Matrix.diagonal
-/

/- warning: matrix.diagonal_apply -> Matrix.diagonal_apply is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] (d : n -> α) (i : n) (j : n), Eq.{succ u1} α (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d i j) (ite.{succ u1} α (Eq.{succ u2} n i j) (_inst_1 i j) (d i) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] (d : n -> α) (i : n) (j : n), Eq.{succ u2} α (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d i j) (ite.{succ u2} α (Eq.{succ u1} n i j) (_inst_1 i j) (d i) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_apply Matrix.diagonal_applyₓ'. -/
-- TODO: set as an equation lemma for `diagonal`, see mathlib4#3024
theorem diagonal_apply [Zero α] (d : n → α) (i j) : diagonal d i j = if i = j then d i else 0 :=
  rfl
#align matrix.diagonal_apply Matrix.diagonal_apply

/- warning: matrix.diagonal_apply_eq -> Matrix.diagonal_apply_eq is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] (d : n -> α) (i : n), Eq.{succ u1} α (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d i i) (d i)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] (d : n -> α) (i : n), Eq.{succ u2} α (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d i i) (d i)
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_apply_eq Matrix.diagonal_apply_eqₓ'. -/
@[simp]
theorem diagonal_apply_eq [Zero α] (d : n → α) (i : n) : (diagonal d) i i = d i := by
  simp [diagonal]
#align matrix.diagonal_apply_eq Matrix.diagonal_apply_eq

/- warning: matrix.diagonal_apply_ne -> Matrix.diagonal_apply_ne is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] (d : n -> α) {i : n} {j : n}, (Ne.{succ u2} n i j) -> (Eq.{succ u1} α (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d i j) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] (d : n -> α) {i : n} {j : n}, (Ne.{succ u1} n i j) -> (Eq.{succ u2} α (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d i j) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_apply_ne Matrix.diagonal_apply_neₓ'. -/
@[simp]
theorem diagonal_apply_ne [Zero α] (d : n → α) {i j : n} (h : i ≠ j) : (diagonal d) i j = 0 := by
  simp [diagonal, h]
#align matrix.diagonal_apply_ne Matrix.diagonal_apply_ne

/- warning: matrix.diagonal_apply_ne' -> Matrix.diagonal_apply_ne' is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] (d : n -> α) {i : n} {j : n}, (Ne.{succ u2} n j i) -> (Eq.{succ u1} α (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d i j) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] (d : n -> α) {i : n} {j : n}, (Ne.{succ u1} n j i) -> (Eq.{succ u2} α (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d i j) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_apply_ne' Matrix.diagonal_apply_ne'ₓ'. -/
theorem diagonal_apply_ne' [Zero α] (d : n → α) {i j : n} (h : j ≠ i) : (diagonal d) i j = 0 :=
  diagonal_apply_ne d h.symm
#align matrix.diagonal_apply_ne' Matrix.diagonal_apply_ne'

/- warning: matrix.diagonal_eq_diagonal_iff -> Matrix.diagonal_eq_diagonal_iff is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] {d₁ : n -> α} {d₂ : n -> α}, Iff (Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d₁) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d₂)) (forall (i : n), Eq.{succ u1} α (d₁ i) (d₂ i))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] {d₁ : n -> α} {d₂ : n -> α}, Iff (Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d₁) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d₂)) (forall (i : n), Eq.{succ u2} α (d₁ i) (d₂ i))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_eq_diagonal_iff Matrix.diagonal_eq_diagonal_iffₓ'. -/
@[simp]
theorem diagonal_eq_diagonal_iff [Zero α] {d₁ d₂ : n → α} :
    diagonal d₁ = diagonal d₂ ↔ ∀ i, d₁ i = d₂ i :=
  ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h, fun h => by
    rw [show d₁ = d₂ from funext h]⟩
#align matrix.diagonal_eq_diagonal_iff Matrix.diagonal_eq_diagonal_iff

/- warning: matrix.diagonal_injective -> Matrix.diagonal_injective is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α], Function.Injective.{max (succ u2) (succ u1), succ (max u2 u1)} (n -> α) (Matrix.{u2, u2, u1} n n α) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (n -> α) (Matrix.{u1, u1, u2} n n α) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2)
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_injective Matrix.diagonal_injectiveₓ'. -/
theorem diagonal_injective [Zero α] : Function.Injective (diagonal : (n → α) → Matrix n n α) :=
  fun d₁ d₂ h => funext fun i => by simpa using matrix.ext_iff.mpr h i i
#align matrix.diagonal_injective Matrix.diagonal_injective

/- warning: matrix.diagonal_zero -> Matrix.diagonal_zero is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α], Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (fun (_x : n) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2)))) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 0 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 0 (Zero.zero.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasZero.{u1, u2, u2} n n α _inst_2))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α], Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (fun (_x : n) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2))) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 0 (Zero.toOfNat0.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.zero.{u2, u1, u1} n n α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_zero Matrix.diagonal_zeroₓ'. -/
@[simp]
theorem diagonal_zero [Zero α] : (diagonal fun _ => 0 : Matrix n n α) = 0 :=
  by
  ext
  simp [diagonal]
#align matrix.diagonal_zero Matrix.diagonal_zero

/- warning: matrix.diagonal_transpose -> Matrix.diagonal_transpose is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] (v : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.transpose.{u1, u2, u2} n n α (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 v)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 v)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] (v : n -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.transpose.{u2, u1, u1} n n α (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 v)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 v)
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_transpose Matrix.diagonal_transposeₓ'. -/
@[simp]
theorem diagonal_transpose [Zero α] (v : n → α) : (diagonal v)ᵀ = diagonal v :=
  by
  ext (i j)
  by_cases h : i = j
  · simp [h, transpose]
  · simp [h, transpose, diagonal_apply_ne' _ h]
#align matrix.diagonal_transpose Matrix.diagonal_transpose

/- warning: matrix.diagonal_add -> Matrix.diagonal_add is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : AddZeroClass.{u1} α] (d₁ : n -> α) (d₂ : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHAdd.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasAdd.{u1, u2, u2} n n α (AddZeroClass.toHasAdd.{u1} α _inst_2))) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α _inst_2) d₁) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α _inst_2) d₂)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α _inst_2) (fun (i : n) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_2)) (d₁ i) (d₂ i)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : AddZeroClass.{u2} α] (d₁ : n -> α) (d₂ : n -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHAdd.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.add.{u2, u1, u1} n n α (AddZeroClass.toAdd.{u2} α _inst_2))) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toZero.{u2} α _inst_2) d₁) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toZero.{u2} α _inst_2) d₂)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toZero.{u2} α _inst_2) (fun (i : n) => HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (AddZeroClass.toAdd.{u2} α _inst_2)) (d₁ i) (d₂ i)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_add Matrix.diagonal_addₓ'. -/
@[simp]
theorem diagonal_add [AddZeroClass α] (d₁ d₂ : n → α) :
    diagonal d₁ + diagonal d₂ = diagonal fun i => d₁ i + d₂ i := by
  ext (i j) <;> by_cases h : i = j <;> simp [h]
#align matrix.diagonal_add Matrix.diagonal_add

/- warning: matrix.diagonal_smul -> Matrix.diagonal_smul is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Monoid.{u3} R] [_inst_3 : AddMonoid.{u1} α] [_inst_4 : DistribMulAction.{u3, u1} R α _inst_2 _inst_3] (r : R) (d : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_3)) (SMul.smul.{u3, max u2 u1} R (n -> α) (Function.hasSMul.{u2, u3, u1} n R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_3)) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α _inst_3) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_2 _inst_3 _inst_4)))) r d)) (SMul.smul.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Matrix.hasSmul.{u1, u2, u2, u3} n n R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_3)) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α _inst_3) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_2 _inst_3 _inst_4)))) r (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_3)) d))
but is expected to have type
  forall {n : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Monoid.{u2} R] [_inst_3 : AddMonoid.{u3} α] [_inst_4 : DistribMulAction.{u2, u3} R α _inst_2 _inst_3] (r : R) (d : n -> α), Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} n n α) (Matrix.diagonal.{u3, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddMonoid.toZero.{u3} α _inst_3) (HSMul.hSMul.{u2, max u3 u1, max u3 u1} R (n -> α) (n -> α) (instHSMul.{u2, max u3 u1} R (n -> α) (Pi.instSMul.{u1, u3, u2} n R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.4412 : n) => α) (fun (i : n) => SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α _inst_3) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α _inst_3) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_2 _inst_3 _inst_4))))) r d)) (HSMul.hSMul.{u2, max u1 u3, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Matrix.{u1, u1, u3} n n α) (instHSMul.{u2, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Matrix.smul.{u3, u1, u1, u2} n n R α (SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α _inst_3) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α _inst_3) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_2 _inst_3 _inst_4))))) r (Matrix.diagonal.{u3, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddMonoid.toZero.{u3} α _inst_3) d))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_smul Matrix.diagonal_smulₓ'. -/
@[simp]
theorem diagonal_smul [Monoid R] [AddMonoid α] [DistribMulAction R α] (r : R) (d : n → α) :
    diagonal (r • d) = r • diagonal d := by ext (i j) <;> by_cases h : i = j <;> simp [h]
#align matrix.diagonal_smul Matrix.diagonal_smul

variable (n α)

#print Matrix.diagonalAddMonoidHom /-
/-- `matrix.diagonal` as an `add_monoid_hom`. -/
@[simps]
def diagonalAddMonoidHom [AddZeroClass α] : (n → α) →+ Matrix n n α
    where
  toFun := diagonal
  map_zero' := diagonal_zero
  map_add' x y := (diagonal_add x y).symm
#align matrix.diagonal_add_monoid_hom Matrix.diagonalAddMonoidHom
-/

variable (R)

#print Matrix.diagonalLinearMap /-
/-- `matrix.diagonal` as a `linear_map`. -/
@[simps]
def diagonalLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : (n → α) →ₗ[R] Matrix n n α :=
  { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }
#align matrix.diagonal_linear_map Matrix.diagonalLinearMap
-/

variable {n α R}

/- warning: matrix.diagonal_map -> Matrix.diagonal_map is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u3} n] [_inst_2 : Zero.{u1} α] [_inst_3 : Zero.{u2} β] {f : α -> β}, (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2)))) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (forall {d : n -> α}, Eq.{succ (max u3 u2)} (Matrix.{u3, u3, u2} n n β) (Matrix.map.{u1, u2, u3, u3} n n α β (Matrix.diagonal.{u1, u3} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d) f) (Matrix.diagonal.{u2, u3} n β (fun (a : n) (b : n) => _inst_1 a b) _inst_3 (fun (m : n) => f (d m))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : Zero.{u3} β] {f : α -> β}, (Eq.{succ u3} β (f (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2))) (OfNat.ofNat.{u3} β 0 (Zero.toOfNat0.{u3} β _inst_3))) -> (forall {d : n -> α}, Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} n n β) (Matrix.map.{u2, u3, u1, u1} n n α β (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 d) f) (Matrix.diagonal.{u3, u1} n β (fun (a : n) (b : n) => _inst_1 a b) _inst_3 (fun (m : n) => f (d m))))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_map Matrix.diagonal_mapₓ'. -/
@[simp]
theorem diagonal_map [Zero α] [Zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
    (diagonal d).map f = diagonal fun m => f (d m) :=
  by
  ext
  simp only [diagonal_apply, map_apply]
  split_ifs <;> simp [h]
#align matrix.diagonal_map Matrix.diagonal_map

/- warning: matrix.diagonal_conj_transpose -> Matrix.diagonal_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : AddMonoid.{u1} α] [_inst_3 : StarAddMonoid.{u1} α _inst_2] (v : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.conjTranspose.{u1, u2, u2} n n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_2 _inst_3)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_2)) v)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_2)) (Star.star.{max u2 u1} (n -> α) (Pi.hasStar.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_2 _inst_3))) v))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : AddMonoid.{u2} α] [_inst_3 : StarAddMonoid.{u2} α _inst_2] (v : n -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.conjTranspose.{u2, u1, u1} n n α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α _inst_2 _inst_3)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddMonoid.toZero.{u2} α _inst_2) v)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddMonoid.toZero.{u2} α _inst_2) (Star.star.{max u1 u2} (n -> α) (Pi.instStarForAll.{u1, u2} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α _inst_2 _inst_3))) v))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_conj_transpose Matrix.diagonal_conjTransposeₓ'. -/
@[simp]
theorem diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n → α) :
    (diagonal v)ᴴ = diagonal (star v) :=
  by
  rw [conj_transpose, diagonal_transpose, diagonal_map (star_zero _)]
  rfl
#align matrix.diagonal_conj_transpose Matrix.diagonal_conjTranspose

section One

variable [Zero α] [One α]

instance : One (Matrix n n α) :=
  ⟨diagonal fun _ => 1⟩

/- warning: matrix.diagonal_one -> Matrix.diagonal_one is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α], Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (fun (_x : n) => OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_3)))) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α], Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (fun (_x : n) => OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_3))) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_one Matrix.diagonal_oneₓ'. -/
@[simp]
theorem diagonal_one : (diagonal fun _ => 1 : Matrix n n α) = 1 :=
  rfl
#align matrix.diagonal_one Matrix.diagonal_one

/- warning: matrix.one_apply -> Matrix.one_apply is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α] {i : n} {j : n}, Eq.{succ u1} α (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) i j) (ite.{succ u1} α (Eq.{succ u2} n i j) (_inst_1 i j) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_3))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α] {i : n} {j : n}, Eq.{succ u2} α (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)) i j) (ite.{succ u2} α (Eq.{succ u1} n i j) (_inst_1 i j) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_3)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.one_apply Matrix.one_applyₓ'. -/
theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
  rfl
#align matrix.one_apply Matrix.one_apply

/- warning: matrix.one_apply_eq -> Matrix.one_apply_eq is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α] (i : n), Eq.{succ u1} α (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) i i) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_3)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α] (i : n), Eq.{succ u2} α (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)) i i) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_3))
Case conversion may be inaccurate. Consider using '#align matrix.one_apply_eq Matrix.one_apply_eqₓ'. -/
@[simp]
theorem one_apply_eq (i) : (1 : Matrix n n α) i i = 1 :=
  diagonal_apply_eq _ i
#align matrix.one_apply_eq Matrix.one_apply_eq

/- warning: matrix.one_apply_ne -> Matrix.one_apply_ne is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α] {i : n} {j : n}, (Ne.{succ u2} n i j) -> (Eq.{succ u1} α (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) i j) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α] {i : n} {j : n}, (Ne.{succ u1} n i j) -> (Eq.{succ u2} α (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)) i j) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.one_apply_ne Matrix.one_apply_neₓ'. -/
@[simp]
theorem one_apply_ne {i j} : i ≠ j → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne _
#align matrix.one_apply_ne Matrix.one_apply_ne

/- warning: matrix.one_apply_ne' -> Matrix.one_apply_ne' is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α] {i : n} {j : n}, (Ne.{succ u2} n j i) -> (Eq.{succ u1} α (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) i j) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α] {i : n} {j : n}, (Ne.{succ u1} n j i) -> (Eq.{succ u2} α (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)) i j) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.one_apply_ne' Matrix.one_apply_ne'ₓ'. -/
theorem one_apply_ne' {i j} : j ≠ i → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne' _
#align matrix.one_apply_ne' Matrix.one_apply_ne'

/- warning: matrix.map_one -> Matrix.map_one is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u3} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α] [_inst_4 : Zero.{u2} β] [_inst_5 : One.{u2} β] (f : α -> β), (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_2)))) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_4)))) -> (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_3)))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_5)))) -> (Eq.{succ (max u3 u2)} (Matrix.{u3, u3, u2} n n β) (Matrix.map.{u1, u2, u3, u3} n n α β (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} n n α) 1 (OfNat.mk.{max u3 u1} (Matrix.{u3, u3, u1} n n α) 1 (One.one.{max u3 u1} (Matrix.{u3, u3, u1} n n α) (Matrix.hasOne.{u1, u3} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)))) f) (OfNat.ofNat.{max u3 u2} (Matrix.{u3, u3, u2} n n β) 1 (OfNat.mk.{max u3 u2} (Matrix.{u3, u3, u2} n n β) 1 (One.one.{max u3 u2} (Matrix.{u3, u3, u2} n n β) (Matrix.hasOne.{u2, u3} n β (fun (a : n) (b : n) => _inst_1 a b) _inst_4 _inst_5)))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α] [_inst_4 : Zero.{u3} β] [_inst_5 : One.{u3} β] (f : α -> β), (Eq.{succ u3} β (f (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_2))) (OfNat.ofNat.{u3} β 0 (Zero.toOfNat0.{u3} β _inst_4))) -> (Eq.{succ u3} β (f (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_3))) (OfNat.ofNat.{u3} β 1 (One.toOfNat1.{u3} β _inst_5))) -> (Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} n n β) (Matrix.map.{u2, u3, u1, u1} n n α β (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3))) f) (OfNat.ofNat.{max u3 u1} (Matrix.{u1, u1, u3} n n β) 1 (One.toOfNat1.{max u3 u1} (Matrix.{u1, u1, u3} n n β) (Matrix.one.{u3, u1} n β (fun (a : n) (b : n) => _inst_1 a b) _inst_4 _inst_5))))
Case conversion may be inaccurate. Consider using '#align matrix.map_one Matrix.map_oneₓ'. -/
@[simp]
theorem map_one [Zero β] [One β] (f : α → β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    (1 : Matrix n n α).map f = (1 : Matrix n n β) :=
  by
  ext
  simp only [one_apply, map_apply]
  split_ifs <;> simp [h₀, h₁]
#align matrix.map_one Matrix.map_one

/- warning: matrix.one_eq_pi_single -> Matrix.one_eq_pi_single is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α] {i : n} {j : n}, Eq.{succ u1} α (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3) i j) (Pi.single.{u2, u1} n (fun {j : n} => α) (fun (a : n) (b : n) => _inst_1 a b) (fun (i : n) => _inst_2) i (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_3))) j)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α] {i : n} {j : n}, Eq.{succ u2} α (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)) i j) (Pi.single.{u1, u2} n (fun (j : n) => α) (fun (a : n) (b : n) => _inst_1 a b) (fun (i : n) => _inst_2) i (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Data.Matrix.Basic._hyg.5263 : n) => α) i) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Data.Matrix.Basic._hyg.5263 : n) => α) i) _inst_3)) j)
Case conversion may be inaccurate. Consider using '#align matrix.one_eq_pi_single Matrix.one_eq_pi_singleₓ'. -/
theorem one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single i 1 j := by
  simp only [one_apply, Pi.single_apply, eq_comm] <;> congr
#align matrix.one_eq_pi_single Matrix.one_eq_pi_single

-- deal with decidable_eq
end One

section Numeral

/- warning: matrix.bit0_apply -> Matrix.bit0_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_2 : Add.{u1} α] (M : Matrix.{u2, u2, u1} m m α) (i : m) (j : m), Eq.{succ u1} α (bit0.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasAdd.{u1, u2, u2} m m α _inst_2) M i j) (bit0.{u1} α _inst_2 (M i j))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_2 : Add.{u2} α] (M : Matrix.{u1, u1, u2} m m α) (i : m) (j : m), Eq.{succ u2} α (bit0.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.add.{u2, u1, u1} m m α _inst_2) M i j) (bit0.{u2} α _inst_2 (M i j))
Case conversion may be inaccurate. Consider using '#align matrix.bit0_apply Matrix.bit0_applyₓ'. -/
@[simp]
theorem bit0_apply [Add α] (M : Matrix m m α) (i : m) (j : m) : (bit0 M) i j = bit0 (M i j) :=
  rfl
#align matrix.bit0_apply Matrix.bit0_apply

variable [AddZeroClass α] [One α]

/- warning: matrix.bit1_apply -> Matrix.bit1_apply is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : AddZeroClass.{u1} α] [_inst_3 : One.{u1} α] (M : Matrix.{u2, u2, u1} n n α) (i : n) (j : n), Eq.{succ u1} α (bit1.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α _inst_2) _inst_3) (Matrix.hasAdd.{u1, u2, u2} n n α (AddZeroClass.toHasAdd.{u1} α _inst_2)) M i j) (ite.{succ u1} α (Eq.{succ u2} n i j) (_inst_1 i j) (bit1.{u1} α _inst_3 (AddZeroClass.toHasAdd.{u1} α _inst_2) (M i j)) (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_2) (M i j)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : AddZeroClass.{u2} α] [_inst_3 : One.{u2} α] (M : Matrix.{u1, u1, u2} n n α) (i : n) (j : n), Eq.{succ u2} α (bit1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toZero.{u2} α _inst_2) _inst_3) (Matrix.add.{u2, u1, u1} n n α (AddZeroClass.toAdd.{u2} α _inst_2)) M i j) (ite.{succ u2} α (Eq.{succ u1} n i j) (_inst_1 i j) (bit1.{u2} α _inst_3 (AddZeroClass.toAdd.{u2} α _inst_2) (M i j)) (bit0.{u2} α (AddZeroClass.toAdd.{u2} α _inst_2) (M i j)))
Case conversion may be inaccurate. Consider using '#align matrix.bit1_apply Matrix.bit1_applyₓ'. -/
theorem bit1_apply (M : Matrix n n α) (i : n) (j : n) :
    (bit1 M) i j = if i = j then bit1 (M i j) else bit0 (M i j) := by
  dsimp [bit1] <;> by_cases h : i = j <;> simp [h]
#align matrix.bit1_apply Matrix.bit1_apply

/- warning: matrix.bit1_apply_eq -> Matrix.bit1_apply_eq is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : AddZeroClass.{u1} α] [_inst_3 : One.{u1} α] (M : Matrix.{u2, u2, u1} n n α) (i : n), Eq.{succ u1} α (bit1.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α _inst_2) _inst_3) (Matrix.hasAdd.{u1, u2, u2} n n α (AddZeroClass.toHasAdd.{u1} α _inst_2)) M i i) (bit1.{u1} α _inst_3 (AddZeroClass.toHasAdd.{u1} α _inst_2) (M i i))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : AddZeroClass.{u2} α] [_inst_3 : One.{u2} α] (M : Matrix.{u1, u1, u2} n n α) (i : n), Eq.{succ u2} α (bit1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toZero.{u2} α _inst_2) _inst_3) (Matrix.add.{u2, u1, u1} n n α (AddZeroClass.toAdd.{u2} α _inst_2)) M i i) (bit1.{u2} α _inst_3 (AddZeroClass.toAdd.{u2} α _inst_2) (M i i))
Case conversion may be inaccurate. Consider using '#align matrix.bit1_apply_eq Matrix.bit1_apply_eqₓ'. -/
@[simp]
theorem bit1_apply_eq (M : Matrix n n α) (i : n) : (bit1 M) i i = bit1 (M i i) := by
  simp [bit1_apply]
#align matrix.bit1_apply_eq Matrix.bit1_apply_eq

/- warning: matrix.bit1_apply_ne -> Matrix.bit1_apply_ne is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : AddZeroClass.{u1} α] [_inst_3 : One.{u1} α] (M : Matrix.{u2, u2, u1} n n α) {i : n} {j : n}, (Ne.{succ u2} n i j) -> (Eq.{succ u1} α (bit1.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α _inst_2) _inst_3) (Matrix.hasAdd.{u1, u2, u2} n n α (AddZeroClass.toHasAdd.{u1} α _inst_2)) M i j) (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α _inst_2) (M i j)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : AddZeroClass.{u2} α] [_inst_3 : One.{u2} α] (M : Matrix.{u1, u1, u2} n n α) {i : n} {j : n}, (Ne.{succ u1} n i j) -> (Eq.{succ u2} α (bit1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toZero.{u2} α _inst_2) _inst_3) (Matrix.add.{u2, u1, u1} n n α (AddZeroClass.toAdd.{u2} α _inst_2)) M i j) (bit0.{u2} α (AddZeroClass.toAdd.{u2} α _inst_2) (M i j)))
Case conversion may be inaccurate. Consider using '#align matrix.bit1_apply_ne Matrix.bit1_apply_neₓ'. -/
@[simp]
theorem bit1_apply_ne (M : Matrix n n α) {i j : n} (h : i ≠ j) : (bit1 M) i j = bit0 (M i j) := by
  simp [bit1_apply, h]
#align matrix.bit1_apply_ne Matrix.bit1_apply_ne

end Numeral

end Diagonal

section Diag

#print Matrix.diag /-
/-- The diagonal of a square matrix. -/
@[simp]
def diag (A : Matrix n n α) (i : n) : α :=
  A i i
#align matrix.diag Matrix.diag
-/

/- warning: matrix.diag_diagonal -> Matrix.diag_diagonal is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] (a : n -> α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 a)) a
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] (a : n -> α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 a)) a
Case conversion may be inaccurate. Consider using '#align matrix.diag_diagonal Matrix.diag_diagonalₓ'. -/
@[simp]
theorem diag_diagonal [DecidableEq n] [Zero α] (a : n → α) : diag (diagonal a) = a :=
  funext <| @diagonal_apply_eq _ _ _ _ a
#align matrix.diag_diagonal Matrix.diag_diagonal

/- warning: matrix.diag_transpose -> Matrix.diag_transpose is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} (A : Matrix.{u2, u2, u1} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Matrix.transpose.{u1, u2, u2} n n α A)) (Matrix.diag.{u1, u2} n α A)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} (A : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (Matrix.transpose.{u2, u1, u1} n n α A)) (Matrix.diag.{u2, u1} n α A)
Case conversion may be inaccurate. Consider using '#align matrix.diag_transpose Matrix.diag_transposeₓ'. -/
@[simp]
theorem diag_transpose (A : Matrix n n α) : diag Aᵀ = diag A :=
  rfl
#align matrix.diag_transpose Matrix.diag_transpose

/- warning: matrix.diag_zero -> Matrix.diag_zero is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α], Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 0 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 0 (Zero.zero.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasZero.{u1, u2, u2} n n α _inst_1))))) (OfNat.ofNat.{max u2 u1} (n -> α) 0 (OfNat.mk.{max u2 u1} (n -> α) 0 (Zero.zero.{max u2 u1} (n -> α) (Pi.instZero.{u2, u1} n (fun (i : n) => α) (fun (i : n) => _inst_1)))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α], Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 0 (Zero.toOfNat0.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.zero.{u2, u1, u1} n n α _inst_1)))) (OfNat.ofNat.{max u2 u1} (n -> α) 0 (Zero.toOfNat0.{max u2 u1} (n -> α) (Pi.instZero.{u1, u2} n (fun (i : n) => α) (fun (i : n) => _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.diag_zero Matrix.diag_zeroₓ'. -/
@[simp]
theorem diag_zero [Zero α] : diag (0 : Matrix n n α) = 0 :=
  rfl
#align matrix.diag_zero Matrix.diag_zero

/- warning: matrix.diag_add -> Matrix.diag_add is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Add.{u1} α] (A : Matrix.{u2, u2, u1} n n α) (B : Matrix.{u2, u2, u1} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHAdd.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasAdd.{u1, u2, u2} n n α _inst_1)) A B)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (n -> α) (n -> α) (n -> α) (instHAdd.{max u2 u1} (n -> α) (Pi.instAdd.{u2, u1} n (fun (i : n) => α) (fun (i : n) => _inst_1))) (Matrix.diag.{u1, u2} n α A) (Matrix.diag.{u1, u2} n α B))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Add.{u2} α] (A : Matrix.{u1, u1, u2} n n α) (B : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHAdd.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.add.{u2, u1, u1} n n α _inst_1)) A B)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (n -> α) (n -> α) (n -> α) (instHAdd.{max u2 u1} (n -> α) (Pi.instAdd.{u1, u2} n (fun (i : n) => α) (fun (i : n) => _inst_1))) (Matrix.diag.{u2, u1} n α A) (Matrix.diag.{u2, u1} n α B))
Case conversion may be inaccurate. Consider using '#align matrix.diag_add Matrix.diag_addₓ'. -/
@[simp]
theorem diag_add [Add α] (A B : Matrix n n α) : diag (A + B) = diag A + diag B :=
  rfl
#align matrix.diag_add Matrix.diag_add

/- warning: matrix.diag_sub -> Matrix.diag_sub is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Sub.{u1} α] (A : Matrix.{u2, u2, u1} n n α) (B : Matrix.{u2, u2, u1} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHSub.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasSub.{u1, u2, u2} n n α _inst_1)) A B)) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (n -> α) (n -> α) (n -> α) (instHSub.{max u2 u1} (n -> α) (Pi.instSub.{u2, u1} n (fun (i : n) => α) (fun (i : n) => _inst_1))) (Matrix.diag.{u1, u2} n α A) (Matrix.diag.{u1, u2} n α B))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Sub.{u2} α] (A : Matrix.{u1, u1, u2} n n α) (B : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHSub.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.sub.{u2, u1, u1} n n α _inst_1)) A B)) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (n -> α) (n -> α) (n -> α) (instHSub.{max u2 u1} (n -> α) (Pi.instSub.{u1, u2} n (fun (i : n) => α) (fun (i : n) => _inst_1))) (Matrix.diag.{u2, u1} n α A) (Matrix.diag.{u2, u1} n α B))
Case conversion may be inaccurate. Consider using '#align matrix.diag_sub Matrix.diag_subₓ'. -/
@[simp]
theorem diag_sub [Sub α] (A B : Matrix n n α) : diag (A - B) = diag A - diag B :=
  rfl
#align matrix.diag_sub Matrix.diag_sub

/- warning: matrix.diag_neg -> Matrix.diag_neg is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Neg.{u1} α] (A : Matrix.{u2, u2, u1} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Neg.neg.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasNeg.{u1, u2, u2} n n α _inst_1) A)) (Neg.neg.{max u2 u1} (n -> α) (Pi.instNeg.{u2, u1} n (fun (i : n) => α) (fun (i : n) => _inst_1)) (Matrix.diag.{u1, u2} n α A))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Neg.{u2} α] (A : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (Neg.neg.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.neg.{u2, u1, u1} n n α _inst_1) A)) (Neg.neg.{max u2 u1} (n -> α) (Pi.instNeg.{u1, u2} n (fun (i : n) => α) (fun (i : n) => _inst_1)) (Matrix.diag.{u2, u1} n α A))
Case conversion may be inaccurate. Consider using '#align matrix.diag_neg Matrix.diag_negₓ'. -/
@[simp]
theorem diag_neg [Neg α] (A : Matrix n n α) : diag (-A) = -diag A :=
  rfl
#align matrix.diag_neg Matrix.diag_neg

/- warning: matrix.diag_smul -> Matrix.diag_smul is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : SMul.{u3, u1} R α] (r : R) (A : Matrix.{u2, u2, u1} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (SMul.smul.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Matrix.hasSmul.{u1, u2, u2, u3} n n R α _inst_1) r A)) (SMul.smul.{u3, max u2 u1} R (n -> α) (Function.hasSMul.{u2, u3, u1} n R α _inst_1) r (Matrix.diag.{u1, u2} n α A))
but is expected to have type
  forall {n : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} [_inst_1 : SMul.{u2, u3} R α] (r : R) (A : Matrix.{u1, u1, u3} n n α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.diag.{u3, u1} n α (HSMul.hSMul.{u2, max u3 u1, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Matrix.{u1, u1, u3} n n α) (instHSMul.{u2, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Matrix.smul.{u3, u1, u1, u2} n n R α _inst_1)) r A)) (HSMul.hSMul.{u2, max u1 u3, max u3 u1} R (n -> α) (n -> α) (instHSMul.{u2, max u3 u1} R (n -> α) (Pi.instSMul.{u1, u3, u2} n R (fun (i : n) => α) (fun (i : n) => _inst_1))) r (Matrix.diag.{u3, u1} n α A))
Case conversion may be inaccurate. Consider using '#align matrix.diag_smul Matrix.diag_smulₓ'. -/
@[simp]
theorem diag_smul [SMul R α] (r : R) (A : Matrix n n α) : diag (r • A) = r • diag A :=
  rfl
#align matrix.diag_smul Matrix.diag_smul

/- warning: matrix.diag_one -> Matrix.diag_one is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α], Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3))))) (OfNat.ofNat.{max u2 u1} (n -> α) 1 (OfNat.mk.{max u2 u1} (n -> α) 1 (One.one.{max u2 u1} (n -> α) (Pi.instOne.{u2, u1} n (fun (i : n) => α) (fun (i : n) => _inst_3)))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α], Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)))) (OfNat.ofNat.{max u2 u1} (n -> α) 1 (One.toOfNat1.{max u2 u1} (n -> α) (Pi.instOne.{u1, u2} n (fun (i : n) => α) (fun (i : n) => _inst_3))))
Case conversion may be inaccurate. Consider using '#align matrix.diag_one Matrix.diag_oneₓ'. -/
@[simp]
theorem diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : Matrix n n α) = 1 :=
  diag_diagonal _
#align matrix.diag_one Matrix.diag_one

variable (n α)

#print Matrix.diagAddMonoidHom /-
/-- `matrix.diag` as an `add_monoid_hom`. -/
@[simps]
def diagAddMonoidHom [AddZeroClass α] : Matrix n n α →+ n → α
    where
  toFun := diag
  map_zero' := diag_zero
  map_add' := diag_add
#align matrix.diag_add_monoid_hom Matrix.diagAddMonoidHom
-/

variable (R)

#print Matrix.diagLinearMap /-
/-- `matrix.diag` as a `linear_map`. -/
@[simps]
def diagLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : Matrix n n α →ₗ[R] n → α :=
  { diagAddMonoidHom n α with map_smul' := diag_smul }
#align matrix.diag_linear_map Matrix.diagLinearMap
-/

variable {n α R}

/- warning: matrix.diag_map -> Matrix.diag_map is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {A : Matrix.{u3, u3, u1} n n α}, Eq.{max (succ u3) (succ u2)} (n -> β) (Matrix.diag.{u2, u3} n β (Matrix.map.{u1, u2, u3, u3} n n α β A f)) (Function.comp.{succ u3, succ u1, succ u2} n α β f (Matrix.diag.{u1, u3} n α A))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {f : α -> β} {A : Matrix.{u1, u1, u2} n n α}, Eq.{max (succ u3) (succ u1)} (n -> β) (Matrix.diag.{u3, u1} n β (Matrix.map.{u2, u3, u1, u1} n n α β A f)) (Function.comp.{succ u1, succ u2, succ u3} n α β f (Matrix.diag.{u2, u1} n α A))
Case conversion may be inaccurate. Consider using '#align matrix.diag_map Matrix.diag_mapₓ'. -/
theorem diag_map {f : α → β} {A : Matrix n n α} : diag (A.map f) = f ∘ diag A :=
  rfl
#align matrix.diag_map Matrix.diag_map

/- warning: matrix.diag_conj_transpose -> Matrix.diag_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1] (A : Matrix.{u2, u2, u1} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Matrix.conjTranspose.{u1, u2, u2} n n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) A)) (Star.star.{max u2 u1} (n -> α) (Pi.hasStar.{u2, u1} n (fun (i : n) => α) (fun (i : n) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2))) (Matrix.diag.{u1, u2} n α A))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u2} α] [_inst_2 : StarAddMonoid.{u2} α _inst_1] (A : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (Matrix.conjTranspose.{u2, u1, u1} n n α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α _inst_1 _inst_2)) A)) (Star.star.{max u1 u2} (n -> α) (Pi.instStarForAll.{u1, u2} n (fun (i : n) => α) (fun (i : n) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α _inst_1 _inst_2))) (Matrix.diag.{u2, u1} n α A))
Case conversion may be inaccurate. Consider using '#align matrix.diag_conj_transpose Matrix.diag_conjTransposeₓ'. -/
@[simp]
theorem diag_conjTranspose [AddMonoid α] [StarAddMonoid α] (A : Matrix n n α) :
    diag Aᴴ = star (diag A) :=
  rfl
#align matrix.diag_conj_transpose Matrix.diag_conjTranspose

/- warning: matrix.diag_list_sum -> Matrix.diag_list_sum is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (l : List.{max u2 u1} (Matrix.{u2, u2, u1} n n α)), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (List.sum.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasAdd.{u1, u2, u2} n n α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.hasZero.{u1, u2, u2} n n α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) l)) (List.sum.{max u2 u1} (n -> α) (Pi.instAdd.{u2, u1} n (fun (i : n) => α) (fun (i : n) => AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Pi.instZero.{u2, u1} n (fun (i : n) => α) (fun (i : n) => AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (List.map.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (n -> α) (Matrix.diag.{u1, u2} n α) l))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u2} α] (l : List.{max u2 u1} (Matrix.{u1, u1, u2} n n α)), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (List.sum.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.add.{u2, u1, u1} n n α (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α _inst_1))) (Matrix.zero.{u2, u1, u1} n n α (AddMonoid.toZero.{u2} α _inst_1)) l)) (List.sum.{max u2 u1} (n -> α) (Pi.instAdd.{u1, u2} n (fun (i : n) => α) (fun (i : n) => AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α _inst_1))) (Pi.instZero.{u1, u2} n (fun (i : n) => α) (fun (i : n) => AddMonoid.toZero.{u2} α _inst_1)) (List.map.{max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} n n α) (n -> α) (Matrix.diag.{u2, u1} n α) l))
Case conversion may be inaccurate. Consider using '#align matrix.diag_list_sum Matrix.diag_list_sumₓ'. -/
@[simp]
theorem diag_list_sum [AddMonoid α] (l : List (Matrix n n α)) : diag l.Sum = (l.map diag).Sum :=
  map_list_sum (diagAddMonoidHom n α) l
#align matrix.diag_list_sum Matrix.diag_list_sum

/- warning: matrix.diag_multiset_sum -> Matrix.diag_multiset_sum is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] (s : Multiset.{max u2 u1} (Matrix.{u2, u2, u1} n n α)), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Multiset.sum.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.addCommMonoid.{u1, u2, u2} n n α _inst_1) s)) (Multiset.sum.{max u2 u1} (n -> α) (Pi.addCommMonoid.{u2, u1} n (fun (i : n) => α) (fun (i : n) => _inst_1)) (Multiset.map.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (n -> α) (Matrix.diag.{u1, u2} n α) s))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} α] (s : Multiset.{max u2 u1} (Matrix.{u1, u1, u2} n n α)), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (Multiset.sum.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.addCommMonoid.{u2, u1, u1} n n α _inst_1) s)) (Multiset.sum.{max u2 u1} (n -> α) (Pi.addCommMonoid.{u1, u2} n (fun (i : n) => α) (fun (i : n) => _inst_1)) (Multiset.map.{max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} n n α) (n -> α) (Matrix.diag.{u2, u1} n α) s))
Case conversion may be inaccurate. Consider using '#align matrix.diag_multiset_sum Matrix.diag_multiset_sumₓ'. -/
@[simp]
theorem diag_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix n n α)) :
    diag s.Sum = (s.map diag).Sum :=
  map_multiset_sum (diagAddMonoidHom n α) s
#align matrix.diag_multiset_sum Matrix.diag_multiset_sum

/- warning: matrix.diag_sum -> Matrix.diag_sum is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} {ι : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} α] (s : Finset.{u3} ι) (f : ι -> (Matrix.{u2, u2, u1} n n α)), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Finset.sum.{max u2 u1, u3} (Matrix.{u2, u2, u1} n n α) ι (Matrix.addCommMonoid.{u1, u2, u2} n n α _inst_1) s (fun (i : ι) => f i))) (Finset.sum.{max u2 u1, u3} (n -> α) ι (Pi.addCommMonoid.{u2, u1} n (fun (i : n) => α) (fun (i : n) => _inst_1)) s (fun (i : ι) => Matrix.diag.{u1, u2} n α (f i)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u3}} {ι : Type.{u2}} [_inst_1 : AddCommMonoid.{u3} α] (s : Finset.{u2} ι) (f : ι -> (Matrix.{u1, u1, u3} n n α)), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.diag.{u3, u1} n α (Finset.sum.{max u1 u3, u2} (Matrix.{u1, u1, u3} n n α) ι (Matrix.addCommMonoid.{u3, u1, u1} n n α _inst_1) s (fun (i : ι) => f i))) (Finset.sum.{max u1 u3, u2} (n -> α) ι (Pi.addCommMonoid.{u1, u3} n (fun (i : n) => α) (fun (i : n) => _inst_1)) s (fun (i : ι) => Matrix.diag.{u3, u1} n α (f i)))
Case conversion may be inaccurate. Consider using '#align matrix.diag_sum Matrix.diag_sumₓ'. -/
@[simp]
theorem diag_sum {ι} [AddCommMonoid α] (s : Finset ι) (f : ι → Matrix n n α) :
    diag (∑ i in s, f i) = ∑ i in s, diag (f i) :=
  map_sum (diagAddMonoidHom n α) f s
#align matrix.diag_sum Matrix.diag_sum

end Diag

section DotProduct

variable [Fintype m] [Fintype n]

#print Matrix.dotProduct /-
/-- `dot_product v w` is the sum of the entrywise products `v i * w i` -/
def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i
#align matrix.dot_product Matrix.dotProduct
-/

-- mathport name: matrix.dot_product
/- The precedence of 72 comes immediately after ` • ` for `has_smul.smul`,
   so that `r₁ • a ⬝ᵥ r₂ • b` is parsed as `(r₁ • a) ⬝ᵥ (r₂ • b)` here. -/
scoped infixl:72 " ⬝ᵥ " => Matrix.dotProduct

/- warning: matrix.dot_product_assoc -> Matrix.dotProduct_assoc is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u3} n] [_inst_3 : NonUnitalSemiring.{u1} α] (u : m -> α) (w : n -> α) (v : Matrix.{u2, u3, u1} m n α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u3} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) (fun (j : n) => Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) u (fun (i : m) => v i j)) w) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) u (fun (i : m) => Matrix.dotProduct.{u1, u3} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) (v i) w))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u1} n] [_inst_3 : NonUnitalSemiring.{u3} α] (u : m -> α) (w : n -> α) (v : Matrix.{u2, u1, u3} m n α), Eq.{succ u3} α (Matrix.dotProduct.{u3, u1} n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (fun (j : n) => Matrix.dotProduct.{u3, u2} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) u (fun (i : m) => v i j)) w) (Matrix.dotProduct.{u3, u2} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) u (fun (i : m) => Matrix.dotProduct.{u3, u1} n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (v i) w))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_assoc Matrix.dotProduct_assocₓ'. -/
theorem dotProduct_assoc [NonUnitalSemiring α] (u : m → α) (w : n → α) (v : Matrix m n α) :
    (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i => v i ⬝ᵥ w := by
  simpa [dot_product, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm
#align matrix.dot_product_assoc Matrix.dotProduct_assoc

/- warning: matrix.dot_product_comm -> Matrix.dotProduct_comm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : AddCommMonoid.{u1} α] [_inst_4 : CommSemigroup.{u1} α] (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_4)) _inst_3 v w) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_4)) _inst_3 w v)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : AddCommMonoid.{u2} α] [_inst_4 : CommSemigroup.{u2} α] (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (Semigroup.toMul.{u2} α (CommSemigroup.toSemigroup.{u2} α _inst_4)) _inst_3 v w) (Matrix.dotProduct.{u2, u1} m α _inst_1 (Semigroup.toMul.{u2} α (CommSemigroup.toSemigroup.{u2} α _inst_4)) _inst_3 w v)
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_comm Matrix.dotProduct_commₓ'. -/
theorem dotProduct_comm [AddCommMonoid α] [CommSemigroup α] (v w : m → α) : v ⬝ᵥ w = w ⬝ᵥ v := by
  simp_rw [dot_product, mul_comm]
#align matrix.dot_product_comm Matrix.dotProduct_comm

/- warning: matrix.dot_product_punit -> Matrix.dotProduct_pUnit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : AddCommMonoid.{u1} α] [_inst_4 : Mul.{u1} α] (v : PUnit.{succ u2} -> α) (w : PUnit.{succ u2} -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} PUnit.{succ u2} α PUnit.fintype.{u2} _inst_4 _inst_3 v w) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_4) (v PUnit.unit.{succ u2}) (w PUnit.unit.{succ u2}))
but is expected to have type
  forall {α : Type.{u2}} [_inst_3 : AddCommMonoid.{u2} α] [_inst_4 : Mul.{u2} α] (v : PUnit.{succ u1} -> α) (w : PUnit.{succ u1} -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} PUnit.{succ u1} α PUnit.fintype.{u1} _inst_4 _inst_3 v w) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_4) (v PUnit.unit.{succ u1}) (w PUnit.unit.{succ u1}))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_punit Matrix.dotProduct_pUnitₓ'. -/
@[simp]
theorem dotProduct_pUnit [AddCommMonoid α] [Mul α] (v w : PUnit → α) : v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩ := by
  simp [dot_product]
#align matrix.dot_product_punit Matrix.dotProduct_pUnit

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] (u v w : m → α) (x y : n → α)

/- warning: matrix.dot_product_zero -> Matrix.dotProduct_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) v (OfNat.ofNat.{max u2 u1} (m -> α) 0 (OfNat.mk.{max u2 u1} (m -> α) 0 (Zero.zero.{max u2 u1} (m -> α) (Pi.instZero.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_3))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_3)))))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) v (OfNat.ofNat.{max u2 u1} (m -> α) 0 (Zero.toOfNat0.{max u2 u1} (m -> α) (Pi.instZero.{u1, u2} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.6393 : m) => α) (fun (i : m) => MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_3)))))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_3))))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_zero Matrix.dotProduct_zeroₓ'. -/
@[simp]
theorem dotProduct_zero : v ⬝ᵥ 0 = 0 := by simp [dot_product]
#align matrix.dot_product_zero Matrix.dotProduct_zero

/- warning: matrix.dot_product_zero' -> Matrix.dotProduct_zero' is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) v (fun (_x : m) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_3)))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_3)))))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) v (fun (_x : m) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_3))))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_3))))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_zero' Matrix.dotProduct_zero'ₓ'. -/
@[simp]
theorem dotProduct_zero' : (v ⬝ᵥ fun _ => 0) = 0 :=
  dotProduct_zero v
#align matrix.dot_product_zero' Matrix.dotProduct_zero'

/- warning: matrix.zero_dot_product -> Matrix.zero_dotProduct is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) (OfNat.ofNat.{max u2 u1} (m -> α) 0 (OfNat.mk.{max u2 u1} (m -> α) 0 (Zero.zero.{max u2 u1} (m -> α) (Pi.instZero.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_3)))))) v) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_3)))))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) (OfNat.ofNat.{max u1 u2} (m -> α) 0 (Zero.toOfNat0.{max u2 u1} (m -> α) (Pi.instZero.{u1, u2} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.6390 : m) => α) (fun (i : m) => MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_3))))) v) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_3))))
Case conversion may be inaccurate. Consider using '#align matrix.zero_dot_product Matrix.zero_dotProductₓ'. -/
@[simp]
theorem zero_dotProduct : 0 ⬝ᵥ v = 0 := by simp [dot_product]
#align matrix.zero_dot_product Matrix.zero_dotProduct

/- warning: matrix.zero_dot_product' -> Matrix.zero_dotProduct' is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) (fun (_x : m) => OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_3))))) v) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_3)))))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) (fun (_x : m) => OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_3)))) v) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_3))))
Case conversion may be inaccurate. Consider using '#align matrix.zero_dot_product' Matrix.zero_dotProduct'ₓ'. -/
@[simp]
theorem zero_dotProduct' : (fun _ => (0 : α)) ⬝ᵥ v = 0 :=
  zero_dotProduct v
#align matrix.zero_dot_product' Matrix.zero_dotProduct'

/- warning: matrix.add_dot_product -> Matrix.add_dotProduct is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocSemiring.{u1} α] (u : m -> α) (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)))) u v) w) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) u w) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) v w))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocSemiring.{u2} α] (u : m -> α) (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_3)))) u v) w) (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_3))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) u w) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) v w))
Case conversion may be inaccurate. Consider using '#align matrix.add_dot_product Matrix.add_dotProductₓ'. -/
@[simp]
theorem add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp [dot_product, add_mul, Finset.sum_add_distrib]
#align matrix.add_dot_product Matrix.add_dotProduct

/- warning: matrix.dot_product_add -> Matrix.dotProduct_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocSemiring.{u1} α] (u : m -> α) (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) u (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)))) v w)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) u v) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) u w))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocSemiring.{u2} α] (u : m -> α) (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) u (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_3)))) v w)) (HAdd.hAdd.{u2, u2, u2} α α α (instHAdd.{u2} α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_3))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) u v) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_3) u w))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_add Matrix.dotProduct_addₓ'. -/
@[simp]
theorem dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp [dot_product, mul_add, Finset.sum_add_distrib]
#align matrix.dot_product_add Matrix.dotProduct_add

/- warning: matrix.sum_elim_dot_product_sum_elim -> Matrix.sum_elim_dotProduct_sum_elim is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u3} n] [_inst_3 : NonUnitalNonAssocSemiring.{u1} α] (u : m -> α) (v : m -> α) (x : n -> α) (y : n -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, max u2 u3} (Sum.{u2, u3} m n) α (Sum.fintype.{u2, u3} m n _inst_1 _inst_2) (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) (Sum.elim.{u2, u3, succ u1} m n α u x) (Sum.elim.{u2, u3, succ u1} m n α v y)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) u v) (Matrix.dotProduct.{u1, u3} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_3) x y))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : Fintype.{u1} m] [_inst_2 : Fintype.{u2} n] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] (u : m -> α) (v : m -> α) (x : n -> α) (y : n -> α), Eq.{succ u3} α (Matrix.dotProduct.{u3, max u2 u1} (Sum.{u1, u2} m n) α (instFintypeSum.{u1, u2} m n _inst_1 _inst_2) (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) (Sum.elim.{u1, u2, succ u3} m n α u x) (Sum.elim.{u1, u2, succ u3} m n α v y)) (HAdd.hAdd.{u3, u3, u3} α α α (instHAdd.{u3} α (Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) (Matrix.dotProduct.{u3, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) u v) (Matrix.dotProduct.{u3, u2} n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) x y))
Case conversion may be inaccurate. Consider using '#align matrix.sum_elim_dot_product_sum_elim Matrix.sum_elim_dotProduct_sum_elimₓ'. -/
@[simp]
theorem sum_elim_dotProduct_sum_elim : Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dot_product]
#align matrix.sum_elim_dot_product_sum_elim Matrix.sum_elim_dotProduct_sum_elim

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocSemiringDecidable

variable [DecidableEq m] [NonUnitalNonAssocSemiring α] (u v w : m → α)

/- warning: matrix.diagonal_dot_product -> Matrix.diagonal_dotProduct is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α) (w : m -> α) (i : m), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_4) (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_4)) v i) w) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4))) (v i) (w i))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] [_inst_4 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α) (w : m -> α) (i : m), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_4) (Matrix.diagonal.{u2, u1} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_4)) v i) w) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4)) (v i) (w i))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_dot_product Matrix.diagonal_dotProductₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (j «expr ≠ » i) -/
@[simp]
theorem diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v i * w i :=
  by
  have : ∀ (j) (_ : j ≠ i), diagonal v i j * w j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
#align matrix.diagonal_dot_product Matrix.diagonal_dotProduct

/- warning: matrix.dot_product_diagonal -> Matrix.dotProduct_diagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α) (w : m -> α) (i : m), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_4) v (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_4)) w i)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4))) (v i) (w i))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] [_inst_4 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α) (w : m -> α) (i : m), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_4) v (Matrix.diagonal.{u2, u1} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_4)) w i)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4)) (v i) (w i))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_diagonal Matrix.dotProduct_diagonalₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (j «expr ≠ » i) -/
@[simp]
theorem dotProduct_diagonal (i : m) : v ⬝ᵥ diagonal w i = v i * w i :=
  by
  have : ∀ (j) (_ : j ≠ i), v j * diagonal w i j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
#align matrix.dot_product_diagonal Matrix.dotProduct_diagonal

/- warning: matrix.dot_product_diagonal' -> Matrix.dotProduct_diagonal' is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α) (w : m -> α) (i : m), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_4) v (fun (j : m) => Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_4)) w j i)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4))) (v i) (w i))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] [_inst_4 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α) (w : m -> α) (i : m), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_4) v (fun (j : m) => Matrix.diagonal.{u2, u1} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_4)) w j i)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4)) (v i) (w i))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_diagonal' Matrix.dotProduct_diagonal'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (j «expr ≠ » i) -/
@[simp]
theorem dotProduct_diagonal' (i : m) : (v ⬝ᵥ fun j => diagonal w j i) = v i * w i :=
  by
  have : ∀ (j) (_ : j ≠ i), v j * diagonal w j i = 0 := fun j hij => by
    simp [diagonal_apply_ne _ hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
#align matrix.dot_product_diagonal' Matrix.dotProduct_diagonal'

/- warning: matrix.single_dot_product -> Matrix.single_dotProduct is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α) (x : α) (i : m), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_4) (Pi.single.{u2, u1} m (fun (i : m) => α) (fun (a : m) (b : m) => _inst_3 a b) (fun (i : m) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_4)) i x) v) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4))) x (v i))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] [_inst_4 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α) (x : α) (i : m), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_4) (Pi.single.{u1, u2} m (fun (i : m) => α) (fun (a : m) (b : m) => _inst_3 a b) (fun (i : m) => MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_4)) i x) v) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4)) x (v i))
Case conversion may be inaccurate. Consider using '#align matrix.single_dot_product Matrix.single_dotProductₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (j «expr ≠ » i) -/
@[simp]
theorem single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ v = x * v i :=
  by
  have : ∀ (j) (_ : j ≠ i), Pi.single i x j * v j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
#align matrix.single_dot_product Matrix.single_dotProduct

/- warning: matrix.dot_product_single -> Matrix.dotProduct_single is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : NonUnitalNonAssocSemiring.{u1} α] (v : m -> α) (x : α) (i : m), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_4) v (Pi.single.{u2, u1} m (fun (ᾰ : m) => α) (fun (a : m) (b : m) => _inst_3 a b) (fun (i : m) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_4)) i x)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_4))) (v i) x)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] [_inst_4 : NonUnitalNonAssocSemiring.{u2} α] (v : m -> α) (x : α) (i : m), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_4) v (Pi.single.{u1, u2} m (fun (ᾰ : m) => α) (fun (a : m) (b : m) => _inst_3 a b) (fun (i : m) => MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_4)) i x)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_4)) (v i) x)
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_single Matrix.dotProduct_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (j «expr ≠ » i) -/
@[simp]
theorem dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x :=
  by
  have : ∀ (j) (_ : j ≠ i), v j * Pi.single i x j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp
#align matrix.dot_product_single Matrix.dotProduct_single

end NonUnitalNonAssocSemiringDecidable

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] (u v w : m → α)

/- warning: matrix.neg_dot_product -> Matrix.neg_dotProduct is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocRing.{u1} α] (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) (Neg.neg.{max u2 u1} (m -> α) (Pi.instNeg.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3))))) v) w) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) v w))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocRing.{u2} α] (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (Neg.neg.{max u2 u1} (m -> α) (Pi.instNeg.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α _inst_3))))))) v) w) (Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α _inst_3)))))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) v w))
Case conversion may be inaccurate. Consider using '#align matrix.neg_dot_product Matrix.neg_dotProductₓ'. -/
@[simp]
theorem neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w) := by simp [dot_product]
#align matrix.neg_dot_product Matrix.neg_dotProduct

/- warning: matrix.dot_product_neg -> Matrix.dotProduct_neg is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocRing.{u1} α] (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) v (Neg.neg.{max u2 u1} (m -> α) (Pi.instNeg.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3))))) w)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) v w))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocRing.{u2} α] (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) v (Neg.neg.{max u2 u1} (m -> α) (Pi.instNeg.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α _inst_3))))))) w)) (Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α _inst_3)))))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) v w))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_neg Matrix.dotProduct_negₓ'. -/
@[simp]
theorem dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w) := by simp [dot_product]
#align matrix.dot_product_neg Matrix.dotProduct_neg

/- warning: matrix.sub_dot_product -> Matrix.sub_dotProduct is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocRing.{u1} α] (u : m -> α) (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHSub.{max u2 u1} (m -> α) (Pi.instSub.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)))))) u v) w) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3))))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) u w) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) v w))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocRing.{u2} α] (u : m -> α) (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHSub.{max u2 u1} (m -> α) (Pi.instSub.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α _inst_3)))))) u v) w) (HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α _inst_3))))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) u w) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) v w))
Case conversion may be inaccurate. Consider using '#align matrix.sub_dot_product Matrix.sub_dotProductₓ'. -/
@[simp]
theorem sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w := by simp [sub_eq_add_neg]
#align matrix.sub_dot_product Matrix.sub_dotProduct

/- warning: matrix.dot_product_sub -> Matrix.dotProduct_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalNonAssocRing.{u1} α] (u : m -> α) (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) u (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHSub.{max u2 u1} (m -> α) (Pi.instSub.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)))))) v w)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3))))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) u v) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_3)) u w))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalNonAssocRing.{u2} α] (u : m -> α) (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) u (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHSub.{max u2 u1} (m -> α) (Pi.instSub.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α _inst_3)))))) v w)) (HSub.hSub.{u2, u2, u2} α α α (instHSub.{u2} α (SubNegMonoid.toSub.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (NonUnitalNonAssocRing.toAddCommGroup.{u2} α _inst_3))))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) u v) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocRing.toMul.{u2} α _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) u w))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_sub Matrix.dotProduct_subₓ'. -/
@[simp]
theorem dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by simp [sub_eq_add_neg]
#align matrix.dot_product_sub Matrix.dotProduct_sub

end NonUnitalNonAssocRing

section DistribMulAction

variable [Monoid R] [Mul α] [AddCommMonoid α] [DistribMulAction R α]

/- warning: matrix.smul_dot_product -> Matrix.smul_dotProduct is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : Monoid.{u3} R] [_inst_4 : Mul.{u1} α] [_inst_5 : AddCommMonoid.{u1} α] [_inst_6 : DistribMulAction.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5)] [_inst_7 : IsScalarTower.{u3, u1, u1} R α α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5) _inst_6))) (Mul.toSMul.{u1} α _inst_4) (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5) _inst_6)))] (x : R) (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 _inst_4 _inst_5 (SMul.smul.{u3, max u2 u1} R (m -> α) (Function.hasSMul.{u2, u3, u1} m R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5) _inst_6)))) x v) w) (SMul.smul.{u3, u1} R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5) _inst_6))) x (Matrix.dotProduct.{u1, u2} m α _inst_1 _inst_4 _inst_5 v w))
but is expected to have type
  forall {m : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} [_inst_1 : Fintype.{u1} m] [_inst_3 : Monoid.{u2} R] [_inst_4 : Mul.{u3} α] [_inst_5 : AddCommMonoid.{u3} α] [_inst_6 : DistribMulAction.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5)] [_inst_7 : IsScalarTower.{u2, u3, u3} R α α (SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5) _inst_6))) (Mul.toSMul.{u3} α _inst_4) (SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5) _inst_6)))] (x : R) (v : m -> α) (w : m -> α), Eq.{succ u3} α (Matrix.dotProduct.{u3, u1} m α _inst_1 _inst_4 _inst_5 (HSMul.hSMul.{u2, max u3 u1, max u3 u1} R (m -> α) (m -> α) (instHSMul.{u2, max u3 u1} R (m -> α) (Pi.instSMul.{u1, u3, u2} m R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.8840 : m) => α) (fun (i : m) => SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5) _inst_6))))) x v) w) (HSMul.hSMul.{u2, u3, u3} R α α (instHSMul.{u2, u3} R α (SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5) _inst_6)))) x (Matrix.dotProduct.{u3, u1} m α _inst_1 _inst_4 _inst_5 v w))
Case conversion may be inaccurate. Consider using '#align matrix.smul_dot_product Matrix.smul_dotProductₓ'. -/
@[simp]
theorem smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m → α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w) :=
  by simp [dot_product, Finset.smul_sum, smul_mul_assoc]
#align matrix.smul_dot_product Matrix.smul_dotProduct

/- warning: matrix.dot_product_smul -> Matrix.dotProduct_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : Monoid.{u3} R] [_inst_4 : Mul.{u1} α] [_inst_5 : AddCommMonoid.{u1} α] [_inst_6 : DistribMulAction.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5)] [_inst_7 : SMulCommClass.{u3, u1, u1} R α α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5) _inst_6))) (Mul.toSMul.{u1} α _inst_4)] (x : R) (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 _inst_4 _inst_5 v (SMul.smul.{u3, max u2 u1} R (m -> α) (Function.hasSMul.{u2, u3, u1} m R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5) _inst_6)))) x w)) (SMul.smul.{u3, u1} R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_5)) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α _inst_5) _inst_6))) x (Matrix.dotProduct.{u1, u2} m α _inst_1 _inst_4 _inst_5 v w))
but is expected to have type
  forall {m : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} [_inst_1 : Fintype.{u1} m] [_inst_3 : Monoid.{u2} R] [_inst_4 : Mul.{u3} α] [_inst_5 : AddCommMonoid.{u3} α] [_inst_6 : DistribMulAction.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5)] [_inst_7 : SMulCommClass.{u2, u3, u3} R α α (SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5) _inst_6))) (Mul.toSMul.{u3} α _inst_4)] (x : R) (v : m -> α) (w : m -> α), Eq.{succ u3} α (Matrix.dotProduct.{u3, u1} m α _inst_1 _inst_4 _inst_5 v (HSMul.hSMul.{u2, max u3 u1, max u3 u1} R (m -> α) (m -> α) (instHSMul.{u2, max u3 u1} R (m -> α) (Pi.instSMul.{u1, u3, u2} m R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.8916 : m) => α) (fun (i : m) => SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5) _inst_6))))) x w)) (HSMul.hSMul.{u2, u3, u3} R α α (instHSMul.{u2, u3} R α (SMulZeroClass.toSMul.{u2, u3} R α (AddMonoid.toZero.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribSMul.toSMulZeroClass.{u2, u3} R α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_5)) (DistribMulAction.toDistribSMul.{u2, u3} R α _inst_3 (AddCommMonoid.toAddMonoid.{u3} α _inst_5) _inst_6)))) x (Matrix.dotProduct.{u3, u1} m α _inst_1 _inst_4 _inst_5 v w))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_smul Matrix.dotProduct_smulₓ'. -/
@[simp]
theorem dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m → α) : v ⬝ᵥ x • w = x • (v ⬝ᵥ w) :=
  by simp [dot_product, Finset.smul_sum, mul_smul_comm]
#align matrix.dot_product_smul Matrix.dotProduct_smul

end DistribMulAction

section StarRing

variable [NonUnitalSemiring α] [StarRing α] (v w : m → α)

/- warning: matrix.star_dot_product_star -> Matrix.star_dotProduct_star is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalSemiring.{u1} α] [_inst_4 : StarRing.{u1} α _inst_3] (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4)))) v) (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4)))) w)) (Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) w v))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalSemiring.{u2} α] [_inst_4 : StarRing.{u2} α _inst_3] (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (Star.star.{max u1 u2} (m -> α) (Pi.instStarForAll.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4)))) v) (Star.star.{max u2 u1} (m -> α) (Pi.instStarForAll.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4)))) w)) (Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) w v))
Case conversion may be inaccurate. Consider using '#align matrix.star_dot_product_star Matrix.star_dotProduct_starₓ'. -/
theorem star_dotProduct_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v) := by simp [dot_product]
#align matrix.star_dot_product_star Matrix.star_dotProduct_star

/- warning: matrix.star_dot_product -> Matrix.star_dotProduct is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalSemiring.{u1} α] [_inst_4 : StarRing.{u1} α _inst_3] (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4)))) v) w) (Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4)))) w) v))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalSemiring.{u2} α] [_inst_4 : StarRing.{u2} α _inst_3] (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (Star.star.{max u1 u2} (m -> α) (Pi.instStarForAll.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4)))) v) w) (Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (Star.star.{max u1 u2} (m -> α) (Pi.instStarForAll.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4)))) w) v))
Case conversion may be inaccurate. Consider using '#align matrix.star_dot_product Matrix.star_dotProductₓ'. -/
theorem star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by simp [dot_product]
#align matrix.star_dot_product Matrix.star_dotProduct

/- warning: matrix.dot_product_star -> Matrix.dotProduct_star is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_3 : NonUnitalSemiring.{u1} α] [_inst_4 : StarRing.{u1} α _inst_3] (v : m -> α) (w : m -> α), Eq.{succ u1} α (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) v (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4)))) w)) (Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4))) (Matrix.dotProduct.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) w (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (StarRing.toStarAddMonoid.{u1} α _inst_3 _inst_4)))) v)))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_3 : NonUnitalSemiring.{u2} α] [_inst_4 : StarRing.{u2} α _inst_3] (v : m -> α) (w : m -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) v (Star.star.{max u2 u1} (m -> α) (Pi.instStarForAll.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4)))) w)) (Star.star.{u2} α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4))) (Matrix.dotProduct.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) w (Star.star.{max u2 u1} (m -> α) (Pi.instStarForAll.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (StarRing.toStarAddMonoid.{u2} α _inst_3 _inst_4)))) v)))
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_star Matrix.dotProduct_starₓ'. -/
theorem dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v) := by simp [dot_product]
#align matrix.dot_product_star Matrix.dotProduct_star

end StarRing

end DotProduct

open Matrix

#print Matrix.mul /-
/-- `M ⬝ N` is the usual product of matrices `M` and `N`, i.e. we have that
`(M ⬝ N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `N`.
This is currently only defined when `m` is finite. -/
protected def mul [Fintype m] [Mul α] [AddCommMonoid α] (M : Matrix l m α) (N : Matrix m n α) :
    Matrix l n α := fun i k => (fun j => M i j) ⬝ᵥ fun j => N j k
#align matrix.mul Matrix.mul
-/

-- mathport name: matrix.mul
scoped infixl:75 " ⬝ " => Matrix.mul

/- warning: matrix.mul_apply -> Matrix.mul_apply is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Mul.{u1} α] [_inst_3 : AddCommMonoid.{u1} α] {M : Matrix.{u2, u3, u1} l m α} {N : Matrix.{u3, u4, u1} m n α} {i : l} {k : n}, Eq.{succ u1} α (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_1 _inst_2 _inst_3 M N i k) (Finset.sum.{u1, u3} α m _inst_3 (Finset.univ.{u3} m _inst_1) (fun (j : m) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (M i j) (N j k)))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u1}} {α : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Mul.{u4} α] [_inst_3 : AddCommMonoid.{u4} α] {M : Matrix.{u2, u3, u4} l m α} {N : Matrix.{u3, u1, u4} m n α} {i : l} {k : n}, Eq.{succ u4} α (Matrix.mul.{u4, u2, u3, u1} l m n α _inst_1 _inst_2 _inst_3 M N i k) (Finset.sum.{u4, u3} α m _inst_3 (Finset.univ.{u3} m _inst_1) (fun (j : m) => HMul.hMul.{u4, u4, u4} α α α (instHMul.{u4} α _inst_2) (M i j) (N j k)))
Case conversion may be inaccurate. Consider using '#align matrix.mul_apply Matrix.mul_applyₓ'. -/
theorem mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M ⬝ N) i k = ∑ j, M i j * N j k :=
  rfl
#align matrix.mul_apply Matrix.mul_apply

instance [Fintype n] [Mul α] [AddCommMonoid α] : Mul (Matrix n n α) :=
  ⟨Matrix.mul⟩

/- warning: matrix.mul_eq_mul -> Matrix.mul_eq_mul is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : Mul.{u1} α] [_inst_3 : AddCommMonoid.{u1} α] (M : Matrix.{u2, u2, u1} n n α) (N : Matrix.{u2, u2, u1} n n α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHMul.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasMul.{u1, u2} n α _inst_1 _inst_2 _inst_3)) M N) (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_1 _inst_2 _inst_3 M N)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} n] [_inst_2 : Mul.{u2} α] [_inst_3 : AddCommMonoid.{u2} α] (M : Matrix.{u1, u1, u2} n n α) (N : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHMul.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.instMulMatrix.{u2, u1} n α _inst_1 _inst_2 _inst_3)) M N) (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_1 _inst_2 _inst_3 M N)
Case conversion may be inaccurate. Consider using '#align matrix.mul_eq_mul Matrix.mul_eq_mulₓ'. -/
@[simp]
theorem mul_eq_mul [Fintype n] [Mul α] [AddCommMonoid α] (M N : Matrix n n α) : M * N = M ⬝ N :=
  rfl
#align matrix.mul_eq_mul Matrix.mul_eq_mul

/- warning: matrix.mul_apply' -> Matrix.mul_apply' is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Mul.{u1} α] [_inst_3 : AddCommMonoid.{u1} α] {M : Matrix.{u2, u3, u1} l m α} {N : Matrix.{u3, u4, u1} m n α} {i : l} {k : n}, Eq.{succ u1} α (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_1 _inst_2 _inst_3 M N i k) (Matrix.dotProduct.{u1, u3} m α _inst_1 _inst_2 _inst_3 (fun (j : m) => M i j) (fun (j : m) => N j k))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u1}} {α : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Mul.{u4} α] [_inst_3 : AddCommMonoid.{u4} α] {M : Matrix.{u2, u3, u4} l m α} {N : Matrix.{u3, u1, u4} m n α} {i : l} {k : n}, Eq.{succ u4} α (Matrix.mul.{u4, u2, u3, u1} l m n α _inst_1 _inst_2 _inst_3 M N i k) (Matrix.dotProduct.{u4, u3} m α _inst_1 _inst_2 _inst_3 (fun (j : m) => M i j) (fun (j : m) => N j k))
Case conversion may be inaccurate. Consider using '#align matrix.mul_apply' Matrix.mul_apply'ₓ'. -/
theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M ⬝ N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k :=
  rfl
#align matrix.mul_apply' Matrix.mul_apply'

/- warning: matrix.diagonal_neg -> Matrix.diagonal_neg is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : AddGroup.{u1} α] (d : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Neg.neg.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasNeg.{u1, u2, u2} n n α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_2))) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_2)))) d)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_2)))) (fun (i : n) => Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_2)) (d i)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : AddGroup.{u2} α] (d : n -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Neg.neg.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.neg.{u2, u1, u1} n n α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (AddGroup.toSubtractionMonoid.{u2} α _inst_2))))) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (AddGroup.toSubtractionMonoid.{u2} α _inst_2)))) d)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (AddGroup.toSubtractionMonoid.{u2} α _inst_2)))) (fun (i : n) => Neg.neg.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (AddGroup.toSubtractionMonoid.{u2} α _inst_2)))) (d i)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_neg Matrix.diagonal_negₓ'. -/
@[simp]
theorem diagonal_neg [DecidableEq n] [AddGroup α] (d : n → α) :
    -diagonal d = diagonal fun i => -d i :=
  ((diagonalAddMonoidHom n α).map_neg d).symm
#align matrix.diagonal_neg Matrix.diagonal_neg

/- warning: matrix.sum_apply -> Matrix.sum_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] (i : m) (j : n) (s : Finset.{u2} β) (g : β -> (Matrix.{u3, u4, u1} m n α)), Eq.{succ u1} α (Finset.sum.{max u3 u4 u1, u2} (Matrix.{u3, u4, u1} m n α) β (Matrix.addCommMonoid.{u1, u3, u4} m n α _inst_1) s (fun (c : β) => g c) i j) (Finset.sum.{u1, u2} α β _inst_1 s (fun (c : β) => g c i j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : AddCommMonoid.{u3} α] (i : m) (j : n) (s : Finset.{u4} β) (g : β -> (Matrix.{u2, u1, u3} m n α)), Eq.{succ u3} α (Finset.sum.{max (max u3 u2) u1, u4} (Matrix.{u2, u1, u3} m n α) β (Matrix.addCommMonoid.{u3, u2, u1} m n α _inst_1) s (fun (c : β) => g c) i j) (Finset.sum.{u3, u4} α β _inst_1 s (fun (c : β) => g c i j))
Case conversion may be inaccurate. Consider using '#align matrix.sum_apply Matrix.sum_applyₓ'. -/
theorem sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β → Matrix m n α) :
    (∑ c in s, g c) i j = ∑ c in s, g c i j :=
  (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)
#align matrix.sum_apply Matrix.sum_apply

/- warning: matrix.two_mul_expl -> Matrix.two_mul_expl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (B : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R), And (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (instHMul.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.hasMul.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) A B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))))) (And (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (instHMul.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.hasMul.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) A B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))))) (And (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (instHMul.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.hasMul.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) A B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))))) (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (instHMul.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.hasMul.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) A B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (A (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (B (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring)))))) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (A : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (B : Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R), And (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (instHMul.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.instMulMatrix.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) A B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))))) (And (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (instHMul.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.instMulMatrix.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) A B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))))) (And (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (instHMul.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.instMulMatrix.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) A B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))))) (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (instHMul.{u1} (Matrix.{0, 0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R) (Matrix.instMulMatrix.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Fin.fintype (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) A B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (A (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (B (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))))))
Case conversion may be inaccurate. Consider using '#align matrix.two_mul_expl Matrix.two_mul_explₓ'. -/
theorem two_mul_expl {R : Type _} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
      (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
        (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧ (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 :=
  by
  constructor; on_goal 2 => constructor; on_goal 3 => constructor
  all_goals
    simp only [Matrix.mul_eq_mul]
    rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
    simp
#align matrix.two_mul_expl Matrix.two_mul_expl

section AddCommMonoid

variable [AddCommMonoid α] [Mul α]

/- warning: matrix.smul_mul -> Matrix.smul_mul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {R : Type.{u5}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : Fintype.{u4} n] [_inst_4 : Monoid.{u5} R] [_inst_5 : DistribMulAction.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] [_inst_6 : IsScalarTower.{u5, u1, u1} R α α (SMulZeroClass.toHasSmul.{u5, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (DistribSMul.toSmulZeroClass.{u5, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (DistribMulAction.toDistribSMul.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_5))) (Mul.toSMul.{u1} α _inst_2) (SMulZeroClass.toHasSmul.{u5, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (DistribSMul.toSmulZeroClass.{u5, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (DistribMulAction.toDistribSMul.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_5)))] (a : R) (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u4, u2, u1} n l α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} m l α) (Matrix.mul.{u1, u3, u4, u2} m n l α _inst_3 _inst_2 _inst_1 (SMul.smul.{u5, max u3 u4 u1} R (Matrix.{u3, u4, u1} m n α) (Matrix.hasSmul.{u1, u3, u4, u5} m n R α (SMulZeroClass.toHasSmul.{u5, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (DistribSMul.toSmulZeroClass.{u5, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (DistribMulAction.toDistribSMul.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_5)))) a M) N) (SMul.smul.{u5, max u3 u2 u1} R (Matrix.{u3, u2, u1} m l α) (Matrix.hasSmul.{u1, u3, u2, u5} m l R α (SMulZeroClass.toHasSmul.{u5, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (DistribSMul.toSmulZeroClass.{u5, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (DistribMulAction.toDistribSMul.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_5)))) a (Matrix.mul.{u1, u3, u4, u2} m n l α _inst_3 _inst_2 _inst_1 M N))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u4}} {R : Type.{u3}} {α : Type.{u5}} [_inst_1 : AddCommMonoid.{u5} α] [_inst_2 : Mul.{u5} α] [_inst_3 : Fintype.{u4} n] [_inst_4 : Monoid.{u3} R] [_inst_5 : DistribMulAction.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1)] [_inst_6 : IsScalarTower.{u3, u5, u5} R α α (SMulZeroClass.toSMul.{u3, u5} R α (AddMonoid.toZero.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u5} R α (AddMonoid.toAddZeroClass.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribMulAction.toDistribSMul.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1) _inst_5))) (Mul.toSMul.{u5} α _inst_2) (SMulZeroClass.toSMul.{u3, u5} R α (AddMonoid.toZero.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u5} R α (AddMonoid.toAddZeroClass.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribMulAction.toDistribSMul.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1) _inst_5)))] (a : R) (M : Matrix.{u2, u4, u5} m n α) (N : Matrix.{u4, u1, u5} n l α), Eq.{max (max (succ u5) (succ u1)) (succ u2)} (Matrix.{u2, u1, u5} m l α) (Matrix.mul.{u5, u2, u4, u1} m n l α _inst_3 _inst_2 _inst_1 (HSMul.hSMul.{u3, max (max u5 u2) u4, max (max u5 u2) u4} R (Matrix.{u2, u4, u5} m n α) (Matrix.{u2, u4, u5} m n α) (instHSMul.{u3, max (max u5 u2) u4} R (Matrix.{u2, u4, u5} m n α) (Matrix.smul.{u5, u2, u4, u3} m n R α (SMulZeroClass.toSMul.{u3, u5} R α (AddMonoid.toZero.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u5} R α (AddMonoid.toAddZeroClass.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribMulAction.toDistribSMul.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1) _inst_5))))) a M) N) (HSMul.hSMul.{u3, max (max u1 u2) u5, max (max u5 u1) u2} R (Matrix.{u2, u1, u5} m l α) (Matrix.{u2, u1, u5} m l α) (instHSMul.{u3, max (max u5 u1) u2} R (Matrix.{u2, u1, u5} m l α) (Matrix.smul.{u5, u2, u1, u3} m l R α (SMulZeroClass.toSMul.{u3, u5} R α (AddMonoid.toZero.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u5} R α (AddMonoid.toAddZeroClass.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribMulAction.toDistribSMul.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1) _inst_5))))) a (Matrix.mul.{u5, u2, u4, u1} m n l α _inst_3 _inst_2 _inst_1 M N))
Case conversion may be inaccurate. Consider using '#align matrix.smul_mul Matrix.smul_mulₓ'. -/
@[simp]
theorem smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α] (a : R)
    (M : Matrix m n α) (N : Matrix n l α) : (a • M) ⬝ N = a • M ⬝ N :=
  by
  ext
  apply smul_dot_product
#align matrix.smul_mul Matrix.smul_mul

/- warning: matrix.mul_smul -> Matrix.mul_smul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {R : Type.{u5}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : Fintype.{u4} n] [_inst_4 : Monoid.{u5} R] [_inst_5 : DistribMulAction.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] [_inst_6 : SMulCommClass.{u5, u1, u1} R α α (SMulZeroClass.toHasSmul.{u5, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (DistribSMul.toSmulZeroClass.{u5, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (DistribMulAction.toDistribSMul.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_5))) (Mul.toSMul.{u1} α _inst_2)] (M : Matrix.{u3, u4, u1} m n α) (a : R) (N : Matrix.{u4, u2, u1} n l α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} m l α) (Matrix.mul.{u1, u3, u4, u2} m n l α _inst_3 _inst_2 _inst_1 M (SMul.smul.{u5, max u4 u2 u1} R (Matrix.{u4, u2, u1} n l α) (Matrix.hasSmul.{u1, u4, u2, u5} n l R α (SMulZeroClass.toHasSmul.{u5, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (DistribSMul.toSmulZeroClass.{u5, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (DistribMulAction.toDistribSMul.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_5)))) a N)) (SMul.smul.{u5, max u3 u2 u1} R (Matrix.{u3, u2, u1} m l α) (Matrix.hasSmul.{u1, u3, u2, u5} m l R α (SMulZeroClass.toHasSmul.{u5, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (DistribSMul.toSmulZeroClass.{u5, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (DistribMulAction.toDistribSMul.{u5, u1} R α _inst_4 (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_5)))) a (Matrix.mul.{u1, u3, u4, u2} m n l α _inst_3 _inst_2 _inst_1 M N))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u4}} {R : Type.{u3}} {α : Type.{u5}} [_inst_1 : AddCommMonoid.{u5} α] [_inst_2 : Mul.{u5} α] [_inst_3 : Fintype.{u4} n] [_inst_4 : Monoid.{u3} R] [_inst_5 : DistribMulAction.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1)] [_inst_6 : SMulCommClass.{u3, u5, u5} R α α (SMulZeroClass.toSMul.{u3, u5} R α (AddMonoid.toZero.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u5} R α (AddMonoid.toAddZeroClass.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribMulAction.toDistribSMul.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1) _inst_5))) (Mul.toSMul.{u5} α _inst_2)] (M : Matrix.{u2, u4, u5} m n α) (a : R) (N : Matrix.{u4, u1, u5} n l α), Eq.{max (max (succ u5) (succ u1)) (succ u2)} (Matrix.{u2, u1, u5} m l α) (Matrix.mul.{u5, u2, u4, u1} m n l α _inst_3 _inst_2 _inst_1 M (HSMul.hSMul.{u3, max (max u5 u1) u4, max (max u5 u1) u4} R (Matrix.{u4, u1, u5} n l α) (Matrix.{u4, u1, u5} n l α) (instHSMul.{u3, max (max u5 u1) u4} R (Matrix.{u4, u1, u5} n l α) (Matrix.smul.{u5, u4, u1, u3} n l R α (SMulZeroClass.toSMul.{u3, u5} R α (AddMonoid.toZero.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u5} R α (AddMonoid.toAddZeroClass.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribMulAction.toDistribSMul.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1) _inst_5))))) a N)) (HSMul.hSMul.{u3, max (max u1 u2) u5, max (max u5 u1) u2} R (Matrix.{u2, u1, u5} m l α) (Matrix.{u2, u1, u5} m l α) (instHSMul.{u3, max (max u5 u1) u2} R (Matrix.{u2, u1, u5} m l α) (Matrix.smul.{u5, u2, u1, u3} m l R α (SMulZeroClass.toSMul.{u3, u5} R α (AddMonoid.toZero.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u5} R α (AddMonoid.toAddZeroClass.{u5} α (AddCommMonoid.toAddMonoid.{u5} α _inst_1)) (DistribMulAction.toDistribSMul.{u3, u5} R α _inst_4 (AddCommMonoid.toAddMonoid.{u5} α _inst_1) _inst_5))))) a (Matrix.mul.{u5, u2, u4, u1} m n l α _inst_3 _inst_2 _inst_1 M N))
Case conversion may be inaccurate. Consider using '#align matrix.mul_smul Matrix.mul_smulₓ'. -/
@[simp]
theorem mul_smul [Fintype n] [Monoid R] [DistribMulAction R α] [SMulCommClass R α α]
    (M : Matrix m n α) (a : R) (N : Matrix n l α) : M ⬝ (a • N) = a • M ⬝ N :=
  by
  ext
  apply dot_product_smul
#align matrix.mul_smul Matrix.mul_smul

end AddCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/- warning: matrix.mul_zero -> Matrix.mul_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} m o α) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) M (OfNat.ofNat.{max u3 u4 u1} (Matrix.{u3, u4, u1} n o α) 0 (OfNat.mk.{max u3 u4 u1} (Matrix.{u3, u4, u1} n o α) 0 (Zero.zero.{max u3 u4 u1} (Matrix.{u3, u4, u1} n o α) (Matrix.hasZero.{u1, u3, u4} n o α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))) (OfNat.ofNat.{max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) 0 (OfNat.mk.{max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) 0 (Zero.zero.{max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.hasZero.{u1, u2, u4} m o α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocSemiring.{u4} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m o α) (Matrix.mul.{u4, u2, u3, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) M (OfNat.ofNat.{max (max u4 u3) u1} (Matrix.{u3, u1, u4} n o α) 0 (Zero.toOfNat0.{max (max u4 u3) u1} (Matrix.{u3, u1, u4} n o α) (Matrix.zero.{u4, u3, u1} n o α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)))))) (OfNat.ofNat.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} m o α) 0 (Zero.toOfNat0.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} m o α) (Matrix.zero.{u4, u2, u1} m o α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.mul_zero Matrix.mul_zeroₓ'. -/
@[simp]
protected theorem mul_zero [Fintype n] (M : Matrix m n α) : M ⬝ (0 : Matrix n o α) = 0 :=
  by
  ext (i j)
  apply dot_product_zero
#align matrix.mul_zero Matrix.mul_zero

/- warning: matrix.zero_mul -> Matrix.zero_mul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} m] (M : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} l n α) (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} l m α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} l m α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} l m α) (Matrix.hasZero.{u1, u2, u3} l m α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)))))) M) (OfNat.ofNat.{max u2 u4 u1} (Matrix.{u2, u4, u1} l n α) 0 (OfNat.mk.{max u2 u4 u1} (Matrix.{u2, u4, u1} l n α) 0 (Zero.zero.{max u2 u4 u1} (Matrix.{u2, u4, u1} l n α) (Matrix.hasZero.{u1, u2, u4} l n α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocSemiring.{u4} α] [_inst_2 : Fintype.{u3} m] (M : Matrix.{u3, u2, u4} m n α), Eq.{max (max (succ u4) (succ u1)) (succ u2)} (Matrix.{u1, u2, u4} l n α) (Matrix.mul.{u4, u1, u3, u2} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) (OfNat.ofNat.{max (max u4 u1) u3} (Matrix.{u1, u3, u4} l m α) 0 (Zero.toOfNat0.{max (max u4 u1) u3} (Matrix.{u1, u3, u4} l m α) (Matrix.zero.{u4, u1, u3} l m α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1))))) M) (OfNat.ofNat.{max (max u4 u1) u2} (Matrix.{u1, u2, u4} l n α) 0 (Zero.toOfNat0.{max (max u4 u1) u2} (Matrix.{u1, u2, u4} l n α) (Matrix.zero.{u4, u1, u2} l n α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.zero_mul Matrix.zero_mulₓ'. -/
@[simp]
protected theorem zero_mul [Fintype m] (M : Matrix m n α) : (0 : Matrix l m α) ⬝ M = 0 :=
  by
  ext (i j)
  apply zero_dot_product
#align matrix.zero_mul Matrix.zero_mul

/- warning: matrix.mul_add -> Matrix.mul_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (L : Matrix.{u2, u3, u1} m n α) (M : Matrix.{u3, u4, u1} n o α) (N : Matrix.{u3, u4, u1} n o α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} m o α) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) L (HAdd.hAdd.{max u3 u4 u1, max u3 u4 u1, max u3 u4 u1} (Matrix.{u3, u4, u1} n o α) (Matrix.{u3, u4, u1} n o α) (Matrix.{u3, u4, u1} n o α) (instHAdd.{max u3 u4 u1} (Matrix.{u3, u4, u1} n o α) (Matrix.hasAdd.{u1, u3, u4} n o α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) M N)) (HAdd.hAdd.{max u2 u4 u1, max u2 u4 u1, max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.{u2, u4, u1} m o α) (Matrix.{u2, u4, u1} m o α) (instHAdd.{max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.hasAdd.{u1, u2, u4} m o α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) L M) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) L N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocSemiring.{u4} α] [_inst_2 : Fintype.{u3} n] (L : Matrix.{u2, u3, u4} m n α) (M : Matrix.{u3, u1, u4} n o α) (N : Matrix.{u3, u1, u4} n o α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m o α) (Matrix.mul.{u4, u2, u3, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) L (HAdd.hAdd.{max (max u4 u3) u1, max (max u4 u3) u1, max (max u4 u3) u1} (Matrix.{u3, u1, u4} n o α) (Matrix.{u3, u1, u4} n o α) (Matrix.{u3, u1, u4} n o α) (instHAdd.{max (max u4 u3) u1} (Matrix.{u3, u1, u4} n o α) (Matrix.add.{u4, u3, u1} n o α (Distrib.toAdd.{u4} α (NonUnitalNonAssocSemiring.toDistrib.{u4} α _inst_1)))) M N)) (HAdd.hAdd.{max (max u4 u2) u1, max (max u4 u2) u1, max (max u4 u2) u1} (Matrix.{u2, u1, u4} m o α) (Matrix.{u2, u1, u4} m o α) (Matrix.{u2, u1, u4} m o α) (instHAdd.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} m o α) (Matrix.add.{u4, u2, u1} m o α (Distrib.toAdd.{u4} α (NonUnitalNonAssocSemiring.toDistrib.{u4} α _inst_1)))) (Matrix.mul.{u4, u2, u3, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) L M) (Matrix.mul.{u4, u2, u3, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) L N))
Case conversion may be inaccurate. Consider using '#align matrix.mul_add Matrix.mul_addₓ'. -/
protected theorem mul_add [Fintype n] (L : Matrix m n α) (M N : Matrix n o α) :
    L ⬝ (M + N) = L ⬝ M + L ⬝ N := by
  ext (i j)
  apply dot_product_add
#align matrix.mul_add Matrix.mul_add

/- warning: matrix.add_mul -> Matrix.add_mul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} m] (L : Matrix.{u2, u3, u1} l m α) (M : Matrix.{u2, u3, u1} l m α) (N : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} l n α) (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} l m α) (Matrix.{u2, u3, u1} l m α) (Matrix.{u2, u3, u1} l m α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} l m α) (Matrix.hasAdd.{u1, u2, u3} l m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) L M) N) (HAdd.hAdd.{max u2 u4 u1, max u2 u4 u1, max u2 u4 u1} (Matrix.{u2, u4, u1} l n α) (Matrix.{u2, u4, u1} l n α) (Matrix.{u2, u4, u1} l n α) (instHAdd.{max u2 u4 u1} (Matrix.{u2, u4, u1} l n α) (Matrix.hasAdd.{u1, u2, u4} l n α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) L N) (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) M N))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocSemiring.{u4} α] [_inst_2 : Fintype.{u3} m] (L : Matrix.{u2, u3, u4} l m α) (M : Matrix.{u2, u3, u4} l m α) (N : Matrix.{u3, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} l n α) (Matrix.mul.{u4, u2, u3, u1} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) (HAdd.hAdd.{max (max u4 u2) u3, max (max u4 u2) u3, max (max u4 u2) u3} (Matrix.{u2, u3, u4} l m α) (Matrix.{u2, u3, u4} l m α) (Matrix.{u2, u3, u4} l m α) (instHAdd.{max (max u4 u2) u3} (Matrix.{u2, u3, u4} l m α) (Matrix.add.{u4, u2, u3} l m α (Distrib.toAdd.{u4} α (NonUnitalNonAssocSemiring.toDistrib.{u4} α _inst_1)))) L M) N) (HAdd.hAdd.{max (max u4 u2) u1, max (max u4 u2) u1, max (max u4 u2) u1} (Matrix.{u2, u1, u4} l n α) (Matrix.{u2, u1, u4} l n α) (Matrix.{u2, u1, u4} l n α) (instHAdd.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} l n α) (Matrix.add.{u4, u2, u1} l n α (Distrib.toAdd.{u4} α (NonUnitalNonAssocSemiring.toDistrib.{u4} α _inst_1)))) (Matrix.mul.{u4, u2, u3, u1} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) L N) (Matrix.mul.{u4, u2, u3, u1} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) M N))
Case conversion may be inaccurate. Consider using '#align matrix.add_mul Matrix.add_mulₓ'. -/
protected theorem add_mul [Fintype m] (L M : Matrix l m α) (N : Matrix m n α) :
    (L + M) ⬝ N = L ⬝ N + M ⬝ N := by
  ext (i j)
  apply add_dot_product
#align matrix.add_mul Matrix.add_mul

instance [Fintype n] : NonUnitalNonAssocSemiring (Matrix n n α) :=
  { Matrix.addCommMonoid with
    mul := (· * ·)
    add := (· + ·)
    zero := 0
    mul_zero := Matrix.mul_zero
    zero_mul := Matrix.zero_mul
    left_distrib := Matrix.mul_add
    right_distrib := Matrix.add_mul }

/- warning: matrix.diagonal_mul -> Matrix.diagonal_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (d : m -> α) (M : Matrix.{u2, u3, u1} m n α) (i : m) (j : n), Eq.{succ u1} α (Matrix.mul.{u1, u2, u2, u3} m m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) d) M i j) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (d i) (M i j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (d : m -> α) (M : Matrix.{u2, u1, u3} m n α) (i : m) (j : n), Eq.{succ u3} α (Matrix.mul.{u3, u2, u2, u1} m m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_1) (Matrix.diagonal.{u3, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)) d) M i j) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_1)) (d i) (M i j))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_mul Matrix.diagonal_mulₓ'. -/
@[simp]
theorem diagonal_mul [Fintype m] [DecidableEq m] (d : m → α) (M : Matrix m n α) (i j) :
    (diagonal d).mul M i j = d i * M i j :=
  diagonal_dotProduct _ _ _
#align matrix.diagonal_mul Matrix.diagonal_mul

/- warning: matrix.mul_diagonal -> Matrix.mul_diagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : DecidableEq.{succ u3} n] (d : n -> α) (M : Matrix.{u2, u3, u1} m n α) (i : m) (j : n), Eq.{succ u1} α (Matrix.mul.{u1, u2, u3, u3} m n n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) M (Matrix.diagonal.{u1, u3} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) d) i j) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (M i j) (d j))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] (d : n -> α) (M : Matrix.{u1, u2, u3} m n α) (i : m) (j : n), Eq.{succ u3} α (Matrix.mul.{u3, u1, u2, u2} m n n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_1) M (Matrix.diagonal.{u3, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)) d) i j) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_1)) (M i j) (d j))
Case conversion may be inaccurate. Consider using '#align matrix.mul_diagonal Matrix.mul_diagonalₓ'. -/
@[simp]
theorem mul_diagonal [Fintype n] [DecidableEq n] (d : n → α) (M : Matrix m n α) (i j) :
    (M ⬝ diagonal d) i j = M i j * d j :=
  by
  rw [← diagonal_transpose]
  apply dot_product_diagonal
#align matrix.mul_diagonal Matrix.mul_diagonal

/- warning: matrix.diagonal_mul_diagonal -> Matrix.diagonal_mul_diagonal is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] (d₁ : n -> α) (d₂ : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) d₁) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) d₂)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (fun (i : n) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (d₁ i) (d₂ i)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : Fintype.{u1} n] [_inst_3 : DecidableEq.{succ u1} n] (d₁ : n -> α) (d₂ : n -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_1)) d₁) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_1)) d₂)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_1)) (fun (i : n) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (d₁ i) (d₂ i)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_mul_diagonal Matrix.diagonal_mul_diagonalₓ'. -/
@[simp]
theorem diagonal_mul_diagonal [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonal d₁ ⬝ diagonal d₂ = diagonal fun i => d₁ i * d₂ i := by
  ext (i j) <;> by_cases i = j <;> simp [h]
#align matrix.diagonal_mul_diagonal Matrix.diagonal_mul_diagonal

/- warning: matrix.diagonal_mul_diagonal' -> Matrix.diagonal_mul_diagonal' is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] (d₁ : n -> α) (d₂ : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (instHMul.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasMul.{u1, u2} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) d₁) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) d₂)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (fun (i : n) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (d₁ i) (d₂ i)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : Fintype.{u1} n] [_inst_3 : DecidableEq.{succ u1} n] (d₁ : n -> α) (d₂ : n -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (Matrix.{u1, u1, u2} n n α) (instHMul.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.instMulMatrix.{u2, u1} n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1))) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_1)) d₁) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_1)) d₂)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_1)) (fun (i : n) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (d₁ i) (d₂ i)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_mul_diagonal' Matrix.diagonal_mul_diagonal'ₓ'. -/
theorem diagonal_mul_diagonal' [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i :=
  diagonal_mul_diagonal _ _
#align matrix.diagonal_mul_diagonal' Matrix.diagonal_mul_diagonal'

/- warning: matrix.smul_eq_diagonal_mul -> Matrix.smul_eq_diagonal_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (M : Matrix.{u2, u3, u1} m n α) (a : α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (SMul.smul.{u1, max u2 u3 u1} α (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u1} m n α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) a M) (Matrix.mul.{u1, u2, u2, u3} m m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (fun (_x : m) => a)) M)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (M : Matrix.{u2, u1, u3} m n α) (a : α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (HSMul.hSMul.{u3, max (max u3 u2) u1, max (max u3 u2) u1} α (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSMul.{u3, max (max u3 u2) u1} α (Matrix.{u2, u1, u3} m n α) (Matrix.smul.{u3, u2, u1, u3} m n α α (SMulZeroClass.toSMul.{u3, u3} α α (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u3, u3} α α (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)) (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)) (MulZeroClass.toSMulWithZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)))))) a M) (Matrix.mul.{u3, u2, u2, u1} m m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_1) (Matrix.diagonal.{u3, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)) (fun (_x : m) => a)) M)
Case conversion may be inaccurate. Consider using '#align matrix.smul_eq_diagonal_mul Matrix.smul_eq_diagonal_mulₓ'. -/
theorem smul_eq_diagonal_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α) :
    a • M = (diagonal fun _ => a) ⬝ M := by
  ext
  simp
#align matrix.smul_eq_diagonal_mul Matrix.smul_eq_diagonal_mul

/- warning: matrix.diag_col_mul_row -> Matrix.diag_col_mul_row is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] (a : n -> α) (b : n -> α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u1, u2} n α (Matrix.mul.{u1, u2, 0, u2} n Unit n α PUnit.fintype.{0} (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) (Matrix.col.{u1, u2} n α a) (Matrix.row.{u1, u2} n α b))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (n -> α) (n -> α) (n -> α) (instHMul.{max u2 u1} (n -> α) (Pi.instMul.{u2, u1} n (fun (i : n) => α) (fun (i : n) => Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] (a : n -> α) (b : n -> α), Eq.{max (succ u2) (succ u1)} (n -> α) (Matrix.diag.{u2, u1} n α (Matrix.mul.{u2, u1, 0, u1} n Unit n α PUnit.fintype.{0} (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Matrix.col.{u2, u1} n α a) (Matrix.row.{u2, u1} n α b))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (n -> α) (n -> α) (n -> α) (instHMul.{max u2 u1} (n -> α) (Pi.instMul.{u1, u2} n (fun (i : n) => α) (fun (i : n) => NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align matrix.diag_col_mul_row Matrix.diag_col_mul_rowₓ'. -/
@[simp]
theorem diag_col_mul_row (a b : n → α) : diag (col a ⬝ row b) = a * b :=
  by
  ext
  simp [Matrix.mul_apply, col, row]
#align matrix.diag_col_mul_row Matrix.diag_col_mul_row

#print Matrix.addMonoidHomMulLeft /-
/-- Left multiplication by a matrix, as an `add_monoid_hom` from matrices to matrices. -/
@[simps]
def addMonoidHomMulLeft [Fintype m] (M : Matrix l m α) : Matrix m n α →+ Matrix l n α
    where
  toFun x := M ⬝ x
  map_zero' := Matrix.mul_zero _
  map_add' := Matrix.mul_add _
#align matrix.add_monoid_hom_mul_left Matrix.addMonoidHomMulLeft
-/

#print Matrix.addMonoidHomMulRight /-
/-- Right multiplication by a matrix, as an `add_monoid_hom` from matrices to matrices. -/
@[simps]
def addMonoidHomMulRight [Fintype m] (M : Matrix m n α) : Matrix l m α →+ Matrix l n α
    where
  toFun x := x ⬝ M
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _
#align matrix.add_monoid_hom_mul_right Matrix.addMonoidHomMulRight
-/

/- warning: matrix.sum_mul -> Matrix.sum_mul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u5}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u4} m] (s : Finset.{u2} β) (f : β -> (Matrix.{u3, u4, u1} l m α)) (M : Matrix.{u4, u5, u1} m n α), Eq.{succ (max u3 u5 u1)} (Matrix.{u3, u5, u1} l n α) (Matrix.mul.{u1, u3, u4, u5} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) (Finset.sum.{max u3 u4 u1, u2} (Matrix.{u3, u4, u1} l m α) β (Matrix.addCommMonoid.{u1, u3, u4} l m α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) s (fun (a : β) => f a)) M) (Finset.sum.{max u3 u5 u1, u2} (Matrix.{u3, u5, u1} l n α) β (Matrix.addCommMonoid.{u1, u3, u5} l n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) s (fun (a : β) => Matrix.mul.{u1, u3, u4, u5} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) (f a) M))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u1}} {α : Type.{u4}} {β : Type.{u5}} [_inst_1 : NonUnitalNonAssocSemiring.{u4} α] [_inst_2 : Fintype.{u3} m] (s : Finset.{u5} β) (f : β -> (Matrix.{u2, u3, u4} l m α)) (M : Matrix.{u3, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} l n α) (Matrix.mul.{u4, u2, u3, u1} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) (Finset.sum.{max (max u3 u2) u4, u5} (Matrix.{u2, u3, u4} l m α) β (Matrix.addCommMonoid.{u4, u2, u3} l m α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1)) s (fun (a : β) => f a)) M) (Finset.sum.{max (max u1 u2) u4, u5} (Matrix.{u2, u1, u4} l n α) β (Matrix.addCommMonoid.{u4, u2, u1} l n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1)) s (fun (a : β) => Matrix.mul.{u4, u2, u3, u1} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) (f a) M))
Case conversion may be inaccurate. Consider using '#align matrix.sum_mul Matrix.sum_mulₓ'. -/
protected theorem sum_mul [Fintype m] (s : Finset β) (f : β → Matrix l m α) (M : Matrix m n α) :
    (∑ a in s, f a) ⬝ M = ∑ a in s, f a ⬝ M :=
  (addMonoidHomMulRight M : Matrix l m α →+ _).map_sum f s
#align matrix.sum_mul Matrix.sum_mul

/- warning: matrix.mul_sum -> Matrix.mul_sum is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u5}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u4} m] (s : Finset.{u2} β) (f : β -> (Matrix.{u4, u5, u1} m n α)) (M : Matrix.{u3, u4, u1} l m α), Eq.{succ (max u3 u5 u1)} (Matrix.{u3, u5, u1} l n α) (Matrix.mul.{u1, u3, u4, u5} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) M (Finset.sum.{max u4 u5 u1, u2} (Matrix.{u4, u5, u1} m n α) β (Matrix.addCommMonoid.{u1, u4, u5} m n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) s (fun (a : β) => f a))) (Finset.sum.{max u3 u5 u1, u2} (Matrix.{u3, u5, u1} l n α) β (Matrix.addCommMonoid.{u1, u3, u5} l n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) s (fun (a : β) => Matrix.mul.{u1, u3, u4, u5} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) M (f a)))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {α : Type.{u4}} {β : Type.{u5}} [_inst_1 : NonUnitalNonAssocSemiring.{u4} α] [_inst_2 : Fintype.{u3} m] (s : Finset.{u5} β) (f : β -> (Matrix.{u3, u2, u4} m n α)) (M : Matrix.{u1, u3, u4} l m α), Eq.{max (max (succ u4) (succ u1)) (succ u2)} (Matrix.{u1, u2, u4} l n α) (Matrix.mul.{u4, u1, u3, u2} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) M (Finset.sum.{max (max u4 u3) u2, u5} (Matrix.{u3, u2, u4} m n α) β (Matrix.addCommMonoid.{u4, u3, u2} m n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1)) s (fun (a : β) => f a))) (Finset.sum.{max (max u2 u1) u4, u5} (Matrix.{u1, u2, u4} l n α) β (Matrix.addCommMonoid.{u4, u1, u2} l n α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1)) s (fun (a : β) => Matrix.mul.{u4, u1, u3, u2} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1) M (f a)))
Case conversion may be inaccurate. Consider using '#align matrix.mul_sum Matrix.mul_sumₓ'. -/
protected theorem mul_sum [Fintype m] (s : Finset β) (f : β → Matrix m n α) (M : Matrix l m α) :
    (M ⬝ ∑ a in s, f a) = ∑ a in s, M ⬝ f a :=
  (addMonoidHomMulLeft M : Matrix m n α →+ _).map_sum f s
#align matrix.mul_sum Matrix.mul_sum

/- warning: matrix.semiring.is_scalar_tower -> Matrix.Semiring.isScalarTower is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : Monoid.{u3} R] [_inst_4 : DistribMulAction.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))] [_inst_5 : IsScalarTower.{u3, u1, u1} R α α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4))) (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))], IsScalarTower.{u3, max u2 u1, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.hasSmul.{u1, u2, u2, u3} n n R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))) (Mul.toSMul.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasMul.{u1, u2} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (Matrix.hasSmul.{u1, u2, u2, u3} n n R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4))))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : Monoid.{u3} R] [_inst_4 : DistribMulAction.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))] [_inst_5 : IsScalarTower.{u3, u1, u1} R α α (SMulZeroClass.toSMul.{u3, u1} R α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4))) (SMulZeroClass.toSMul.{u1, u1} α α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)))) (SMulZeroClass.toSMul.{u3, u1} R α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))], IsScalarTower.{u3, max u1 u2, max u1 u2} R (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.smul.{u1, u2, u2, u3} n n R α (SMulZeroClass.toSMul.{u3, u1} R α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))) (SMulZeroClass.toSMul.{max u1 u2, max u1 u2} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.zero.{u1, u2, u2} n n α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))) (SMulWithZero.toSMulZeroClass.{max u1 u2, max u1 u2} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.zero.{u1, u2, u2} n n α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))) (Matrix.zero.{u1, u2, u2} n n α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))) (MulZeroClass.toSMulWithZero.{max u1 u2} (Matrix.{u2, u2, u1} n n α) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u1 u2} (Matrix.{u2, u2, u1} n n α) (Matrix.nonUnitalNonAssocSemiring.{u1, u2} n α _inst_1 _inst_2))))) (Matrix.smul.{u1, u2, u2, u3} n n R α (SMulZeroClass.toSMul.{u3, u1} R α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4))))
Case conversion may be inaccurate. Consider using '#align matrix.semiring.is_scalar_tower Matrix.Semiring.isScalarTowerₓ'. -/
/-- This instance enables use with `smul_mul_assoc`. -/
instance Semiring.isScalarTower [Fintype n] [Monoid R] [DistribMulAction R α]
    [IsScalarTower R α α] : IsScalarTower R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => Matrix.smul_mul r m n⟩
#align matrix.semiring.is_scalar_tower Matrix.Semiring.isScalarTower

/- warning: matrix.semiring.smul_comm_class -> Matrix.Semiring.smulCommClass is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : Monoid.{u3} R] [_inst_4 : DistribMulAction.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))] [_inst_5 : SMulCommClass.{u3, u1, u1} R α α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4))) (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))], SMulCommClass.{u3, max u2 u1, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.hasSmul.{u1, u2, u2, u3} n n R α (SMulZeroClass.toHasSmul.{u3, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))) (Mul.toSMul.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasMul.{u1, u2} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : Monoid.{u3} R] [_inst_4 : DistribMulAction.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))] [_inst_5 : SMulCommClass.{u3, u1, u1} R α α (SMulZeroClass.toSMul.{u3, u1} R α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4))) (SMulZeroClass.toSMul.{u1, u1} α α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u1, u1} α α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (MulZeroClass.toSMulWithZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))], SMulCommClass.{u3, max u1 u2, max u1 u2} R (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.smul.{u1, u2, u2, u3} n n R α (SMulZeroClass.toSMul.{u3, u1} R α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) (DistribSMul.toSMulZeroClass.{u3, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u3, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))) (SMulZeroClass.toSMul.{max u1 u2, max u1 u2} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.zero.{u1, u2, u2} n n α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))) (SMulWithZero.toSMulZeroClass.{max u1 u2, max u1 u2} (Matrix.{u2, u2, u1} n n α) (Matrix.{u2, u2, u1} n n α) (Matrix.zero.{u1, u2, u2} n n α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))) (Matrix.zero.{u1, u2, u2} n n α (MulZeroClass.toZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))) (MulZeroClass.toSMulWithZero.{max u1 u2} (Matrix.{u2, u2, u1} n n α) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u1 u2} (Matrix.{u2, u2, u1} n n α) (Matrix.nonUnitalNonAssocSemiring.{u1, u2} n α _inst_1 _inst_2)))))
Case conversion may be inaccurate. Consider using '#align matrix.semiring.smul_comm_class Matrix.Semiring.smulCommClassₓ'. -/
/-- This instance enables use with `mul_smul_comm`. -/
instance Semiring.smulCommClass [Fintype n] [Monoid R] [DistribMulAction R α]
    [SMulCommClass R α α] : SMulCommClass R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩
#align matrix.semiring.smul_comm_class Matrix.Semiring.smulCommClass

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

/- warning: matrix.one_mul -> Matrix.one_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.mul.{u1, u2, u2, u3} m m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasOne.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1))))))) M) M
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.mul.{u3, u2, u2, u1} m m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1)) (OfNat.ofNat.{max u3 u2} (Matrix.{u2, u2, u3} m m α) 1 (One.toOfNat1.{max u3 u2} (Matrix.{u2, u2, u3} m m α) (Matrix.one.{u3, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroOneClass.toZero.{u3} α (NonAssocSemiring.toMulZeroOneClass.{u3} α _inst_1)) (NonAssocSemiring.toOne.{u3} α _inst_1)))) M) M
Case conversion may be inaccurate. Consider using '#align matrix.one_mul Matrix.one_mulₓ'. -/
@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) :
    (1 : Matrix m m α) ⬝ M = M := by ext (i j) <;> rw [← diagonal_one, diagonal_mul, one_mul]
#align matrix.one_mul Matrix.one_mul

/- warning: matrix.mul_one -> Matrix.mul_one is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : DecidableEq.{succ u3} n] (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.mul.{u1, u2, u3, u3} m n n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) M (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} n n α) 1 (OfNat.mk.{max u3 u1} (Matrix.{u3, u3, u1} n n α) 1 (One.one.{max u3 u1} (Matrix.{u3, u3, u1} n n α) (Matrix.hasOne.{u1, u3} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))))) M
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] (M : Matrix.{u1, u2, u3} m n α), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u1, u2, u3} m n α) (Matrix.mul.{u3, u1, u2, u2} m n n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1)) M (OfNat.ofNat.{max u3 u2} (Matrix.{u2, u2, u3} n n α) 1 (One.toOfNat1.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.one.{u3, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroOneClass.toZero.{u3} α (NonAssocSemiring.toMulZeroOneClass.{u3} α _inst_1)) (NonAssocSemiring.toOne.{u3} α _inst_1))))) M
Case conversion may be inaccurate. Consider using '#align matrix.mul_one Matrix.mul_oneₓ'. -/
@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) :
    M ⬝ (1 : Matrix n n α) = M := by ext (i j) <;> rw [← diagonal_one, mul_diagonal, mul_one]
#align matrix.mul_one Matrix.mul_one

instance [Fintype n] [DecidableEq n] : NonAssocSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring with
    one := 1
    one_mul := Matrix.one_mul
    mul_one := Matrix.mul_one
    natCast := fun n => diagonal fun _ => n
    natCast_zero := by ext <;> simp [Nat.cast]
    natCast_succ := fun n => by ext <;> by_cases i = j <;> simp [Nat.cast, *] }

/- warning: matrix.map_mul -> Matrix.map_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u4} n] {L : Matrix.{u3, u4, u1} m n α} {M : Matrix.{u4, u5, u1} n o α} [_inst_3 : NonAssocSemiring.{u2} β] {f : RingHom.{u1, u2} α β _inst_1 _inst_3}, Eq.{succ (max u3 u5 u2)} (Matrix.{u3, u5, u2} m o β) (Matrix.map.{u1, u2, u3, u5} m o α β (Matrix.mul.{u1, u3, u4, u5} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) L M) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β _inst_1 _inst_3) (fun (_x : RingHom.{u1, u2} α β _inst_1 _inst_3) => α -> β) (RingHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_3) f)) (Matrix.mul.{u2, u3, u4, u5} m n o β _inst_2 (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_3)) (Matrix.map.{u1, u2, u3, u4} m n α β L (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β _inst_1 _inst_3) (fun (_x : RingHom.{u1, u2} α β _inst_1 _inst_3) => α -> β) (RingHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_3) f)) (Matrix.map.{u1, u2, u4, u5} n o α β M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β _inst_1 _inst_3) (fun (_x : RingHom.{u1, u2} α β _inst_1 _inst_3) => α -> β) (RingHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_3) f)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u4}} {β : Type.{u5}} [_inst_1 : NonAssocSemiring.{u4} α] [_inst_2 : Fintype.{u3} n] {L : Matrix.{u2, u3, u4} m n α} {M : Matrix.{u3, u1, u4} n o α} [_inst_3 : NonAssocSemiring.{u5} β] {f : RingHom.{u4, u5} α β _inst_1 _inst_3}, Eq.{max (max (succ u5) (succ u2)) (succ u1)} (Matrix.{u2, u1, u5} m o β) (Matrix.map.{u4, u5, u2, u1} m o α β (Matrix.mul.{u4, u2, u3, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) L M) (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3) (RingHomClass.toNonUnitalRingHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β _inst_1 _inst_3 (RingHom.instRingHomClassRingHom.{u4, u5} α β _inst_1 _inst_3)))) f)) (Matrix.mul.{u5, u2, u3, u1} m n o β _inst_2 (NonUnitalNonAssocSemiring.toMul.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (Matrix.map.{u4, u5, u2, u3} m n α β L (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3) (RingHomClass.toNonUnitalRingHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β _inst_1 _inst_3 (RingHom.instRingHomClassRingHom.{u4, u5} α β _inst_1 _inst_3)))) f)) (Matrix.map.{u4, u5, u3, u1} n o α β M (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3) (RingHomClass.toNonUnitalRingHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_1 _inst_3) α β _inst_1 _inst_3 (RingHom.instRingHomClassRingHom.{u4, u5} α β _inst_1 _inst_3)))) f)))
Case conversion may be inaccurate. Consider using '#align matrix.map_mul Matrix.map_mulₓ'. -/
@[simp]
theorem map_mul [Fintype n] {L : Matrix m n α} {M : Matrix n o α} [NonAssocSemiring β]
    {f : α →+* β} : (L ⬝ M).map f = L.map f ⬝ M.map f :=
  by
  ext
  simp [mul_apply, RingHom.map_sum]
#align matrix.map_mul Matrix.map_mul

variable (α n)

#print Matrix.diagonalRingHom /-
/-- `matrix.diagonal` as a `ring_hom`. -/
@[simps]
def diagonalRingHom [Fintype n] [DecidableEq n] : (n → α) →+* Matrix n n α :=
  { diagonalAddMonoidHom n α with
    toFun := diagonal
    map_one' := diagonal_one
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }
#align matrix.diagonal_ring_hom Matrix.diagonalRingHom
-/

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α] [Fintype m] [Fintype n]

/- warning: matrix.mul_assoc -> Matrix.mul_assoc is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} α] [_inst_2 : Fintype.{u3} m] [_inst_3 : Fintype.{u4} n] (L : Matrix.{u2, u3, u1} l m α) (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u4, u5, u1} n o α), Eq.{succ (max u2 u5 u1)} (Matrix.{u2, u5, u1} l o α) (Matrix.mul.{u1, u2, u4, u5} l n o α _inst_3 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) L M) N) (Matrix.mul.{u1, u2, u3, u5} l m o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) L (Matrix.mul.{u1, u3, u4, u5} m n o α _inst_3 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) M N))
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : NonUnitalSemiring.{u5} α] [_inst_2 : Fintype.{u3} m] [_inst_3 : Fintype.{u2} n] (L : Matrix.{u4, u3, u5} l m α) (M : Matrix.{u3, u2, u5} m n α) (N : Matrix.{u2, u1, u5} n o α), Eq.{max (max (succ u5) (succ u4)) (succ u1)} (Matrix.{u4, u1, u5} l o α) (Matrix.mul.{u5, u4, u2, u1} l n o α _inst_3 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_1)) (Matrix.mul.{u5, u4, u3, u2} l m n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_1)) L M) N) (Matrix.mul.{u5, u4, u3, u1} l m o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_1)) L (Matrix.mul.{u5, u3, u2, u1} m n o α _inst_3 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_1)) M N))
Case conversion may be inaccurate. Consider using '#align matrix.mul_assoc Matrix.mul_assocₓ'. -/
protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) :
    L ⬝ M ⬝ N = L ⬝ (M ⬝ N) := by
  ext
  apply dot_product_assoc
#align matrix.mul_assoc Matrix.mul_assoc

instance : NonUnitalSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring with mul_assoc := Matrix.mul_assoc }

end NonUnitalSemiring

section Semiring

variable [Semiring α]

instance [Fintype n] [DecidableEq n] : Semiring (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.nonAssocSemiring with }

end Semiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] [Fintype n]

/- warning: matrix.neg_mul -> Matrix.neg_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u3, u4, u1} n o α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} m o α) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) (Neg.neg.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasNeg.{u1, u2, u3} m n α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) M) N) (Neg.neg.{max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.hasNeg.{u1, u2, u4} m o α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) M N))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocRing.{u4} α] [_inst_2 : Fintype.{u2} n] (M : Matrix.{u3, u2, u4} m n α) (N : Matrix.{u2, u1, u4} n o α), Eq.{max (max (succ u4) (succ u3)) (succ u1)} (Matrix.{u3, u1, u4} m o α) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) (Neg.neg.{max (max u4 u3) u2} (Matrix.{u3, u2, u4} m n α) (Matrix.neg.{u4, u3, u2} m n α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toAddCommGroup.{u4} α _inst_1))))))) M) N) (Neg.neg.{max (max u4 u3) u1} (Matrix.{u3, u1, u4} m o α) (Matrix.neg.{u4, u3, u1} m o α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toAddCommGroup.{u4} α _inst_1))))))) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M N))
Case conversion may be inaccurate. Consider using '#align matrix.neg_mul Matrix.neg_mulₓ'. -/
@[simp]
protected theorem neg_mul (M : Matrix m n α) (N : Matrix n o α) : (-M) ⬝ N = -M ⬝ N :=
  by
  ext
  apply neg_dot_product
#align matrix.neg_mul Matrix.neg_mul

/- warning: matrix.mul_neg -> Matrix.mul_neg is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u3, u4, u1} n o α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} m o α) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) M (Neg.neg.{max u3 u4 u1} (Matrix.{u3, u4, u1} n o α) (Matrix.hasNeg.{u1, u3, u4} n o α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) N)) (Neg.neg.{max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.hasNeg.{u1, u2, u4} m o α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) M N))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocRing.{u4} α] [_inst_2 : Fintype.{u2} n] (M : Matrix.{u3, u2, u4} m n α) (N : Matrix.{u2, u1, u4} n o α), Eq.{max (max (succ u4) (succ u3)) (succ u1)} (Matrix.{u3, u1, u4} m o α) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M (Neg.neg.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} n o α) (Matrix.neg.{u4, u2, u1} n o α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toAddCommGroup.{u4} α _inst_1))))))) N)) (Neg.neg.{max (max u4 u3) u1} (Matrix.{u3, u1, u4} m o α) (Matrix.neg.{u4, u3, u1} m o α (NegZeroClass.toNeg.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toAddCommGroup.{u4} α _inst_1))))))) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M N))
Case conversion may be inaccurate. Consider using '#align matrix.mul_neg Matrix.mul_negₓ'. -/
@[simp]
protected theorem mul_neg (M : Matrix m n α) (N : Matrix n o α) : M ⬝ (-N) = -M ⬝ N :=
  by
  ext
  apply dot_product_neg
#align matrix.mul_neg Matrix.mul_neg

/- warning: matrix.sub_mul -> Matrix.sub_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n α) (M' : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u3, u4, u1} n o α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} m o α) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHSub.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasSub.{u1, u2, u3} m n α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)))))) M M') N) (HSub.hSub.{max u2 u4 u1, max u2 u4 u1, max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.{u2, u4, u1} m o α) (Matrix.{u2, u4, u1} m o α) (instHSub.{max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.hasSub.{u1, u2, u4} m o α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)))))) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) M N) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) M' N))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocRing.{u4} α] [_inst_2 : Fintype.{u2} n] (M : Matrix.{u3, u2, u4} m n α) (M' : Matrix.{u3, u2, u4} m n α) (N : Matrix.{u2, u1, u4} n o α), Eq.{max (max (succ u4) (succ u3)) (succ u1)} (Matrix.{u3, u1, u4} m o α) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) (HSub.hSub.{max (max u4 u3) u2, max (max u4 u3) u2, max (max u4 u3) u2} (Matrix.{u3, u2, u4} m n α) (Matrix.{u3, u2, u4} m n α) (Matrix.{u3, u2, u4} m n α) (instHSub.{max (max u4 u3) u2} (Matrix.{u3, u2, u4} m n α) (Matrix.sub.{u4, u3, u2} m n α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α (NonUnitalNonAssocRing.toAddCommGroup.{u4} α _inst_1)))))) M M') N) (HSub.hSub.{max (max u4 u3) u1, max (max u4 u3) u1, max (max u4 u3) u1} (Matrix.{u3, u1, u4} m o α) (Matrix.{u3, u1, u4} m o α) (Matrix.{u3, u1, u4} m o α) (instHSub.{max (max u4 u3) u1} (Matrix.{u3, u1, u4} m o α) (Matrix.sub.{u4, u3, u1} m o α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α (NonUnitalNonAssocRing.toAddCommGroup.{u4} α _inst_1)))))) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M N) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M' N))
Case conversion may be inaccurate. Consider using '#align matrix.sub_mul Matrix.sub_mulₓ'. -/
protected theorem sub_mul (M M' : Matrix m n α) (N : Matrix n o α) :
    (M - M') ⬝ N = M ⬝ N - M' ⬝ N := by
  rw [sub_eq_add_neg, Matrix.add_mul, Matrix.neg_mul, sub_eq_add_neg]
#align matrix.sub_mul Matrix.sub_mul

/- warning: matrix.mul_sub -> Matrix.mul_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u3, u4, u1} n o α) (N' : Matrix.{u3, u4, u1} n o α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} m o α) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) M (HSub.hSub.{max u3 u4 u1, max u3 u4 u1, max u3 u4 u1} (Matrix.{u3, u4, u1} n o α) (Matrix.{u3, u4, u1} n o α) (Matrix.{u3, u4, u1} n o α) (instHSub.{max u3 u4 u1} (Matrix.{u3, u4, u1} n o α) (Matrix.hasSub.{u1, u3, u4} n o α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)))))) N N')) (HSub.hSub.{max u2 u4 u1, max u2 u4 u1, max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.{u2, u4, u1} m o α) (Matrix.{u2, u4, u1} m o α) (instHSub.{max u2 u4 u1} (Matrix.{u2, u4, u1} m o α) (Matrix.hasSub.{u1, u2, u4} m o α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)))))) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) M N) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)) M N'))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocRing.{u4} α] [_inst_2 : Fintype.{u2} n] (M : Matrix.{u3, u2, u4} m n α) (N : Matrix.{u2, u1, u4} n o α) (N' : Matrix.{u2, u1, u4} n o α), Eq.{max (max (succ u4) (succ u3)) (succ u1)} (Matrix.{u3, u1, u4} m o α) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M (HSub.hSub.{max (max u4 u2) u1, max (max u4 u2) u1, max (max u4 u2) u1} (Matrix.{u2, u1, u4} n o α) (Matrix.{u2, u1, u4} n o α) (Matrix.{u2, u1, u4} n o α) (instHSub.{max (max u4 u2) u1} (Matrix.{u2, u1, u4} n o α) (Matrix.sub.{u4, u2, u1} n o α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α (NonUnitalNonAssocRing.toAddCommGroup.{u4} α _inst_1)))))) N N')) (HSub.hSub.{max (max u4 u3) u1, max (max u4 u3) u1, max (max u4 u3) u1} (Matrix.{u3, u1, u4} m o α) (Matrix.{u3, u1, u4} m o α) (Matrix.{u3, u1, u4} m o α) (instHSub.{max (max u4 u3) u1} (Matrix.{u3, u1, u4} m o α) (Matrix.sub.{u4, u3, u1} m o α (SubNegMonoid.toSub.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α (NonUnitalNonAssocRing.toAddCommGroup.{u4} α _inst_1)))))) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M N) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocRing.toMul.{u4} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M N'))
Case conversion may be inaccurate. Consider using '#align matrix.mul_sub Matrix.mul_subₓ'. -/
protected theorem mul_sub (M : Matrix m n α) (N N' : Matrix n o α) :
    M ⬝ (N - N') = M ⬝ N - M ⬝ N' := by
  rw [sub_eq_add_neg, Matrix.mul_add, Matrix.mul_neg, sub_eq_add_neg]
#align matrix.mul_sub Matrix.mul_sub

instance : NonUnitalNonAssocRing (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring, Matrix.addCommGroup with }

end NonUnitalNonAssocRing

instance [Fintype n] [NonUnitalRing α] : NonUnitalRing (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.addCommGroup with }

instance [Fintype n] [DecidableEq n] [NonAssocRing α] : NonAssocRing (Matrix n n α) :=
  { Matrix.nonAssocSemiring, Matrix.addCommGroup with }

instance [Fintype n] [DecidableEq n] [Ring α] : Ring (Matrix n n α) :=
  { Matrix.semiring, Matrix.addCommGroup with }

section Semiring

variable [Semiring α]

/- warning: matrix.diagonal_pow -> Matrix.diagonal_pow is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] (v : n -> α) (k : Nat), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u2, u2, u1} n n α) Nat (Matrix.{u2, u2, u1} n n α) (instHPow.{max u2 u1, 0} (Matrix.{u2, u2, u1} n n α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.semiring.{u1, u2} n α _inst_1 _inst_2 (fun (a : n) (b : n) => _inst_3 a b)))))) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) v) k) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (HPow.hPow.{max u2 u1, 0, max u2 u1} (n -> α) Nat (n -> α) (instHPow.{max u2 u1, 0} (n -> α) Nat (Pi.hasPow.{u2, u1, 0} n Nat (fun (ᾰ : n) => α) (fun (i : n) => Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1))))) v k))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] [_inst_2 : Fintype.{u1} n] [_inst_3 : DecidableEq.{succ u1} n] (v : n -> α) (k : Nat), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u1, u1, u2} n n α) Nat (Matrix.{u1, u1, u2} n n α) (instHPow.{max u2 u1, 0} (Matrix.{u1, u1, u2} n n α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.semiring.{u2, u1} n α _inst_1 _inst_2 (fun (a : n) (b : n) => _inst_3 a b)))))) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_3 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) v) k) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_3 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (n -> α) Nat (n -> α) (instHPow.{max u2 u1, 0} (n -> α) Nat (Pi.instPow.{u1, u2, 0} n Nat (fun (ᾰ : n) => α) (fun (i : n) => Monoid.Pow.{u2} α (MonoidWithZero.toMonoid.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1))))) v k))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_pow Matrix.diagonal_powₓ'. -/
theorem diagonal_pow [Fintype n] [DecidableEq n] (v : n → α) (k : ℕ) :
    diagonal v ^ k = diagonal (v ^ k) :=
  (map_pow (diagonalRingHom n α) v k).symm
#align matrix.diagonal_pow Matrix.diagonal_pow

/- warning: matrix.mul_mul_left -> Matrix.mul_mul_left is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u3, u4, u1} n o α) (a : α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} m o α) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (coeFn.{max 1 (max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))) (succ (max u2 u3 u1)) (succ u2) (succ u3) (succ u1), max (max (succ u2) (succ u3) (succ u1)) (succ (max u2 u3 u1))} (Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) => (m -> n -> α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3) (succ u1), succ (max u2 u3 u1)} (m -> n -> α) (Matrix.{u2, u3, u1} m n α)) (Matrix.of.{u1, u2, u3} m n α) (fun (i : m) (j : n) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a (M i j))) N) (SMul.smul.{u1, max u2 u4 u1} α (Matrix.{u2, u4, u1} m o α) (Matrix.hasSmul.{u1, u2, u4, u1} m o α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))) a (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) M N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : Semiring.{u4} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u4} m n α) (N : Matrix.{u3, u1, u4} n o α) (a : α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m o α) (Matrix.mul.{u4, u2, u3, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_1))) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u4), max (max (succ u3) (succ u2)) (succ u4), max (max (succ u3) (succ u2)) (succ u4)} (Equiv.{max (max (succ u4) (succ u2)) (succ u3), max (max (succ u4) (succ u3)) (succ u2)} (m -> n -> α) (Matrix.{u2, u3, u4} m n α)) (m -> n -> α) (fun (_x : m -> n -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m -> n -> α) => Matrix.{u2, u3, u4} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u3) (succ u2)) (succ u4), max (max (succ u3) (succ u2)) (succ u4)} (m -> n -> α) (Matrix.{u2, u3, u4} m n α)) (Matrix.of.{u4, u2, u3} m n α) (fun (i : m) (j : n) => HMul.hMul.{u4, u4, u4} α α α (instHMul.{u4} α (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_1)))) a (M i j))) N) (HSMul.hSMul.{u4, max (max u1 u2) u4, max (max u4 u2) u1} α (Matrix.{u2, u1, u4} m o α) (Matrix.{u2, u1, u4} m o α) (instHSMul.{u4, max (max u4 u2) u1} α (Matrix.{u2, u1, u4} m o α) (Matrix.smul.{u4, u2, u1, u4} m o α α (SMulZeroClass.toSMul.{u4, u4} α α (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u4, u4} α α (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_1)) (MonoidWithZero.toZero.{u4} α (Semiring.toMonoidWithZero.{u4} α _inst_1)) (MulZeroClass.toSMulWithZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_1)))))))) a (Matrix.mul.{u4, u2, u3, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α _inst_1))) M N))
Case conversion may be inaccurate. Consider using '#align matrix.mul_mul_left Matrix.mul_mul_leftₓ'. -/
@[simp]
theorem mul_mul_left [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (of fun i j => a * M i j) ⬝ N = a • M ⬝ N :=
  smul_mul a M N
#align matrix.mul_mul_left Matrix.mul_mul_left

#print Matrix.scalar /-
/-- The ring homomorphism `α →+* matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [DecidableEq n] [Fintype n] : α →+* Matrix n n α :=
  {
    (smulAddHom α _).flip (1 :
        Matrix n n α) with
    toFun := fun a => a • 1
    map_one' := by simp
    map_mul' := by
      intros
      ext
      simp [mul_assoc] }
#align matrix.scalar Matrix.scalar
-/

section Scalar

variable [DecidableEq n] [Fintype n]

/- warning: matrix.coe_scalar -> Matrix.coe_scalar is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Fintype.{u2} n], Eq.{max (succ u1) (succ (max u2 u1))} ((fun (_x : RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) => α -> (Matrix.{u2, u2, u1} n n α)) (Matrix.scalar.{u2, u1} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3)) (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (fun (_x : RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) => α -> (Matrix.{u2, u2, u1} n n α)) (RingHom.hasCoeToFun.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (Matrix.scalar.{u2, u1} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3)) (fun (a : α) => SMul.smul.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Matrix.hasSmul.{u1, u2, u2, u1} n n α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))) a (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : Fintype.{u1} n], Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) a) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))))) (Matrix.scalar.{u1, u2} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3)) (fun (a : α) => HSMul.hSMul.{u2, max u2 u1, max u2 u1} α (Matrix.{u1, u1, u2} n n α) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) a) (instHSMul.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Matrix.smul.{u2, u1, u1, u2} n n α α (SMulZeroClass.toSMul.{u2, u2} α α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u2, u2} α α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (MulZeroClass.toSMulWithZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)))))))) a (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_2 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (Semiring.toOne.{u2} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.coe_scalar Matrix.coe_scalarₓ'. -/
@[simp]
theorem coe_scalar : (scalar n : α → Matrix n n α) = fun a => a • 1 :=
  rfl
#align matrix.coe_scalar Matrix.coe_scalar

/- warning: matrix.scalar_apply_eq -> Matrix.scalar_apply_eq is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Fintype.{u2} n] (a : α) (i : n), Eq.{succ u1} α (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (fun (_x : RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) => α -> (Matrix.{u2, u2, u1} n n α)) (RingHom.hasCoeToFun.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (Matrix.scalar.{u2, u1} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3) a i i) a
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : Fintype.{u1} n] (a : α) (i : n), Eq.{succ u2} α (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))))) (Matrix.scalar.{u1, u2} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3) a i i) a
Case conversion may be inaccurate. Consider using '#align matrix.scalar_apply_eq Matrix.scalar_apply_eqₓ'. -/
theorem scalar_apply_eq (a : α) (i : n) : scalar n a i i = a := by
  simp only [coe_scalar, smul_eq_mul, mul_one, one_apply_eq, Pi.smul_apply]
#align matrix.scalar_apply_eq Matrix.scalar_apply_eq

/- warning: matrix.scalar_apply_ne -> Matrix.scalar_apply_ne is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Fintype.{u2} n] (a : α) (i : n) (j : n), (Ne.{succ u2} n i j) -> (Eq.{succ u1} α (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (fun (_x : RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) => α -> (Matrix.{u2, u2, u1} n n α)) (RingHom.hasCoeToFun.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (Matrix.scalar.{u2, u1} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3) a i j) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : Fintype.{u1} n] (a : α) (i : n) (j : n), (Ne.{succ u1} n i j) -> (Eq.{succ u2} α (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))))) (Matrix.scalar.{u1, u2} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3) a i j) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.scalar_apply_ne Matrix.scalar_apply_neₓ'. -/
theorem scalar_apply_ne (a : α) (i j : n) (h : i ≠ j) : scalar n a i j = 0 := by
  simp only [h, coe_scalar, one_apply_ne, Ne.def, not_false_iff, Pi.smul_apply, smul_zero]
#align matrix.scalar_apply_ne Matrix.scalar_apply_ne

/- warning: matrix.scalar_inj -> Matrix.scalar_inj is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : Fintype.{u2} n] [_inst_4 : Nonempty.{succ u2} n] {r : α} {s : α}, Iff (Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (fun (_x : RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) => α -> (Matrix.{u2, u2, u1} n n α)) (RingHom.hasCoeToFun.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (Matrix.scalar.{u2, u1} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3) r) (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (fun (_x : RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) => α -> (Matrix.{u2, u2, u1} n n α)) (RingHom.hasCoeToFun.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α _inst_1) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_1) _inst_3 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b))) (Matrix.scalar.{u2, u1} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3) s)) (Eq.{succ u1} α r s)
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : Fintype.{u1} n] [_inst_4 : Nonempty.{succ u1} n] {r : α} {s : α}, Iff (Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) r) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))))) (Matrix.scalar.{u1, u2} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3) r) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b))) α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α _inst_1) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α _inst_1) _inst_3 (fun (a : n) (b : n) => _inst_2 a b)))))) (Matrix.scalar.{u1, u2} α _inst_1 n (fun (a : n) (b : n) => _inst_2 a b) _inst_3) s)) (Eq.{succ u2} α r s)
Case conversion may be inaccurate. Consider using '#align matrix.scalar_inj Matrix.scalar_injₓ'. -/
theorem scalar_inj [Nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s :=
  by
  constructor
  · intro h
    inhabit n
    rw [← scalar_apply_eq r (Inhabited.default n), ← scalar_apply_eq s (Inhabited.default n), h]
  · rintro rfl
    rfl
#align matrix.scalar_inj Matrix.scalar_inj

end Scalar

end Semiring

section CommSemiring

variable [CommSemiring α] [Fintype n]

/- warning: matrix.smul_eq_mul_diagonal -> Matrix.smul_eq_mul_diagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : DecidableEq.{succ u3} n] (M : Matrix.{u2, u3, u1} m n α) (a : α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (SMul.smul.{u1, max u2 u3 u1} α (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u1} m n α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))))) a M) (Matrix.mul.{u1, u2, u3, u3} m n n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) M (Matrix.diagonal.{u1, u3} n α (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (fun (_x : n) => a)))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : CommSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] (M : Matrix.{u1, u2, u3} m n α) (a : α), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u1, u2, u3} m n α) (HSMul.hSMul.{u3, max (max u3 u1) u2, max (max u3 u1) u2} α (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (instHSMul.{u3, max (max u3 u1) u2} α (Matrix.{u1, u2, u3} m n α) (Matrix.smul.{u3, u1, u2, u3} m n α α (Algebra.toSMul.{u3, u3} α α _inst_1 (CommSemiring.toSemiring.{u3} α _inst_1) (Algebra.id.{u3} α _inst_1)))) a M) (Matrix.mul.{u3, u1, u2, u2} m n n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α (CommSemiring.toSemiring.{u3} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α (CommSemiring.toSemiring.{u3} α _inst_1)))) M (Matrix.diagonal.{u3, u2} n α (fun (a : n) (b : n) => _inst_3 a b) (CommMonoidWithZero.toZero.{u3} α (CommSemiring.toCommMonoidWithZero.{u3} α _inst_1)) (fun (_x : n) => a)))
Case conversion may be inaccurate. Consider using '#align matrix.smul_eq_mul_diagonal Matrix.smul_eq_mul_diagonalₓ'. -/
theorem smul_eq_mul_diagonal [DecidableEq n] (M : Matrix m n α) (a : α) :
    a • M = M ⬝ diagonal fun _ => a := by
  ext
  simp [mul_comm]
#align matrix.smul_eq_mul_diagonal Matrix.smul_eq_mul_diagonal

/- warning: matrix.mul_mul_right -> Matrix.mul_mul_right is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u3, u4, u1} n o α) (a : α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} m o α) (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) M (coeFn.{max 1 (max (max (succ u3) (succ u4) (succ u1)) (succ (max u3 u4 u1))) (succ (max u3 u4 u1)) (succ u3) (succ u4) (succ u1), max (max (succ u3) (succ u4) (succ u1)) (succ (max u3 u4 u1))} (Equiv.{max (succ u3) (succ u4) (succ u1), succ (max u3 u4 u1)} (n -> o -> α) (Matrix.{u3, u4, u1} n o α)) (fun (_x : Equiv.{max (succ u3) (succ u4) (succ u1), succ (max u3 u4 u1)} (n -> o -> α) (Matrix.{u3, u4, u1} n o α)) => (n -> o -> α) -> (Matrix.{u3, u4, u1} n o α)) (Equiv.hasCoeToFun.{max (succ u3) (succ u4) (succ u1), succ (max u3 u4 u1)} (n -> o -> α) (Matrix.{u3, u4, u1} n o α)) (Matrix.of.{u1, u3, u4} n o α) (fun (i : n) (j : o) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) a (N i j)))) (SMul.smul.{u1, max u2 u4 u1} α (Matrix.{u2, u4, u1} m o α) (Matrix.hasSmul.{u1, u2, u4, u1} m o α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))))) a (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) M N))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : CommSemiring.{u4} α] [_inst_2 : Fintype.{u2} n] (M : Matrix.{u3, u2, u4} m n α) (N : Matrix.{u2, u1, u4} n o α) (a : α), Eq.{max (max (succ u4) (succ u3)) (succ u1)} (Matrix.{u3, u1, u4} m o α) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α (CommSemiring.toSemiring.{u4} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α (CommSemiring.toSemiring.{u4} α _inst_1)))) M (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4)} (Equiv.{max (max (succ u4) (succ u2)) (succ u1), max (max (succ u4) (succ u1)) (succ u2)} (n -> o -> α) (Matrix.{u2, u1, u4} n o α)) (n -> o -> α) (fun (_x : n -> o -> α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : n -> o -> α) => Matrix.{u2, u1, u4} n o α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u4), max (max (succ u1) (succ u2)) (succ u4)} (n -> o -> α) (Matrix.{u2, u1, u4} n o α)) (Matrix.of.{u4, u2, u1} n o α) (fun (i : n) (j : o) => HMul.hMul.{u4, u4, u4} α α α (instHMul.{u4} α (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α (CommSemiring.toSemiring.{u4} α _inst_1))))) a (N i j)))) (HSMul.hSMul.{u4, max (max u1 u3) u4, max (max u4 u3) u1} α (Matrix.{u3, u1, u4} m o α) (Matrix.{u3, u1, u4} m o α) (instHSMul.{u4, max (max u4 u3) u1} α (Matrix.{u3, u1, u4} m o α) (Matrix.smul.{u4, u3, u1, u4} m o α α (Algebra.toSMul.{u4, u4} α α _inst_1 (CommSemiring.toSemiring.{u4} α _inst_1) (Algebra.id.{u4} α _inst_1)))) a (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α (CommSemiring.toSemiring.{u4} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α (Semiring.toNonAssocSemiring.{u4} α (CommSemiring.toSemiring.{u4} α _inst_1)))) M N))
Case conversion may be inaccurate. Consider using '#align matrix.mul_mul_right Matrix.mul_mul_rightₓ'. -/
@[simp]
theorem mul_mul_right (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (M ⬝ of fun i j => a * N i j) = a • M ⬝ N :=
  mul_smul M a N
#align matrix.mul_mul_right Matrix.mul_mul_right

/- warning: matrix.scalar.commute -> Matrix.scalar.commute is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] (r : α) (M : Matrix.{u2, u2, u1} n n α), Commute.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasMul.{u1, u2} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_3 a b) a b))) (fun (_x : RingHom.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_3 a b) a b))) => α -> (Matrix.{u2, u2, u1} n n α)) (RingHom.hasCoeToFun.{u1, max u2 u1} α (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) _inst_2 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_3 a b) a b))) (Matrix.scalar.{u2, u1} α (CommSemiring.toSemiring.{u1} α _inst_1) n (fun (a : n) (b : n) => _inst_3 a b) _inst_2) r) M
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommSemiring.{u2} α] [_inst_2 : Fintype.{u1} n] [_inst_3 : DecidableEq.{succ u1} n] (r : α) (M : Matrix.{u1, u1, u2} n n α), Commute.{max u2 u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) r) (Matrix.instMulMatrix.{u2, u1} n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1))))) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) _inst_2 (fun (a : n) (b : n) => _inst_3 a b))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Matrix.{u1, u1, u2} n n α) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) _inst_2 (fun (a : n) (b : n) => _inst_3 a b))) α (Matrix.{u1, u1, u2} n n α) (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) _inst_2 (fun (a : n) (b : n) => _inst_3 a b)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) _inst_2 (fun (a : n) (b : n) => _inst_3 a b))) α (Matrix.{u1, u1, u2} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) _inst_2 (fun (a : n) (b : n) => _inst_3 a b))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) _inst_2 (fun (a : n) (b : n) => _inst_3 a b))) α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) _inst_2 (fun (a : n) (b : n) => _inst_3 a b)) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} α (Matrix.{u1, u1, u2} n n α) (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) (Matrix.nonAssocSemiring.{u2, u1} n α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) _inst_2 (fun (a : n) (b : n) => _inst_3 a b)))))) (Matrix.scalar.{u1, u2} α (CommSemiring.toSemiring.{u2} α _inst_1) n (fun (a : n) (b : n) => _inst_3 a b) _inst_2) r) M
Case conversion may be inaccurate. Consider using '#align matrix.scalar.commute Matrix.scalar.commuteₓ'. -/
theorem scalar.commute [DecidableEq n] (r : α) (M : Matrix n n α) : Commute (scalar n r) M := by
  simp [Commute, SemiconjBy]
#align matrix.scalar.commute Matrix.scalar.commute

end CommSemiring

section Algebra

variable [Fintype n] [DecidableEq n]

variable [CommSemiring R] [Semiring α] [Semiring β] [Algebra R α] [Algebra R β]

instance : Algebra R (Matrix n n α) :=
  {
    (Matrix.scalar n).comp
      (algebraMap R
        α) with
    commutes' := fun r x => by ext;
      simp [Matrix.scalar, Matrix.mul_apply, Matrix.one_apply, Algebra.commutes, smul_ite]
    smul_def' := fun r x => by ext; simp [Matrix.scalar, Algebra.smul_def r] }

/- warning: matrix.algebra_map_matrix_apply -> Matrix.algebraMap_matrix_apply is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u1} α] [_inst_6 : Algebra.{u3, u1} R α _inst_3 _inst_4] {r : R} {i : n} {j : n}, Eq.{succ u1} α (coeFn.{max (succ u3) (succ (max u2 u1)), max (succ u3) (succ (max u2 u1))} (RingHom.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (fun (_x : RingHom.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) => R -> (Matrix.{u2, u2, u1} n n α)) (RingHom.hasCoeToFun.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (algebraMap.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) _inst_3 (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.algebra.{u1, u2, u3} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)) r i j) (ite.{succ u1} α (Eq.{succ u2} n i j) (_inst_2 i j) (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (RingHom.{u3, u1} R α (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{u1} α _inst_4)) (fun (_x : RingHom.{u3, u1} R α (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{u1} α _inst_4)) => R -> α) (RingHom.hasCoeToFun.{u3, u1} R α (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{u1} α _inst_4)) (algebraMap.{u3, u1} R α _inst_3 _inst_4 _inst_6) r) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4))))))))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : Semiring.{u3} α] [_inst_6 : Algebra.{u1, u3} R α _inst_3 _inst_4] {r : R} {i : n} {j : n}, Eq.{succ u3} α (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u1, max (succ u3) (succ u2)} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Matrix.{u2, u2, u3} n n α) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u3} n n α) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u3} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))) (RingHom.instRingHomClassRingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))))) (algebraMap.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) _inst_3 (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)) r i j) (ite.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => α) r) (Eq.{succ u2} n i j) (_inst_2 i j) (FunLike.coe.{max (succ u3) (succ u1), succ u1, succ u3} (RingHom.{u1, u3} R α (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => α) _x) (MulHomClass.toFunLike.{max u3 u1, u1, u3} (RingHom.{u1, u3} R α (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4)) R α (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))) (NonUnitalRingHomClass.toMulHomClass.{max u3 u1, u1, u3} (RingHom.{u1, u3} R α (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4)) R α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)) (RingHomClass.toNonUnitalRingHomClass.{max u3 u1, u1, u3} (RingHom.{u1, u3} R α (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4)) R α (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4) (RingHom.instRingHomClassRingHom.{u1, u3} R α (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4))))) (algebraMap.{u1, u3} R α _inst_3 _inst_4 _inst_6) r) (OfNat.ofNat.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => α) r) 0 (Zero.toOfNat0.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => α) r) (MonoidWithZero.toZero.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => α) r) (Semiring.toMonoidWithZero.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => α) r) _inst_4)))))
Case conversion may be inaccurate. Consider using '#align matrix.algebra_map_matrix_apply Matrix.algebraMap_matrix_applyₓ'. -/
theorem algebraMap_matrix_apply {r : R} {i j : n} :
    algebraMap R (Matrix n n α) r i j = if i = j then algebraMap R α r else 0 :=
  by
  dsimp [algebraMap, Algebra.toRingHom, Matrix.scalar]
  split_ifs with h <;> simp [h, Matrix.one_apply_ne]
#align matrix.algebra_map_matrix_apply Matrix.algebraMap_matrix_apply

/- warning: matrix.algebra_map_eq_diagonal -> Matrix.algebraMap_eq_diagonal is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u1} α] [_inst_6 : Algebra.{u3, u1} R α _inst_3 _inst_4] (r : R), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (coeFn.{max (succ u3) (succ (max u2 u1)), max (succ u3) (succ (max u2 u1))} (RingHom.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (fun (_x : RingHom.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) => R -> (Matrix.{u2, u2, u1} n n α)) (RingHom.hasCoeToFun.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (algebraMap.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) _inst_3 (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.algebra.{u1, u2, u3} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)) r) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))) (coeFn.{max (succ u3) (succ (max u2 u1)), max (succ u3) (succ (max u2 u1))} (RingHom.{u3, max u2 u1} R (n -> α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (n -> α) (Pi.semiring.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)))) (fun (_x : RingHom.{u3, max u2 u1} R (n -> α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (n -> α) (Pi.semiring.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)))) => R -> n -> α) (RingHom.hasCoeToFun.{u3, max u2 u1} R (n -> α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (n -> α) (Pi.semiring.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)))) (algebraMap.{u3, max u2 u1} R (n -> α) _inst_3 (Pi.semiring.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)) (Function.algebra.{u3, u2, u1} R n α _inst_3 _inst_4 _inst_6)) r))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : Semiring.{u3} α] [_inst_6 : Algebra.{u1, u3} R α _inst_3 _inst_4] (r : R), Eq.{max (succ u3) (succ u2)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Matrix.{u2, u2, u3} n n α) r) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u1, max (succ u3) (succ u2)} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Matrix.{u2, u2, u3} n n α) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u3} n n α) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u3} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))) (RingHom.instRingHomClassRingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))))) (algebraMap.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) _inst_3 (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)) r) (Matrix.diagonal.{u3, u2} n α (fun (a : n) (b : n) => _inst_2 a b) (MonoidWithZero.toZero.{u3} α (Semiring.toMonoidWithZero.{u3} α _inst_4)) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u1, max (succ u3) (succ u2)} (RingHom.{u1, max u3 u2} R (n -> α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (n -> α) (Pi.semiring.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) (fun (i : n) => _inst_4)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => n -> α) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (n -> α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (n -> α) (Pi.semiring.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) (fun (i : n) => _inst_4)))) R (n -> α) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{max u3 u2} (n -> α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (n -> α) (Semiring.toNonAssocSemiring.{max u3 u2} (n -> α) (Pi.semiring.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) (fun (i : n) => _inst_4))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (n -> α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (n -> α) (Pi.semiring.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) (fun (i : n) => _inst_4)))) R (n -> α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (n -> α) (Semiring.toNonAssocSemiring.{max u3 u2} (n -> α) (Pi.semiring.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) (fun (i : n) => _inst_4)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (n -> α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (n -> α) (Pi.semiring.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) (fun (i : n) => _inst_4)))) R (n -> α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (n -> α) (Pi.semiring.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) (fun (i : n) => _inst_4))) (RingHom.instRingHomClassRingHom.{u1, max u3 u2} R (n -> α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (n -> α) (Pi.semiring.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) (fun (i : n) => _inst_4))))))) (algebraMap.{u1, max u3 u2} R (n -> α) _inst_3 (Pi.semiring.{u2, u3} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)) (Pi.algebra.{u2, u3, u1} n R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14213 : n) => α) _inst_3 (fun (i : n) => _inst_4) (fun (i : n) => _inst_6))) r))
Case conversion may be inaccurate. Consider using '#align matrix.algebra_map_eq_diagonal Matrix.algebraMap_eq_diagonalₓ'. -/
theorem algebraMap_eq_diagonal (r : R) :
    algebraMap R (Matrix n n α) r = diagonal (algebraMap R (n → α) r) :=
  Matrix.ext fun i j => algebraMap_matrix_apply
#align matrix.algebra_map_eq_diagonal Matrix.algebraMap_eq_diagonal

/- warning: matrix.algebra_map_eq_smul -> Matrix.algebraMap_eq_smul is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_1 : Fintype.{u1} n] [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : CommSemiring.{u2} R] (r : R), Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} n n R) (coeFn.{max (succ u2) (succ (max u1 u2)), max (succ u2) (succ (max u1 u2))} (RingHom.{u2, max u1 u2} R (Matrix.{u1, u1, u2} n n R) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (fun (_x : RingHom.{u2, max u1 u2} R (Matrix.{u1, u1, u2} n n R) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) => R -> (Matrix.{u1, u1, u2} n n R)) (RingHom.hasCoeToFun.{u2, max u1 u2} R (Matrix.{u1, u1, u2} n n R) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (algebraMap.{u2, max u1 u2} R (Matrix.{u1, u1, u2} n n R) _inst_3 (Matrix.semiring.{u2, u1} n R (CommSemiring.toSemiring.{u2} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.algebra.{u2, u1, u2} n R R _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 (CommSemiring.toSemiring.{u2} R _inst_3) (Algebra.id.{u2} R _inst_3))) r) (SMul.smul.{u2, max u1 u2} R (Matrix.{u1, u1, u2} n n R) (Matrix.hasSmul.{u2, u1, u1, u2} n n R R (Mul.toSMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3))))))) r (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (OfNat.mk.{max u1 u2} (Matrix.{u1, u1, u2} n n R) 1 (One.one.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasOne.{u2, u1} n R (fun (a : n) (b : n) => _inst_2 a b) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3))))) (AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3))))))))))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u1} R] (r : R), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Matrix.{u2, u2, u1} n n R) r) (FunLike.coe.{max (succ u2) (succ u1), succ u1, max (succ u2) (succ u1)} (RingHom.{u1, max u1 u2} R (Matrix.{u2, u2, u1} n n R) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Matrix.{u2, u2, u1} n n R) _x) (MulHomClass.toFunLike.{max u2 u1, u1, max u2 u1} (RingHom.{u1, max u1 u2} R (Matrix.{u2, u2, u1} n n R) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u1} n n R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u1, max u2 u1} (RingHom.{u1, max u1 u2} R (Matrix.{u2, u2, u1} n n R) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u1} n n R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u1, max u2 u1} (RingHom.{u1, max u1 u2} R (Matrix.{u2, u2, u1} n n R) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u2, u2, u1} n n R) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b))) (RingHom.instRingHomClassRingHom.{u1, max u2 u1} R (Matrix.{u2, u2, u1} n n R) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u1 u2} (Matrix.{u2, u2, u1} n n R) (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))))) (algebraMap.{u1, max u1 u2} R (Matrix.{u2, u2, u1} n n R) _inst_3 (Matrix.semiring.{u1, u2} n R (CommSemiring.toSemiring.{u1} R _inst_3) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u1} n R R _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 (CommSemiring.toSemiring.{u1} R _inst_3) (Algebra.id.{u1} R _inst_3))) r) (HSMul.hSMul.{u1, max u2 u1, max u2 u1} R (Matrix.{u2, u2, u1} n n R) (Matrix.{u2, u2, u1} n n R) (instHSMul.{u1, max u2 u1} R (Matrix.{u2, u2, u1} n n R) (Matrix.smul.{u1, u2, u2, u1} n n R R (Algebra.toSMul.{u1, u1} R R _inst_3 (CommSemiring.toSemiring.{u1} R _inst_3) (Algebra.id.{u1} R _inst_3)))) r (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n R) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.one.{u1, u2} n R (fun (a : n) (b : n) => _inst_2 a b) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_3)) (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))))))
Case conversion may be inaccurate. Consider using '#align matrix.algebra_map_eq_smul Matrix.algebraMap_eq_smulₓ'. -/
@[simp]
theorem algebraMap_eq_smul (r : R) : algebraMap R (Matrix n n R) r = r • (1 : Matrix n n R) :=
  rfl
#align matrix.algebra_map_eq_smul Matrix.algebraMap_eq_smul

/- warning: matrix.algebra_map_eq_diagonal_ring_hom -> Matrix.algebraMap_eq_diagonalRingHom is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u1} α] [_inst_6 : Algebra.{u3, u1} R α _inst_3 _inst_4], Eq.{max (succ u3) (succ (max u2 u1))} (RingHom.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Semiring.toNonAssocSemiring.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (algebraMap.{u3, max u2 u1} R (Matrix.{u2, u2, u1} n n α) _inst_3 (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.algebra.{u1, u2, u3} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)) (RingHom.comp.{u3, max u2 u1, max u2 u1} R (n -> α) (Matrix.{u2, u2, u1} n n α) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)) (Pi.nonAssocSemiring.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => Semiring.toNonAssocSemiring.{u1} α _inst_4)) (Matrix.nonAssocSemiring.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_4) _inst_1 (fun (a : n) (b : n) => (fun (a : n) (b : n) => _inst_2 a b) a b)) (Matrix.diagonalRingHom.{u1, u2} n α (Semiring.toNonAssocSemiring.{u1} α _inst_4) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (algebraMap.{u3, max u2 u1} R (n -> α) _inst_3 (Pi.semiring.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)) (Function.algebra.{u3, u2, u1} R n α _inst_3 _inst_4 _inst_6)))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : Semiring.{u3} α] [_inst_6 : Algebra.{u1, u3} R α _inst_3 _inst_4], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (RingHom.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u2, u2, u3} n n α) (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (algebraMap.{u1, max u3 u2} R (Matrix.{u2, u2, u3} n n α) _inst_3 (Matrix.semiring.{u3, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)) (RingHom.comp.{u1, max u3 u2, max u3 u2} R (n -> α) (Matrix.{u2, u2, u3} n n α) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (Pi.nonAssocSemiring.{u2, u3} n (fun (ᾰ : n) => α) (fun (i : n) => Semiring.toNonAssocSemiring.{u3} α _inst_4)) (Matrix.nonAssocSemiring.{u3, u2} n α (Semiring.toNonAssocSemiring.{u3} α _inst_4) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.diagonalRingHom.{u3, u2} n α (Semiring.toNonAssocSemiring.{u3} α _inst_4) _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (algebraMap.{u1, max u3 u2} R (n -> α) _inst_3 (Pi.semiring.{u2, u3} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)) (Pi.algebra.{u2, u3, u1} n R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.12264 : n) => α) _inst_3 (fun (i : n) => _inst_4) (fun (i : n) => _inst_6))))
Case conversion may be inaccurate. Consider using '#align matrix.algebra_map_eq_diagonal_ring_hom Matrix.algebraMap_eq_diagonalRingHomₓ'. -/
theorem algebraMap_eq_diagonalRingHom :
    algebraMap R (Matrix n n α) = (diagonalRingHom n α).comp (algebraMap R _) :=
  RingHom.ext algebraMap_eq_diagonal
#align matrix.algebra_map_eq_diagonal_ring_hom Matrix.algebraMap_eq_diagonalRingHom

/- warning: matrix.map_algebra_map -> Matrix.map_algebraMap is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} n] [_inst_2 : DecidableEq.{succ u3} n] [_inst_3 : CommSemiring.{u4} R] [_inst_4 : Semiring.{u1} α] [_inst_5 : Semiring.{u2} β] [_inst_6 : Algebra.{u4, u1} R α _inst_3 _inst_4] [_inst_7 : Algebra.{u4, u2} R β _inst_3 _inst_5] (r : R) (f : α -> β), (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_4)))))))) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_5)))))))) -> (Eq.{succ u2} β (f (coeFn.{max (succ u4) (succ u1), max (succ u4) (succ u1)} (RingHom.{u4, u1} R α (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{u1} α _inst_4)) (fun (_x : RingHom.{u4, u1} R α (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{u1} α _inst_4)) => R -> α) (RingHom.hasCoeToFun.{u4, u1} R α (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{u1} α _inst_4)) (algebraMap.{u4, u1} R α _inst_3 _inst_4 _inst_6) r)) (coeFn.{max (succ u4) (succ u2), max (succ u4) (succ u2)} (RingHom.{u4, u2} R β (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{u2} β _inst_5)) (fun (_x : RingHom.{u4, u2} R β (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{u2} β _inst_5)) => R -> β) (RingHom.hasCoeToFun.{u4, u2} R β (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{u2} β _inst_5)) (algebraMap.{u4, u2} R β _inst_3 _inst_5 _inst_7) r)) -> (Eq.{succ (max u3 u2)} (Matrix.{u3, u3, u2} n n β) (Matrix.map.{u1, u2, u3, u3} n n α β (coeFn.{max (succ u4) (succ (max u3 u1)), max (succ u4) (succ (max u3 u1))} (RingHom.{u4, max u3 u1} R (Matrix.{u3, u3, u1} n n α) (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u3, u3, u1} n n α) (Matrix.semiring.{u1, u3} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (fun (_x : RingHom.{u4, max u3 u1} R (Matrix.{u3, u3, u1} n n α) (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u3, u3, u1} n n α) (Matrix.semiring.{u1, u3} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) => R -> (Matrix.{u3, u3, u1} n n α)) (RingHom.hasCoeToFun.{u4, max u3 u1} R (Matrix.{u3, u3, u1} n n α) (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u3, u3, u1} n n α) (Matrix.semiring.{u1, u3} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (algebraMap.{u4, max u3 u1} R (Matrix.{u3, u3, u1} n n α) _inst_3 (Matrix.semiring.{u1, u3} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.algebra.{u1, u3, u4} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)) r) f) (coeFn.{max (succ u4) (succ (max u3 u2)), max (succ u4) (succ (max u3 u2))} (RingHom.{u4, max u3 u2} R (Matrix.{u3, u3, u2} n n β) (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u3, u3, u2} n n β) (Matrix.semiring.{u2, u3} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (fun (_x : RingHom.{u4, max u3 u2} R (Matrix.{u3, u3, u2} n n β) (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u3, u3, u2} n n β) (Matrix.semiring.{u2, u3} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) => R -> (Matrix.{u3, u3, u2} n n β)) (RingHom.hasCoeToFun.{u4, max u3 u2} R (Matrix.{u3, u3, u2} n n β) (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u2} (Matrix.{u3, u3, u2} n n β) (Matrix.semiring.{u2, u3} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (algebraMap.{u4, max u3 u2} R (Matrix.{u3, u3, u2} n n β) _inst_3 (Matrix.semiring.{u2, u3} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.algebra.{u2, u3, u4} n R β _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_5 _inst_7)) r))
but is expected to have type
  forall {n : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Fintype.{u1} n] [_inst_2 : DecidableEq.{succ u1} n] [_inst_3 : CommSemiring.{u2} R] [_inst_4 : Semiring.{u3} α] [_inst_5 : Semiring.{u4} β] [_inst_6 : Algebra.{u2, u3} R α _inst_3 _inst_4] [_inst_7 : Algebra.{u2, u4} R β _inst_3 _inst_5] (r : R) (f : α -> β), (Eq.{succ u4} β (f (OfNat.ofNat.{u3} α 0 (Zero.toOfNat0.{u3} α (MonoidWithZero.toZero.{u3} α (Semiring.toMonoidWithZero.{u3} α _inst_4))))) (OfNat.ofNat.{u4} β 0 (Zero.toOfNat0.{u4} β (MonoidWithZero.toZero.{u4} β (Semiring.toMonoidWithZero.{u4} β _inst_5))))) -> (Eq.{succ u4} β (f (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (RingHom.{u2, u3} R α (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => α) _x) (MulHomClass.toFunLike.{max u3 u2, u2, u3} (RingHom.{u2, u3} R α (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4)) R α (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4))) (NonUnitalRingHomClass.toMulHomClass.{max u3 u2, u2, u3} (RingHom.{u2, u3} R α (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4)) R α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α _inst_4)) (RingHomClass.toNonUnitalRingHomClass.{max u3 u2, u2, u3} (RingHom.{u2, u3} R α (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4)) R α (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4) (RingHom.instRingHomClassRingHom.{u2, u3} R α (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u3} α _inst_4))))) (algebraMap.{u2, u3} R α _inst_3 _inst_4 _inst_6) r)) (FunLike.coe.{max (succ u4) (succ u2), succ u2, succ u4} (RingHom.{u2, u4} R β (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u4} β _inst_5)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => β) _x) (MulHomClass.toFunLike.{max u4 u2, u2, u4} (RingHom.{u2, u4} R β (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u4} β _inst_5)) R β (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β (Semiring.toNonAssocSemiring.{u4} β _inst_5))) (NonUnitalRingHomClass.toMulHomClass.{max u4 u2, u2, u4} (RingHom.{u2, u4} R β (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u4} β _inst_5)) R β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β (Semiring.toNonAssocSemiring.{u4} β _inst_5)) (RingHomClass.toNonUnitalRingHomClass.{max u4 u2, u2, u4} (RingHom.{u2, u4} R β (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u4} β _inst_5)) R β (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u4} β _inst_5) (RingHom.instRingHomClassRingHom.{u2, u4} R β (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{u4} β _inst_5))))) (algebraMap.{u2, u4} R β _inst_3 _inst_5 _inst_7) r)) -> (Eq.{max (succ u4) (succ u1)} (Matrix.{u1, u1, u4} n n β) (Matrix.map.{u3, u4, u1, u1} n n α β (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), succ u2, max (succ u3) (succ u1)} (RingHom.{u2, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Matrix.{u1, u1, u3} n n α) _x) (MulHomClass.toFunLike.{max (max u3 u1) u2, u2, max u3 u1} (RingHom.{u2, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u1, u1, u3} n n α) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u3 u1) u2, u2, max u3 u1} (RingHom.{u2, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u1, u1, u3} n n α) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u3 u1) u2, u2, max u3 u1} (RingHom.{u2, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u1, u1, u3} n n α) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))) (RingHom.instRingHomClassRingHom.{u2, max u3 u1} R (Matrix.{u1, u1, u3} n n α) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u3 u1} (Matrix.{u1, u1, u3} n n α) (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))))) (algebraMap.{u2, max u3 u1} R (Matrix.{u1, u1, u3} n n α) _inst_3 (Matrix.semiring.{u3, u1} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u1, u2} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)) r) f) (FunLike.coe.{max (max (succ u4) (succ u1)) (succ u2), succ u2, max (succ u4) (succ u1)} (RingHom.{u2, max u4 u1} R (Matrix.{u1, u1, u4} n n β) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Matrix.{u1, u1, u4} n n β) _x) (MulHomClass.toFunLike.{max (max u4 u1) u2, u2, max u4 u1} (RingHom.{u2, max u4 u1} R (Matrix.{u1, u1, u4} n n β) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u1, u1, u4} n n β) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)))) (NonUnitalNonAssocSemiring.toMul.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Semiring.toNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u4 u1) u2, u2, max u4 u1} (RingHom.{u2, max u4 u1} R (Matrix.{u1, u1, u4} n n β) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u1, u1, u4} n n β) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Semiring.toNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u4 u1) u2, u2, max u4 u1} (RingHom.{u2, max u4 u1} R (Matrix.{u1, u1, u4} n n β) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)))) R (Matrix.{u1, u1, u4} n n β) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))) (RingHom.instRingHomClassRingHom.{u2, max u4 u1} R (Matrix.{u1, u1, u4} n n β) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_3)) (Semiring.toNonAssocSemiring.{max u4 u1} (Matrix.{u1, u1, u4} n n β) (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b))))))) (algebraMap.{u2, max u4 u1} R (Matrix.{u1, u1, u4} n n β) _inst_3 (Matrix.semiring.{u4, u1} n β _inst_5 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u4, u1, u2} n R β _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_5 _inst_7)) r))
Case conversion may be inaccurate. Consider using '#align matrix.map_algebra_map Matrix.map_algebraMapₓ'. -/
@[simp]
theorem map_algebraMap (r : R) (f : α → β) (hf : f 0 = 0)
    (hf₂ : f (algebraMap R α r) = algebraMap R β r) :
    (algebraMap R (Matrix n n α) r).map f = algebraMap R (Matrix n n β) r :=
  by
  rw [algebra_map_eq_diagonal, algebra_map_eq_diagonal, diagonal_map hf]
  congr 1 with x
  simp only [hf₂, Pi.algebraMap_apply]
#align matrix.map_algebra_map Matrix.map_algebraMap

variable (R)

/- warning: matrix.diagonal_alg_hom -> Matrix.diagonalAlgHom is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} (R : Type.{u3}) {α : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u1} α] [_inst_6 : Algebra.{u3, u1} R α _inst_3 _inst_4], AlgHom.{u3, max u2 u1, max u2 u1} R (n -> α) (Matrix.{u2, u2, u1} n n α) _inst_3 (Pi.semiring.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Function.algebra.{u3, u2, u1} R n α _inst_3 _inst_4 _inst_6) (Matrix.algebra.{u1, u2, u3} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)
but is expected to have type
  forall {n : Type.{u2}} (R : Type.{u3}) {α : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : DecidableEq.{succ u2} n] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u1} α] [_inst_6 : Algebra.{u3, u1} R α _inst_3 _inst_4], AlgHom.{u3, max u1 u2, max u1 u2} R (n -> α) (Matrix.{u2, u2, u1} n n α) _inst_3 (Pi.semiring.{u2, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_4)) (Matrix.semiring.{u1, u2} n α _inst_4 _inst_1 (fun (a : n) (b : n) => _inst_2 a b)) (Pi.algebra.{u2, u1, u3} n R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.14598 : n) => α) _inst_3 (fun (i : n) => _inst_4) (fun (i : n) => _inst_6)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u3} n R α _inst_1 (fun (a : n) (b : n) => _inst_2 a b) _inst_3 _inst_4 _inst_6)
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_alg_hom Matrix.diagonalAlgHomₓ'. -/
/-- `matrix.diagonal` as an `alg_hom`. -/
@[simps]
def diagonalAlgHom : (n → α) →ₐ[R] Matrix n n α :=
  { diagonalRingHom n α with
    toFun := diagonal
    commutes' := fun r => (algebraMap_eq_diagonal r).symm }
#align matrix.diagonal_alg_hom Matrix.diagonalAlgHom

end Algebra

end Matrix

/-!
### Bundled versions of `matrix.map`
-/


namespace Equiv

#print Equiv.mapMatrix /-
/-- The `equiv` between spaces of matrices induced by an `equiv` between their
coefficients. This is `matrix.map` as an `equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ β) : Matrix m n α ≃ Matrix m n β
    where
  toFun M := M.map f
  invFun M := M.map f.symm
  left_inv M := Matrix.ext fun _ _ => f.symm_apply_apply _
  right_inv M := Matrix.ext fun _ _ => f.apply_symm_apply _
#align equiv.map_matrix Equiv.mapMatrix
-/

/- warning: equiv.map_matrix_refl -> Equiv.mapMatrix_refl is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}}, Eq.{succ (max u2 u3 u1)} (Equiv.{succ (max u2 u3 u1), succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α)) (Equiv.mapMatrix.{u1, u1, u2, u3} m n α α (Equiv.refl.{succ u1} α)) (Equiv.refl.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}}, Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Equiv.{max (max (succ u3) (succ u1)) (succ u2), max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α)) (Equiv.mapMatrix.{u3, u3, u2, u1} m n α α (Equiv.refl.{succ u3} α)) (Equiv.refl.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} m n α))
Case conversion may be inaccurate. Consider using '#align equiv.map_matrix_refl Equiv.mapMatrix_reflₓ'. -/
@[simp]
theorem mapMatrix_refl : (Equiv.refl α).mapMatrix = Equiv.refl (Matrix m n α) :=
  rfl
#align equiv.map_matrix_refl Equiv.mapMatrix_refl

/- warning: equiv.map_matrix_symm -> Equiv.mapMatrix_symm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} (f : Equiv.{succ u1, succ u2} α β), Eq.{max 1 (max (succ (max u3 u4 u2)) (succ (max u3 u4 u1))) (succ (max u3 u4 u1)) (succ (max u3 u4 u2))} (Equiv.{succ (max u3 u4 u2), succ (max u3 u4 u1)} (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u1} m n α)) (Equiv.symm.{succ (max u3 u4 u1), succ (max u3 u4 u2)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) (Equiv.mapMatrix.{u1, u2, u3, u4} m n α β f)) (Equiv.mapMatrix.{u2, u1, u3, u4} m n β α (Equiv.symm.{succ u1, succ u2} α β f))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} (f : Equiv.{succ u3, succ u4} α β), Eq.{max (max (max (succ u3) (succ u4)) (succ u2)) (succ u1)} (Equiv.{max (max (succ u4) (succ u1)) (succ u2), max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u4} m n β) (Matrix.{u2, u1, u3} m n α)) (Equiv.symm.{max (max (succ u3) (succ u1)) (succ u2), max (max (succ u4) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u4} m n β) (Equiv.mapMatrix.{u3, u4, u2, u1} m n α β f)) (Equiv.mapMatrix.{u4, u3, u2, u1} m n β α (Equiv.symm.{succ u3, succ u4} α β f))
Case conversion may be inaccurate. Consider using '#align equiv.map_matrix_symm Equiv.mapMatrix_symmₓ'. -/
@[simp]
theorem mapMatrix_symm (f : α ≃ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ _) :=
  rfl
#align equiv.map_matrix_symm Equiv.mapMatrix_symm

/- warning: equiv.map_matrix_trans -> Equiv.mapMatrix_trans is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u5}} (f : Equiv.{succ u1, succ u2} α β) (g : Equiv.{succ u2, succ u5} β γ), Eq.{max 1 (max (succ (max u3 u4 u1)) (succ (max u3 u4 u5))) (succ (max u3 u4 u5)) (succ (max u3 u4 u1))} (Equiv.{succ (max u3 u4 u1), succ (max u3 u4 u5)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u5} m n γ)) (Equiv.trans.{succ (max u3 u4 u1), succ (max u3 u4 u2), succ (max u3 u4 u5)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u5} m n γ) (Equiv.mapMatrix.{u1, u2, u3, u4} m n α β f) (Equiv.mapMatrix.{u2, u5, u3, u4} m n β γ g)) (Equiv.mapMatrix.{u1, u5, u3, u4} m n α γ (Equiv.trans.{succ u1, succ u2, succ u5} α β γ f g))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u4}} {β : Type.{u5}} {γ : Type.{u3}} (f : Equiv.{succ u4, succ u5} α β) (g : Equiv.{succ u5, succ u3} β γ), Eq.{max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3)} (Equiv.{max (max (succ u4) (succ u1)) (succ u2), max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u3} m n γ)) (Equiv.trans.{max (max (succ u4) (succ u1)) (succ u2), max (max (succ u5) (succ u1)) (succ u2), max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u5} m n β) (Matrix.{u2, u1, u3} m n γ) (Equiv.mapMatrix.{u4, u5, u2, u1} m n α β f) (Equiv.mapMatrix.{u5, u3, u2, u1} m n β γ g)) (Equiv.mapMatrix.{u4, u3, u2, u1} m n α γ (Equiv.trans.{succ u4, succ u5, succ u3} α β γ f g))
Case conversion may be inaccurate. Consider using '#align equiv.map_matrix_trans Equiv.mapMatrix_transₓ'. -/
@[simp]
theorem mapMatrix_trans (f : α ≃ β) (g : β ≃ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ _) :=
  rfl
#align equiv.map_matrix_trans Equiv.mapMatrix_trans

end Equiv

namespace AddMonoidHom

variable [AddZeroClass α] [AddZeroClass β] [AddZeroClass γ]

#print AddMonoidHom.mapMatrix /-
/-- The `add_monoid_hom` between spaces of matrices induced by an `add_monoid_hom` between their
coefficients. This is `matrix.map` as an `add_monoid_hom`. -/
@[simps]
def mapMatrix (f : α →+ β) : Matrix m n α →+ Matrix m n β
    where
  toFun M := M.map f
  map_zero' := Matrix.map_zero f f.map_zero
  map_add' := Matrix.map_add f f.map_add
#align add_monoid_hom.map_matrix AddMonoidHom.mapMatrix
-/

/- warning: add_monoid_hom.map_matrix_id -> AddMonoidHom.mapMatrix_id is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddZeroClass.{u1} α], Eq.{succ (max u2 u3 u1)} (AddMonoidHom.{max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.addZeroClass.{u1, u2, u3} m n α _inst_1) (Matrix.addZeroClass.{u1, u2, u3} m n α _inst_1)) (AddMonoidHom.mapMatrix.{u1, u1, u2, u3} m n α α _inst_1 _inst_1 (AddMonoidHom.id.{u1} α _inst_1)) (AddMonoidHom.id.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.addZeroClass.{u1, u2, u3} m n α _inst_1))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddZeroClass.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AddMonoidHom.{max (max u3 u1) u2, max (max u3 u1) u2} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.addZeroClass.{u3, u2, u1} m n α _inst_1) (Matrix.addZeroClass.{u3, u2, u1} m n α _inst_1)) (AddMonoidHom.mapMatrix.{u3, u3, u2, u1} m n α α _inst_1 _inst_1 (AddMonoidHom.id.{u3} α _inst_1)) (AddMonoidHom.id.{max (max u3 u1) u2} (Matrix.{u2, u1, u3} m n α) (Matrix.addZeroClass.{u3, u2, u1} m n α _inst_1))
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.map_matrix_id AddMonoidHom.mapMatrix_idₓ'. -/
@[simp]
theorem mapMatrix_id : (AddMonoidHom.id α).mapMatrix = AddMonoidHom.id (Matrix m n α) :=
  rfl
#align add_monoid_hom.map_matrix_id AddMonoidHom.mapMatrix_id

/- warning: add_monoid_hom.map_matrix_comp -> AddMonoidHom.mapMatrix_comp is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u5}} [_inst_1 : AddZeroClass.{u1} α] [_inst_2 : AddZeroClass.{u2} β] [_inst_3 : AddZeroClass.{u5} γ] (f : AddMonoidHom.{u2, u5} β γ _inst_2 _inst_3) (g : AddMonoidHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ (max u3 u4 u5)) (succ (max u3 u4 u1))} (AddMonoidHom.{max u3 u4 u1, max u3 u4 u5} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u5} m n γ) (Matrix.addZeroClass.{u1, u3, u4} m n α _inst_1) (Matrix.addZeroClass.{u5, u3, u4} m n γ _inst_3)) (AddMonoidHom.comp.{max u3 u4 u1, max u3 u4 u2, max u3 u4 u5} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u5} m n γ) (Matrix.addZeroClass.{u1, u3, u4} m n α _inst_1) (Matrix.addZeroClass.{u2, u3, u4} m n β _inst_2) (Matrix.addZeroClass.{u5, u3, u4} m n γ _inst_3) (AddMonoidHom.mapMatrix.{u2, u5, u3, u4} m n β γ _inst_2 _inst_3 f) (AddMonoidHom.mapMatrix.{u1, u2, u3, u4} m n α β _inst_1 _inst_2 g)) (AddMonoidHom.mapMatrix.{u1, u5, u3, u4} m n α γ _inst_1 _inst_3 (AddMonoidHom.comp.{u1, u2, u5} α β γ _inst_1 _inst_2 _inst_3 f g))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u4}} {β : Type.{u5}} {γ : Type.{u3}} [_inst_1 : AddZeroClass.{u4} α] [_inst_2 : AddZeroClass.{u5} β] [_inst_3 : AddZeroClass.{u3} γ] (f : AddMonoidHom.{u5, u3} β γ _inst_2 _inst_3) (g : AddMonoidHom.{u4, u5} α β _inst_1 _inst_2), Eq.{max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3)} (AddMonoidHom.{max (max u4 u1) u2, max (max u3 u1) u2} (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u3} m n γ) (Matrix.addZeroClass.{u4, u2, u1} m n α _inst_1) (Matrix.addZeroClass.{u3, u2, u1} m n γ _inst_3)) (AddMonoidHom.comp.{max (max u4 u1) u2, max (max u5 u1) u2, max (max u3 u1) u2} (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u5} m n β) (Matrix.{u2, u1, u3} m n γ) (Matrix.addZeroClass.{u4, u2, u1} m n α _inst_1) (Matrix.addZeroClass.{u5, u2, u1} m n β _inst_2) (Matrix.addZeroClass.{u3, u2, u1} m n γ _inst_3) (AddMonoidHom.mapMatrix.{u5, u3, u2, u1} m n β γ _inst_2 _inst_3 f) (AddMonoidHom.mapMatrix.{u4, u5, u2, u1} m n α β _inst_1 _inst_2 g)) (AddMonoidHom.mapMatrix.{u4, u3, u2, u1} m n α γ _inst_1 _inst_3 (AddMonoidHom.comp.{u4, u5, u3} α β γ _inst_1 _inst_2 _inst_3 f g))
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.map_matrix_comp AddMonoidHom.mapMatrix_compₓ'. -/
@[simp]
theorem mapMatrix_comp (f : β →+ γ) (g : α →+ β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →+ _) :=
  rfl
#align add_monoid_hom.map_matrix_comp AddMonoidHom.mapMatrix_comp

end AddMonoidHom

namespace AddEquiv

variable [Add α] [Add β] [Add γ]

#print AddEquiv.mapMatrix /-
/-- The `add_equiv` between spaces of matrices induced by an `add_equiv` between their
coefficients. This is `matrix.map` as an `add_equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃+ β) : Matrix m n α ≃+ Matrix m n β :=
  { f.toEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm
    map_add' := Matrix.map_add f f.map_add }
#align add_equiv.map_matrix AddEquiv.mapMatrix
-/

/- warning: add_equiv.map_matrix_refl -> AddEquiv.mapMatrix_refl is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Add.{u1} α], Eq.{succ (max u2 u3 u1)} (AddEquiv.{max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α _inst_1) (Matrix.hasAdd.{u1, u2, u3} m n α _inst_1)) (AddEquiv.mapMatrix.{u1, u1, u2, u3} m n α α _inst_1 _inst_1 (AddEquiv.refl.{u1} α _inst_1)) (AddEquiv.refl.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α _inst_1))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Add.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AddEquiv.{max (max u3 u1) u2, max (max u3 u1) u2} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α _inst_1) (Matrix.add.{u3, u2, u1} m n α _inst_1)) (AddEquiv.mapMatrix.{u3, u3, u2, u1} m n α α _inst_1 _inst_1 (AddEquiv.refl.{u3} α _inst_1)) (AddEquiv.refl.{max (max u3 u1) u2} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α _inst_1))
Case conversion may be inaccurate. Consider using '#align add_equiv.map_matrix_refl AddEquiv.mapMatrix_reflₓ'. -/
@[simp]
theorem mapMatrix_refl : (AddEquiv.refl α).mapMatrix = AddEquiv.refl (Matrix m n α) :=
  rfl
#align add_equiv.map_matrix_refl AddEquiv.mapMatrix_refl

/- warning: add_equiv.map_matrix_symm -> AddEquiv.mapMatrix_symm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Add.{u1} α] [_inst_2 : Add.{u2} β] (f : AddEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ (max u3 u4 u2)) (succ (max u3 u4 u1))} (AddEquiv.{max u3 u4 u2, max u3 u4 u1} (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u1} m n α) (Matrix.hasAdd.{u2, u3, u4} m n β _inst_2) (Matrix.hasAdd.{u1, u3, u4} m n α _inst_1)) (AddEquiv.symm.{max u3 u4 u1, max u3 u4 u2} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) (Matrix.hasAdd.{u1, u3, u4} m n α _inst_1) (Matrix.hasAdd.{u2, u3, u4} m n β _inst_2) (AddEquiv.mapMatrix.{u1, u2, u3, u4} m n α β _inst_1 _inst_2 f)) (AddEquiv.mapMatrix.{u2, u1, u3, u4} m n β α _inst_2 _inst_1 (AddEquiv.symm.{u1, u2} α β _inst_1 _inst_2 f))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Add.{u3} α] [_inst_2 : Add.{u4} β] (f : AddEquiv.{u3, u4} α β _inst_1 _inst_2), Eq.{max (max (max (succ u3) (succ u4)) (succ u2)) (succ u1)} (AddEquiv.{max (max u4 u1) u2, max (max u3 u1) u2} (Matrix.{u2, u1, u4} m n β) (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u4, u2, u1} m n β _inst_2) (Matrix.add.{u3, u2, u1} m n α _inst_1)) (AddEquiv.symm.{max (max u3 u1) u2, max (max u4 u1) u2} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u4} m n β) (Matrix.add.{u3, u2, u1} m n α _inst_1) (Matrix.add.{u4, u2, u1} m n β _inst_2) (AddEquiv.mapMatrix.{u3, u4, u2, u1} m n α β _inst_1 _inst_2 f)) (AddEquiv.mapMatrix.{u4, u3, u2, u1} m n β α _inst_2 _inst_1 (AddEquiv.symm.{u3, u4} α β _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align add_equiv.map_matrix_symm AddEquiv.mapMatrix_symmₓ'. -/
@[simp]
theorem mapMatrix_symm (f : α ≃+ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃+ _) :=
  rfl
#align add_equiv.map_matrix_symm AddEquiv.mapMatrix_symm

/- warning: add_equiv.map_matrix_trans -> AddEquiv.mapMatrix_trans is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u5}} [_inst_1 : Add.{u1} α] [_inst_2 : Add.{u2} β] [_inst_3 : Add.{u5} γ] (f : AddEquiv.{u1, u2} α β _inst_1 _inst_2) (g : AddEquiv.{u2, u5} β γ _inst_2 _inst_3), Eq.{max (succ (max u3 u4 u1)) (succ (max u3 u4 u5))} (AddEquiv.{max u3 u4 u1, max u3 u4 u5} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u5} m n γ) (Matrix.hasAdd.{u1, u3, u4} m n α _inst_1) (Matrix.hasAdd.{u5, u3, u4} m n γ _inst_3)) (AddEquiv.trans.{max u3 u4 u1, max u3 u4 u2, max u3 u4 u5} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u5} m n γ) (Matrix.hasAdd.{u1, u3, u4} m n α _inst_1) (Matrix.hasAdd.{u2, u3, u4} m n β _inst_2) (Matrix.hasAdd.{u5, u3, u4} m n γ _inst_3) (AddEquiv.mapMatrix.{u1, u2, u3, u4} m n α β _inst_1 _inst_2 f) (AddEquiv.mapMatrix.{u2, u5, u3, u4} m n β γ _inst_2 _inst_3 g)) (AddEquiv.mapMatrix.{u1, u5, u3, u4} m n α γ _inst_1 _inst_3 (AddEquiv.trans.{u1, u2, u5} α β γ _inst_1 _inst_2 _inst_3 f g))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u4}} {β : Type.{u5}} {γ : Type.{u3}} [_inst_1 : Add.{u4} α] [_inst_2 : Add.{u5} β] [_inst_3 : Add.{u3} γ] (f : AddEquiv.{u4, u5} α β _inst_1 _inst_2) (g : AddEquiv.{u5, u3} β γ _inst_2 _inst_3), Eq.{max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3)} (AddEquiv.{max (max u4 u1) u2, max (max u3 u1) u2} (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u3} m n γ) (Matrix.add.{u4, u2, u1} m n α _inst_1) (Matrix.add.{u3, u2, u1} m n γ _inst_3)) (AddEquiv.trans.{max (max u4 u1) u2, max (max u5 u1) u2, max (max u3 u1) u2} (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u5} m n β) (Matrix.{u2, u1, u3} m n γ) (Matrix.add.{u4, u2, u1} m n α _inst_1) (Matrix.add.{u5, u2, u1} m n β _inst_2) (Matrix.add.{u3, u2, u1} m n γ _inst_3) (AddEquiv.mapMatrix.{u4, u5, u2, u1} m n α β _inst_1 _inst_2 f) (AddEquiv.mapMatrix.{u5, u3, u2, u1} m n β γ _inst_2 _inst_3 g)) (AddEquiv.mapMatrix.{u4, u3, u2, u1} m n α γ _inst_1 _inst_3 (AddEquiv.trans.{u4, u5, u3} α β γ _inst_1 _inst_2 _inst_3 f g))
Case conversion may be inaccurate. Consider using '#align add_equiv.map_matrix_trans AddEquiv.mapMatrix_transₓ'. -/
@[simp]
theorem mapMatrix_trans (f : α ≃+ β) (g : β ≃+ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃+ _) :=
  rfl
#align add_equiv.map_matrix_trans AddEquiv.mapMatrix_trans

end AddEquiv

namespace LinearMap

variable [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

#print LinearMap.mapMatrix /-
/-- The `linear_map` between spaces of matrices induced by a `linear_map` between their
coefficients. This is `matrix.map` as a `linear_map`. -/
@[simps]
def mapMatrix (f : α →ₗ[R] β) : Matrix m n α →ₗ[R] Matrix m n β
    where
  toFun M := M.map f
  map_add' := Matrix.map_add f f.map_add
  map_smul' r := Matrix.map_smul f r (f.map_smul r)
#align linear_map.map_matrix LinearMap.mapMatrix
-/

/- warning: linear_map.map_matrix_id -> LinearMap.mapMatrix_id is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : Semiring.{u4} R] [_inst_2 : AddCommMonoid.{u1} α] [_inst_5 : Module.{u4, u1} R α _inst_1 _inst_2], Eq.{succ (max u2 u3 u1)} (LinearMap.{u4, u4, max u2 u3 u1, max u2 u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_2) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_2) (Matrix.module.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_5)) (LinearMap.mapMatrix.{u1, u1, u2, u3, u4} m n R α α _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (LinearMap.id.{u4, u1} R α _inst_1 _inst_2 _inst_5)) (LinearMap.id.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) _inst_1 (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_2) (Matrix.module.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_5))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u1}} {α : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u4} α] [_inst_5 : Module.{u1, u4} R α _inst_1 _inst_2], Eq.{max (max (succ u4) (succ u3)) (succ u2)} (LinearMap.{u1, u1, max (max u4 u2) u3, max (max u4 u2) u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (Matrix.{u3, u2, u4} m n α) (Matrix.{u3, u2, u4} m n α) (Matrix.addCommMonoid.{u4, u3, u2} m n α _inst_2) (Matrix.addCommMonoid.{u4, u3, u2} m n α _inst_2) (Matrix.module.{u4, u3, u2, u1} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u4, u3, u2, u1} m n R α _inst_1 _inst_2 _inst_5)) (LinearMap.mapMatrix.{u4, u4, u3, u2, u1} m n R α α _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (LinearMap.id.{u1, u4} R α _inst_1 _inst_2 _inst_5)) (LinearMap.id.{u1, max (max u4 u3) u2} R (Matrix.{u3, u2, u4} m n α) _inst_1 (Matrix.addCommMonoid.{u4, u3, u2} m n α _inst_2) (Matrix.module.{u4, u3, u2, u1} m n R α _inst_1 _inst_2 _inst_5))
Case conversion may be inaccurate. Consider using '#align linear_map.map_matrix_id LinearMap.mapMatrix_idₓ'. -/
@[simp]
theorem mapMatrix_id : LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α →ₗ[R] _) :=
  rfl
#align linear_map.map_matrix_id LinearMap.mapMatrix_id

/- warning: linear_map.map_matrix_comp -> LinearMap.mapMatrix_comp is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {R : Type.{u5}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u6}} [_inst_1 : Semiring.{u5} R] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : AddCommMonoid.{u2} β] [_inst_4 : AddCommMonoid.{u6} γ] [_inst_5 : Module.{u5, u1} R α _inst_1 _inst_2] [_inst_6 : Module.{u5, u2} R β _inst_1 _inst_3] [_inst_7 : Module.{u5, u6} R γ _inst_1 _inst_4] (f : LinearMap.{u5, u5, u2, u6} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) β γ _inst_3 _inst_4 _inst_6 _inst_7) (g : LinearMap.{u5, u5, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) α β _inst_2 _inst_3 _inst_5 _inst_6), Eq.{max (succ (max u3 u4 u1)) (succ (max u3 u4 u6))} (LinearMap.{u5, u5, max u3 u4 u1, max u3 u4 u6} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u6} m n γ) (Matrix.addCommMonoid.{u1, u3, u4} m n α _inst_2) (Matrix.addCommMonoid.{u6, u3, u4} m n γ _inst_4) (Matrix.module.{u1, u3, u4, u5} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u6, u3, u4, u5} m n R γ _inst_1 _inst_4 _inst_7)) (LinearMap.comp.{u5, u5, u5, max u3 u4 u1, max u3 u4 u2, max u3 u4 u6} R R R (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u6} m n γ) _inst_1 _inst_1 _inst_1 (Matrix.addCommMonoid.{u1, u3, u4} m n α _inst_2) (Matrix.addCommMonoid.{u2, u3, u4} m n β _inst_3) (Matrix.addCommMonoid.{u6, u3, u4} m n γ _inst_4) (Matrix.module.{u1, u3, u4, u5} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u2, u3, u4, u5} m n R β _inst_1 _inst_3 _inst_6) (Matrix.module.{u6, u3, u4, u5} m n R γ _inst_1 _inst_4 _inst_7) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomCompTriple.right_ids.{u5, u5} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1))) (LinearMap.mapMatrix.{u2, u6, u3, u4, u5} m n R β γ _inst_1 _inst_3 _inst_4 _inst_6 _inst_7 f) (LinearMap.mapMatrix.{u1, u2, u3, u4, u5} m n R α β _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 g)) (LinearMap.mapMatrix.{u1, u6, u3, u4, u5} m n R α γ _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (LinearMap.comp.{u5, u5, u5, u1, u2, u6} R R R α β γ _inst_1 _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomCompTriple.right_ids.{u5, u5} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1))) f g))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u4}} {α : Type.{u5}} {β : Type.{u6}} {γ : Type.{u3}} [_inst_1 : Semiring.{u4} R] [_inst_2 : AddCommMonoid.{u5} α] [_inst_3 : AddCommMonoid.{u6} β] [_inst_4 : AddCommMonoid.{u3} γ] [_inst_5 : Module.{u4, u5} R α _inst_1 _inst_2] [_inst_6 : Module.{u4, u6} R β _inst_1 _inst_3] [_inst_7 : Module.{u4, u3} R γ _inst_1 _inst_4] (f : LinearMap.{u4, u4, u6, u3} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) β γ _inst_3 _inst_4 _inst_6 _inst_7) (g : LinearMap.{u4, u4, u5, u6} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) α β _inst_2 _inst_3 _inst_5 _inst_6), Eq.{max (max (max (succ u5) (succ u2)) (succ u1)) (succ u3)} (LinearMap.{u4, u4, max (max u5 u1) u2, max (max u3 u1) u2} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (Matrix.{u2, u1, u5} m n α) (Matrix.{u2, u1, u3} m n γ) (Matrix.addCommMonoid.{u5, u2, u1} m n α _inst_2) (Matrix.addCommMonoid.{u3, u2, u1} m n γ _inst_4) (Matrix.module.{u5, u2, u1, u4} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u3, u2, u1, u4} m n R γ _inst_1 _inst_4 _inst_7)) (LinearMap.comp.{u4, u4, u4, max (max u5 u1) u2, max (max u6 u1) u2, max (max u3 u1) u2} R R R (Matrix.{u2, u1, u5} m n α) (Matrix.{u2, u1, u6} m n β) (Matrix.{u2, u1, u3} m n γ) _inst_1 _inst_1 _inst_1 (Matrix.addCommMonoid.{u5, u2, u1} m n α _inst_2) (Matrix.addCommMonoid.{u6, u2, u1} m n β _inst_3) (Matrix.addCommMonoid.{u3, u2, u1} m n γ _inst_4) (Matrix.module.{u5, u2, u1, u4} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u6, u2, u1, u4} m n R β _inst_1 _inst_3 _inst_6) (Matrix.module.{u3, u2, u1, u4} m n R γ _inst_1 _inst_4 _inst_7) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomCompTriple.ids.{u4, u4} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))) (LinearMap.mapMatrix.{u6, u3, u2, u1, u4} m n R β γ _inst_1 _inst_3 _inst_4 _inst_6 _inst_7 f) (LinearMap.mapMatrix.{u5, u6, u2, u1, u4} m n R α β _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 g)) (LinearMap.mapMatrix.{u5, u3, u2, u1, u4} m n R α γ _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (LinearMap.comp.{u4, u4, u4, u5, u6, u3} R R R α β γ _inst_1 _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomCompTriple.ids.{u4, u4} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))) f g))
Case conversion may be inaccurate. Consider using '#align linear_map.map_matrix_comp LinearMap.mapMatrix_compₓ'. -/
@[simp]
theorem mapMatrix_comp (f : β →ₗ[R] γ) (g : α →ₗ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →ₗ[R] _) :=
  rfl
#align linear_map.map_matrix_comp LinearMap.mapMatrix_comp

end LinearMap

namespace LinearEquiv

variable [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [AddCommMonoid γ]

variable [Module R α] [Module R β] [Module R γ]

#print LinearEquiv.mapMatrix /-
/-- The `linear_equiv` between spaces of matrices induced by an `linear_equiv` between their
coefficients. This is `matrix.map` as an `linear_equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ₗ[R] β) : Matrix m n α ≃ₗ[R] Matrix m n β :=
  { f.toEquiv.mapMatrix,
    f.toLinearMap.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }
#align linear_equiv.map_matrix LinearEquiv.mapMatrix
-/

/- warning: linear_equiv.map_matrix_refl -> LinearEquiv.mapMatrix_refl is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : Semiring.{u4} R] [_inst_2 : AddCommMonoid.{u1} α] [_inst_5 : Module.{u4, u1} R α _inst_1 _inst_2], Eq.{succ (max u2 u3 u1)} (LinearEquiv.{u4, u4, max u2 u3 u1, max u2 u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_2) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_2) (Matrix.module.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_5)) (LinearEquiv.mapMatrix.{u1, u1, u2, u3, u4} m n R α α _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (LinearEquiv.refl.{u4, u1} R α _inst_1 _inst_2 _inst_5)) (LinearEquiv.refl.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) _inst_1 (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_2) (Matrix.module.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_5))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u1}} {α : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u4} α] [_inst_5 : Module.{u1, u4} R α _inst_1 _inst_2], Eq.{max (max (succ u4) (succ u3)) (succ u2)} (LinearEquiv.{u1, u1, max (max u4 u2) u3, max (max u4 u2) u3} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (Matrix.{u3, u2, u4} m n α) (Matrix.{u3, u2, u4} m n α) (Matrix.addCommMonoid.{u4, u3, u2} m n α _inst_2) (Matrix.addCommMonoid.{u4, u3, u2} m n α _inst_2) (Matrix.module.{u4, u3, u2, u1} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u4, u3, u2, u1} m n R α _inst_1 _inst_2 _inst_5)) (LinearEquiv.mapMatrix.{u4, u4, u3, u2, u1} m n R α α _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (LinearEquiv.refl.{u1, u4} R α _inst_1 _inst_2 _inst_5)) (LinearEquiv.refl.{u1, max (max u4 u2) u3} R (Matrix.{u3, u2, u4} m n α) _inst_1 (Matrix.addCommMonoid.{u4, u3, u2} m n α _inst_2) (Matrix.module.{u4, u3, u2, u1} m n R α _inst_1 _inst_2 _inst_5))
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_matrix_refl LinearEquiv.mapMatrix_reflₓ'. -/
@[simp]
theorem mapMatrix_refl : (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Matrix m n α) :=
  rfl
#align linear_equiv.map_matrix_refl LinearEquiv.mapMatrix_refl

/- warning: linear_equiv.map_matrix_symm -> LinearEquiv.mapMatrix_symm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {R : Type.{u5}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semiring.{u5} R] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : AddCommMonoid.{u2} β] [_inst_5 : Module.{u5, u1} R α _inst_1 _inst_2] [_inst_6 : Module.{u5, u2} R β _inst_1 _inst_3] (f : LinearEquiv.{u5, u5, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) α β _inst_2 _inst_3 _inst_5 _inst_6), Eq.{max (succ (max u3 u4 u2)) (succ (max u3 u4 u1))} (LinearEquiv.{u5, u5, max u3 u4 u2, max u3 u4 u1} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u1} m n α) (Matrix.addCommMonoid.{u2, u3, u4} m n β _inst_3) (Matrix.addCommMonoid.{u1, u3, u4} m n α _inst_2) (Matrix.module.{u2, u3, u4, u5} m n R β _inst_1 _inst_3 _inst_6) (Matrix.module.{u1, u3, u4, u5} m n R α _inst_1 _inst_2 _inst_5)) (LinearEquiv.symm.{u5, u5, max u3 u4 u1, max u3 u4 u2} R R (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) _inst_1 _inst_1 (Matrix.addCommMonoid.{u1, u3, u4} m n α _inst_2) (Matrix.addCommMonoid.{u2, u3, u4} m n β _inst_3) (Matrix.module.{u1, u3, u4, u5} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u2, u3, u4, u5} m n R β _inst_1 _inst_3 _inst_6) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (LinearEquiv.mapMatrix.{u1, u2, u3, u4, u5} m n R α β _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f)) (LinearEquiv.mapMatrix.{u2, u1, u3, u4, u5} m n R β α _inst_1 _inst_3 _inst_2 _inst_6 _inst_5 (LinearEquiv.symm.{u5, u5, u1, u2} R R α β _inst_1 _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) f))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} {β : Type.{u5}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} α] [_inst_3 : AddCommMonoid.{u5} β] [_inst_5 : Module.{u3, u4} R α _inst_1 _inst_2] [_inst_6 : Module.{u3, u5} R β _inst_1 _inst_3] (f : LinearEquiv.{u3, u3, u4, u5} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) α β _inst_2 _inst_3 _inst_5 _inst_6), Eq.{max (max (max (succ u4) (succ u5)) (succ u2)) (succ u1)} (LinearEquiv.{u3, u3, max (max u5 u1) u2, max (max u4 u1) u2} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (Matrix.{u2, u1, u5} m n β) (Matrix.{u2, u1, u4} m n α) (Matrix.addCommMonoid.{u5, u2, u1} m n β _inst_3) (Matrix.addCommMonoid.{u4, u2, u1} m n α _inst_2) (Matrix.module.{u5, u2, u1, u3} m n R β _inst_1 _inst_3 _inst_6) (Matrix.module.{u4, u2, u1, u3} m n R α _inst_1 _inst_2 _inst_5)) (LinearEquiv.symm.{u3, u3, max (max u4 u1) u2, max (max u5 u1) u2} R R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u5} m n β) _inst_1 _inst_1 (Matrix.addCommMonoid.{u4, u2, u1} m n α _inst_2) (Matrix.addCommMonoid.{u5, u2, u1} m n β _inst_3) (Matrix.module.{u4, u2, u1, u3} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u5, u2, u1, u3} m n R β _inst_1 _inst_3 _inst_6) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (LinearEquiv.mapMatrix.{u4, u5, u2, u1, u3} m n R α β _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f)) (LinearEquiv.mapMatrix.{u5, u4, u2, u1, u3} m n R β α _inst_1 _inst_3 _inst_2 _inst_6 _inst_5 (LinearEquiv.symm.{u3, u3, u4, u5} R R α β _inst_1 _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) f))
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_matrix_symm LinearEquiv.mapMatrix_symmₓ'. -/
@[simp]
theorem mapMatrix_symm (f : α ≃ₗ[R] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ₗ[R] _) :=
  rfl
#align linear_equiv.map_matrix_symm LinearEquiv.mapMatrix_symm

/- warning: linear_equiv.map_matrix_trans -> LinearEquiv.mapMatrix_trans is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {R : Type.{u5}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u6}} [_inst_1 : Semiring.{u5} R] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : AddCommMonoid.{u2} β] [_inst_4 : AddCommMonoid.{u6} γ] [_inst_5 : Module.{u5, u1} R α _inst_1 _inst_2] [_inst_6 : Module.{u5, u2} R β _inst_1 _inst_3] [_inst_7 : Module.{u5, u6} R γ _inst_1 _inst_4] (f : LinearEquiv.{u5, u5, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) α β _inst_2 _inst_3 _inst_5 _inst_6) (g : LinearEquiv.{u5, u5, u2, u6} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) β γ _inst_3 _inst_4 _inst_6 _inst_7), Eq.{max (succ (max u3 u4 u1)) (succ (max u3 u4 u6))} (LinearEquiv.{u5, u5, max u3 u4 u1, max u3 u4 u6} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u6} m n γ) (Matrix.addCommMonoid.{u1, u3, u4} m n α _inst_2) (Matrix.addCommMonoid.{u6, u3, u4} m n γ _inst_4) (Matrix.module.{u1, u3, u4, u5} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u6, u3, u4, u5} m n R γ _inst_1 _inst_4 _inst_7)) (LinearEquiv.trans.{u5, u5, u5, max u3 u4 u1, max u3 u4 u2, max u3 u4 u6} R R R (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u2} m n β) (Matrix.{u3, u4, u6} m n γ) _inst_1 _inst_1 _inst_1 (Matrix.addCommMonoid.{u1, u3, u4} m n α _inst_2) (Matrix.addCommMonoid.{u2, u3, u4} m n β _inst_3) (Matrix.addCommMonoid.{u6, u3, u4} m n γ _inst_4) (Matrix.module.{u1, u3, u4, u5} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u2, u3, u4, u5} m n R β _inst_1 _inst_3 _inst_6) (Matrix.module.{u6, u3, u4, u5} m n R γ _inst_1 _inst_4 _inst_7) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomCompTriple.right_ids.{u5, u5} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1))) (RingHomCompTriple.right_ids.{u5, u5} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1))) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (LinearEquiv.mapMatrix.{u1, u2, u3, u4, u5} m n R α β _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) (LinearEquiv.mapMatrix.{u2, u6, u3, u4, u5} m n R β γ _inst_1 _inst_3 _inst_4 _inst_6 _inst_7 g)) (LinearEquiv.mapMatrix.{u1, u6, u3, u4, u5} m n R α γ _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (LinearEquiv.trans.{u5, u5, u5, u1, u2, u6} R R R α β γ _inst_1 _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1)) (RingHomCompTriple.right_ids.{u5, u5} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1))) (RingHomCompTriple.right_ids.{u5, u5} R R _inst_1 _inst_1 (RingHom.id.{u5} R (Semiring.toNonAssocSemiring.{u5} R _inst_1))) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) (RingHomInvPair.ids.{u5} R _inst_1) f g))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u4}} {α : Type.{u5}} {β : Type.{u6}} {γ : Type.{u3}} [_inst_1 : Semiring.{u4} R] [_inst_2 : AddCommMonoid.{u5} α] [_inst_3 : AddCommMonoid.{u6} β] [_inst_4 : AddCommMonoid.{u3} γ] [_inst_5 : Module.{u4, u5} R α _inst_1 _inst_2] [_inst_6 : Module.{u4, u6} R β _inst_1 _inst_3] [_inst_7 : Module.{u4, u3} R γ _inst_1 _inst_4] (f : LinearEquiv.{u4, u4, u5, u6} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) α β _inst_2 _inst_3 _inst_5 _inst_6) (g : LinearEquiv.{u4, u4, u6, u3} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) β γ _inst_3 _inst_4 _inst_6 _inst_7), Eq.{max (max (max (succ u5) (succ u2)) (succ u1)) (succ u3)} (LinearEquiv.{u4, u4, max (max u5 u1) u2, max (max u3 u1) u2} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (Matrix.{u2, u1, u5} m n α) (Matrix.{u2, u1, u3} m n γ) (Matrix.addCommMonoid.{u5, u2, u1} m n α _inst_2) (Matrix.addCommMonoid.{u3, u2, u1} m n γ _inst_4) (Matrix.module.{u5, u2, u1, u4} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u3, u2, u1, u4} m n R γ _inst_1 _inst_4 _inst_7)) (LinearEquiv.trans.{u4, u4, u4, max (max u5 u1) u2, max (max u6 u1) u2, max (max u3 u1) u2} R R R (Matrix.{u2, u1, u5} m n α) (Matrix.{u2, u1, u6} m n β) (Matrix.{u2, u1, u3} m n γ) _inst_1 _inst_1 _inst_1 (Matrix.addCommMonoid.{u5, u2, u1} m n α _inst_2) (Matrix.addCommMonoid.{u6, u2, u1} m n β _inst_3) (Matrix.addCommMonoid.{u3, u2, u1} m n γ _inst_4) (Matrix.module.{u5, u2, u1, u4} m n R α _inst_1 _inst_2 _inst_5) (Matrix.module.{u6, u2, u1, u4} m n R β _inst_1 _inst_3 _inst_6) (Matrix.module.{u3, u2, u1, u4} m n R γ _inst_1 _inst_4 _inst_7) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomCompTriple.ids.{u4, u4} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))) (RingHomCompTriple.ids.{u4, u4} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (LinearEquiv.mapMatrix.{u5, u6, u2, u1, u4} m n R α β _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) (LinearEquiv.mapMatrix.{u6, u3, u2, u1, u4} m n R β γ _inst_1 _inst_3 _inst_4 _inst_6 _inst_7 g)) (LinearEquiv.mapMatrix.{u5, u3, u2, u1, u4} m n R α γ _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (LinearEquiv.trans.{u4, u4, u4, u5, u6, u3} R R R α β γ _inst_1 _inst_1 _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomCompTriple.ids.{u4, u4} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))) (RingHomCompTriple.ids.{u4, u4} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) f g))
Case conversion may be inaccurate. Consider using '#align linear_equiv.map_matrix_trans LinearEquiv.mapMatrix_transₓ'. -/
@[simp]
theorem mapMatrix_trans (f : α ≃ₗ[R] β) (g : β ≃ₗ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ₗ[R] _) :=
  rfl
#align linear_equiv.map_matrix_trans LinearEquiv.mapMatrix_trans

end LinearEquiv

namespace RingHom

variable [Fintype m] [DecidableEq m]

variable [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]

#print RingHom.mapMatrix /-
/-- The `ring_hom` between spaces of square matrices induced by a `ring_hom` between their
coefficients. This is `matrix.map` as a `ring_hom`. -/
@[simps]
def mapMatrix (f : α →+* β) : Matrix m m α →+* Matrix m m β :=
  { f.toAddMonoidHom.mapMatrix with
    toFun := fun M => M.map f
    map_one' := by simp
    map_mul' := fun L M => Matrix.map_mul }
#align ring_hom.map_matrix RingHom.mapMatrix
-/

/- warning: ring_hom.map_matrix_id -> RingHom.mapMatrix_id is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : NonAssocSemiring.{u1} α], Eq.{succ (max u2 u1)} (RingHom.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.{u2, u2, u1} m m α) (Matrix.nonAssocSemiring.{u1, u2} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.nonAssocSemiring.{u1, u2} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b))) (RingHom.mapMatrix.{u1, u1, u2} m α α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_3 (RingHom.id.{u1} α _inst_3)) (RingHom.id.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.nonAssocSemiring.{u1, u2} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : NonAssocSemiring.{u2} α], Eq.{max (succ u2) (succ u1)} (RingHom.{max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.{u1, u1, u2} m m α) (Matrix.nonAssocSemiring.{u2, u1} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.nonAssocSemiring.{u2, u1} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b))) (RingHom.mapMatrix.{u2, u2, u1} m α α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_3 (RingHom.id.{u2} α _inst_3)) (RingHom.id.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.nonAssocSemiring.{u2, u1} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_matrix_id RingHom.mapMatrix_idₓ'. -/
@[simp]
theorem mapMatrix_id : (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α) :=
  rfl
#align ring_hom.map_matrix_id RingHom.mapMatrix_id

/- warning: ring_hom.map_matrix_comp -> RingHom.mapMatrix_comp is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : NonAssocSemiring.{u1} α] [_inst_4 : NonAssocSemiring.{u2} β] [_inst_5 : NonAssocSemiring.{u4} γ] (f : RingHom.{u2, u4} β γ _inst_4 _inst_5) (g : RingHom.{u1, u2} α β _inst_3 _inst_4), Eq.{max (succ (max u3 u1)) (succ (max u3 u4))} (RingHom.{max u3 u1, max u3 u4} (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u4} m m γ) (Matrix.nonAssocSemiring.{u1, u3} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.nonAssocSemiring.{u4, u3} m γ _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b))) (RingHom.comp.{max u3 u1, max u3 u2, max u3 u4} (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) (Matrix.{u3, u3, u4} m m γ) (Matrix.nonAssocSemiring.{u1, u3} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.nonAssocSemiring.{u2, u3} m β _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.nonAssocSemiring.{u4, u3} m γ _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (RingHom.mapMatrix.{u2, u4, u3} m β γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_4 _inst_5 f) (RingHom.mapMatrix.{u1, u2, u3} m α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 g)) (RingHom.mapMatrix.{u1, u4, u3} m α γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 (RingHom.comp.{u1, u2, u4} α β γ _inst_3 _inst_4 _inst_5 f g))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : NonAssocSemiring.{u3} α] [_inst_4 : NonAssocSemiring.{u4} β] [_inst_5 : NonAssocSemiring.{u2} γ] (f : RingHom.{u4, u2} β γ _inst_4 _inst_5) (g : RingHom.{u3, u4} α β _inst_3 _inst_4), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (RingHom.{max u3 u1, max u2 u1} (Matrix.{u1, u1, u3} m m α) (Matrix.{u1, u1, u2} m m γ) (Matrix.nonAssocSemiring.{u3, u1} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.nonAssocSemiring.{u2, u1} m γ _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b))) (RingHom.comp.{max u3 u1, max u4 u1, max u2 u1} (Matrix.{u1, u1, u3} m m α) (Matrix.{u1, u1, u4} m m β) (Matrix.{u1, u1, u2} m m γ) (Matrix.nonAssocSemiring.{u3, u1} m α _inst_3 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.nonAssocSemiring.{u4, u1} m β _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.nonAssocSemiring.{u2, u1} m γ _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (RingHom.mapMatrix.{u4, u2, u1} m β γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_4 _inst_5 f) (RingHom.mapMatrix.{u3, u4, u1} m α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 g)) (RingHom.mapMatrix.{u3, u2, u1} m α γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 (RingHom.comp.{u3, u4, u2} α β γ _inst_3 _inst_4 _inst_5 f g))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_matrix_comp RingHom.mapMatrix_compₓ'. -/
@[simp]
theorem mapMatrix_comp (f : β →+* γ) (g : α →+* β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →+* _) :=
  rfl
#align ring_hom.map_matrix_comp RingHom.mapMatrix_comp

end RingHom

namespace RingEquiv

variable [Fintype m] [DecidableEq m]

variable [NonAssocSemiring α] [NonAssocSemiring β] [NonAssocSemiring γ]

/- warning: ring_equiv.map_matrix -> RingEquiv.mapMatrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : NonAssocSemiring.{u1} α] [_inst_4 : NonAssocSemiring.{u2} β], (RingEquiv.{u1, u2} α β (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))) -> (RingEquiv.{max u3 u1, max u3 u2} (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) (Matrix.hasMul.{u1, u3} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.hasAdd.{u1, u3, u3} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)))) (Matrix.hasMul.{u2, u3} m β _inst_1 (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Matrix.hasAdd.{u2, u3, u3} m m β (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))))
but is expected to have type
  forall {m : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : NonAssocSemiring.{u1} α] [_inst_4 : NonAssocSemiring.{u2} β], (RingEquiv.{u1, u2} α β (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))) -> (RingEquiv.{max u1 u3, max u2 u3} (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) (Matrix.instMulMatrix.{u1, u3} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.instMulMatrix.{u2, u3} m β _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Matrix.add.{u1, u3, u3} m m α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)))) (Matrix.add.{u2, u3, u3} m m β (Distrib.toAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))))
Case conversion may be inaccurate. Consider using '#align ring_equiv.map_matrix RingEquiv.mapMatrixₓ'. -/
/-- The `ring_equiv` between spaces of square matrices induced by a `ring_equiv` between their
coefficients. This is `matrix.map` as a `ring_equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃+* β) : Matrix m m α ≃+* Matrix m m β :=
  { f.toRingHom.mapMatrix,
    f.toAddEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }
#align ring_equiv.map_matrix RingEquiv.mapMatrix

/- warning: ring_equiv.map_matrix_refl -> RingEquiv.mapMatrix_refl is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : NonAssocSemiring.{u1} α], Eq.{succ (max u2 u1)} (RingEquiv.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.{u2, u2, u1} m m α) (Matrix.hasMul.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.hasAdd.{u1, u2, u2} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)))) (Matrix.hasMul.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.hasAdd.{u1, u2, u2} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))))) (RingEquiv.mapMatrix.{u1, u1, u2} m α α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_3 (RingEquiv.refl.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))))) (RingEquiv.refl.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasMul.{u1, u2} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.hasAdd.{u1, u2, u2} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)))))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : NonAssocSemiring.{u2} α], Eq.{max (succ u2) (succ u1)} (RingEquiv.{max u2 u1, max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.{u1, u1, u2} m m α) (Matrix.instMulMatrix.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (Matrix.instMulMatrix.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (Matrix.add.{u2, u1, u1} m m α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)))) (Matrix.add.{u2, u1, u1} m m α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))))) (RingEquiv.mapMatrix.{u2, u2, u1} m α α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_3 (RingEquiv.refl.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))))) (RingEquiv.refl.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.instMulMatrix.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (Matrix.add.{u2, u1, u1} m m α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)))))
Case conversion may be inaccurate. Consider using '#align ring_equiv.map_matrix_refl RingEquiv.mapMatrix_reflₓ'. -/
@[simp]
theorem mapMatrix_refl : (RingEquiv.refl α).mapMatrix = RingEquiv.refl (Matrix m m α) :=
  rfl
#align ring_equiv.map_matrix_refl RingEquiv.mapMatrix_refl

/- warning: ring_equiv.map_matrix_symm -> RingEquiv.mapMatrix_symm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : NonAssocSemiring.{u1} α] [_inst_4 : NonAssocSemiring.{u2} β] (f : RingEquiv.{u1, u2} α β (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))), Eq.{max (succ (max u3 u2)) (succ (max u3 u1))} (RingEquiv.{max u3 u2, max u3 u1} (Matrix.{u3, u3, u2} m m β) (Matrix.{u3, u3, u1} m m α) (Matrix.hasMul.{u2, u3} m β _inst_1 (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Matrix.hasAdd.{u2, u3, u3} m m β (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))) (Matrix.hasMul.{u1, u3} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.hasAdd.{u1, u3, u3} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))))) (RingEquiv.symm.{max u3 u1, max u3 u2} (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) (Matrix.hasMul.{u1, u3} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.hasAdd.{u1, u3, u3} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)))) (Matrix.hasMul.{u2, u3} m β _inst_1 (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Matrix.hasAdd.{u2, u3, u3} m m β (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))) (RingEquiv.mapMatrix.{u1, u2, u3} m α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 f)) (RingEquiv.mapMatrix.{u2, u1, u3} m β α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_4 _inst_3 (RingEquiv.symm.{u1, u2} α β (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) f))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : NonAssocSemiring.{u2} α] [_inst_4 : NonAssocSemiring.{u3} β] (f : RingEquiv.{u2, u3} α β (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toMul.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4)) (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (Distrib.toAdd.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4)))), Eq.{max (max (succ u2) (succ u3)) (succ u1)} (RingEquiv.{max u3 u1, max u2 u1} (Matrix.{u1, u1, u3} m m β) (Matrix.{u1, u1, u2} m m α) (Matrix.instMulMatrix.{u3, u1} m β _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4))) (Matrix.instMulMatrix.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (Matrix.add.{u3, u1, u1} m m β (Distrib.toAdd.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4)))) (Matrix.add.{u2, u1, u1} m m α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))))) (RingEquiv.symm.{max u2 u1, max u3 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.{u1, u1, u3} m m β) (Matrix.instMulMatrix.{u2, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (Matrix.instMulMatrix.{u3, u1} m β _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4))) (Matrix.add.{u2, u1, u1} m m α (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)))) (Matrix.add.{u3, u1, u1} m m β (Distrib.toAdd.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4)))) (RingEquiv.mapMatrix.{u2, u3, u1} m α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 f)) (RingEquiv.mapMatrix.{u3, u2, u1} m β α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_4 _inst_3 (RingEquiv.symm.{u2, u3} α β (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toMul.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4)) (Distrib.toAdd.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (Distrib.toAdd.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β _inst_4))) f))
Case conversion may be inaccurate. Consider using '#align ring_equiv.map_matrix_symm RingEquiv.mapMatrix_symmₓ'. -/
@[simp]
theorem mapMatrix_symm (f : α ≃+* β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃+* _) :=
  rfl
#align ring_equiv.map_matrix_symm RingEquiv.mapMatrix_symm

/- warning: ring_equiv.map_matrix_trans -> RingEquiv.mapMatrix_trans is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : NonAssocSemiring.{u1} α] [_inst_4 : NonAssocSemiring.{u2} β] [_inst_5 : NonAssocSemiring.{u4} γ] (f : RingEquiv.{u1, u2} α β (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))) (g : RingEquiv.{u2, u4} β γ (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Distrib.toHasMul.{u4} γ (NonUnitalNonAssocSemiring.toDistrib.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5))) (Distrib.toHasAdd.{u4} γ (NonUnitalNonAssocSemiring.toDistrib.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5)))), Eq.{max (succ (max u3 u1)) (succ (max u3 u4))} (RingEquiv.{max u3 u1, max u3 u4} (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u4} m m γ) (Matrix.hasMul.{u1, u3} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.hasAdd.{u1, u3, u3} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)))) (Matrix.hasMul.{u4, u3} m γ _inst_1 (Distrib.toHasMul.{u4} γ (NonUnitalNonAssocSemiring.toDistrib.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5))) (Matrix.hasAdd.{u4, u3, u3} m m γ (Distrib.toHasAdd.{u4} γ (NonUnitalNonAssocSemiring.toDistrib.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5))))) (RingEquiv.trans.{max u3 u1, max u3 u2, max u3 u4} (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) (Matrix.{u3, u3, u4} m m γ) (Matrix.hasMul.{u1, u3} m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Matrix.hasAdd.{u1, u3, u3} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)))) (Matrix.hasMul.{u2, u3} m β _inst_1 (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Matrix.hasAdd.{u2, u3, u3} m m β (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4)))) (Matrix.hasMul.{u4, u3} m γ _inst_1 (Distrib.toHasMul.{u4} γ (NonUnitalNonAssocSemiring.toDistrib.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5))) (Matrix.hasAdd.{u4, u3, u3} m m γ (Distrib.toHasAdd.{u4} γ (NonUnitalNonAssocSemiring.toDistrib.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5)))) (RingEquiv.mapMatrix.{u1, u2, u3} m α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 f) (RingEquiv.mapMatrix.{u2, u4, u3} m β γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_4 _inst_5 g)) (RingEquiv.mapMatrix.{u1, u4, u3} m α γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 (RingEquiv.trans.{u1, u2, u4} α β γ (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_4))) (Distrib.toHasMul.{u4} γ (NonUnitalNonAssocSemiring.toDistrib.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5))) (Distrib.toHasAdd.{u4} γ (NonUnitalNonAssocSemiring.toDistrib.{u4} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} γ _inst_5))) f g))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : NonAssocSemiring.{u3} α] [_inst_4 : NonAssocSemiring.{u4} β] [_inst_5 : NonAssocSemiring.{u2} γ] (f : RingEquiv.{u3, u4} α β (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (NonUnitalNonAssocSemiring.toMul.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4)) (Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3))) (Distrib.toAdd.{u4} β (NonUnitalNonAssocSemiring.toDistrib.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4)))) (g : RingEquiv.{u4, u2} β γ (NonUnitalNonAssocSemiring.toMul.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5)) (Distrib.toAdd.{u4} β (NonUnitalNonAssocSemiring.toDistrib.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4))) (Distrib.toAdd.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5)))), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (RingEquiv.{max u3 u1, max u2 u1} (Matrix.{u1, u1, u3} m m α) (Matrix.{u1, u1, u2} m m γ) (Matrix.instMulMatrix.{u3, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3))) (Matrix.instMulMatrix.{u2, u1} m γ _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5))) (Matrix.add.{u3, u1, u1} m m α (Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)))) (Matrix.add.{u2, u1, u1} m m γ (Distrib.toAdd.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5))))) (RingEquiv.trans.{max u3 u1, max u4 u1, max u2 u1} (Matrix.{u1, u1, u3} m m α) (Matrix.{u1, u1, u4} m m β) (Matrix.{u1, u1, u2} m m γ) (Matrix.instMulMatrix.{u3, u1} m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3))) (Matrix.instMulMatrix.{u4, u1} m β _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4))) (Matrix.add.{u3, u1, u1} m m α (Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)))) (Matrix.add.{u4, u1, u1} m m β (Distrib.toAdd.{u4} β (NonUnitalNonAssocSemiring.toDistrib.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4)))) (Matrix.instMulMatrix.{u2, u1} m γ _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5))) (Matrix.add.{u2, u1, u1} m m γ (Distrib.toAdd.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5)))) (RingEquiv.mapMatrix.{u3, u4, u1} m α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 f) (RingEquiv.mapMatrix.{u4, u2, u1} m β γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_4 _inst_5 g)) (RingEquiv.mapMatrix.{u3, u2, u1} m α γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 (RingEquiv.trans.{u3, u4, u2} α β γ (NonUnitalNonAssocSemiring.toMul.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3)) (NonUnitalNonAssocSemiring.toMul.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4)) (Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_3))) (Distrib.toAdd.{u4} β (NonUnitalNonAssocSemiring.toDistrib.{u4} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} β _inst_4))) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5)) (Distrib.toAdd.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_5))) f g))
Case conversion may be inaccurate. Consider using '#align ring_equiv.map_matrix_trans RingEquiv.mapMatrix_transₓ'. -/
@[simp]
theorem mapMatrix_trans (f : α ≃+* β) (g : β ≃+* γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃+* _) :=
  rfl
#align ring_equiv.map_matrix_trans RingEquiv.mapMatrix_trans

end RingEquiv

namespace AlgHom

variable [Fintype m] [DecidableEq m]

variable [CommSemiring R] [Semiring α] [Semiring β] [Semiring γ]

variable [Algebra R α] [Algebra R β] [Algebra R γ]

/- warning: alg_hom.map_matrix -> AlgHom.mapMatrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : CommSemiring.{u4} R] [_inst_4 : Semiring.{u1} α] [_inst_5 : Semiring.{u2} β] [_inst_7 : Algebra.{u4, u1} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u4, u2} R β _inst_3 _inst_5], (AlgHom.{u4, u1, u2} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8) -> (AlgHom.{u4, max u3 u1, max u3 u2} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u3} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u2, u3, u4} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8))
but is expected to have type
  forall {m : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : CommSemiring.{u4} R] [_inst_4 : Semiring.{u1} α] [_inst_5 : Semiring.{u2} β] [_inst_7 : Algebra.{u4, u1} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u4, u2} R β _inst_3 _inst_5], (AlgHom.{u4, u1, u2} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8) -> (AlgHom.{u4, max u1 u3, max u2 u3} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u3} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u2, u3, u4} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8))
Case conversion may be inaccurate. Consider using '#align alg_hom.map_matrix AlgHom.mapMatrixₓ'. -/
/-- The `alg_hom` between spaces of square matrices induced by a `alg_hom` between their
coefficients. This is `matrix.map` as a `alg_hom`. -/
@[simps]
def mapMatrix (f : α →ₐ[R] β) : Matrix m m α →ₐ[R] Matrix m m β :=
  { f.toRingHom.mapMatrix with
    toFun := fun M => M.map f
    commutes' := fun r => Matrix.map_algebraMap r f f.map_zero (f.commutes r) }
#align alg_hom.map_matrix AlgHom.mapMatrix

/- warning: alg_hom.map_matrix_id -> AlgHom.mapMatrix_id is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u1} α] [_inst_7 : Algebra.{u3, u1} R α _inst_3 _inst_4], Eq.{succ (max u2 u1)} (AlgHom.{u3, max u2 u1, max u2 u1} R (Matrix.{u2, u2, u1} m m α) (Matrix.{u2, u2, u1} m m α) _inst_3 (Matrix.semiring.{u1, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u1, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u2, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u1, u2, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7)) (AlgHom.mapMatrix.{u1, u1, u2, u3} m R α α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_4 _inst_7 _inst_7 (AlgHom.id.{u3, u1} R α _inst_3 _inst_4 _inst_7)) (AlgHom.id.{u3, max u2 u1} R (Matrix.{u2, u2, u1} m m α) _inst_3 (Matrix.semiring.{u1, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u2, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7))
but is expected to have type
  forall {m : Type.{u2}} {R : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : Semiring.{u3} α] [_inst_7 : Algebra.{u1, u3} R α _inst_3 _inst_4], Eq.{max (succ u3) (succ u2)} (AlgHom.{u1, max u3 u2, max u3 u2} R (Matrix.{u2, u2, u3} m m α) (Matrix.{u2, u2, u3} m m α) _inst_3 (Matrix.semiring.{u3, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u3, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7)) (AlgHom.mapMatrix.{u3, u3, u2, u1} m R α α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_4 _inst_7 _inst_7 (AlgHom.id.{u1, u3} R α _inst_3 _inst_4 _inst_7)) (AlgHom.id.{u1, max u3 u2} R (Matrix.{u2, u2, u3} m m α) _inst_3 (Matrix.semiring.{u3, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7))
Case conversion may be inaccurate. Consider using '#align alg_hom.map_matrix_id AlgHom.mapMatrix_idₓ'. -/
@[simp]
theorem mapMatrix_id : (AlgHom.id R α).mapMatrix = AlgHom.id R (Matrix m m α) :=
  rfl
#align alg_hom.map_matrix_id AlgHom.mapMatrix_id

/- warning: alg_hom.map_matrix_comp -> AlgHom.mapMatrix_comp is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u5}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : CommSemiring.{u4} R] [_inst_4 : Semiring.{u1} α] [_inst_5 : Semiring.{u2} β] [_inst_6 : Semiring.{u5} γ] [_inst_7 : Algebra.{u4, u1} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u4, u2} R β _inst_3 _inst_5] [_inst_9 : Algebra.{u4, u5} R γ _inst_3 _inst_6] (f : AlgHom.{u4, u2, u5} R β γ _inst_3 _inst_5 _inst_6 _inst_8 _inst_9) (g : AlgHom.{u4, u1, u2} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8), Eq.{max (succ (max u3 u1)) (succ (max u3 u5))} (AlgHom.{u4, max u3 u1, max u3 u5} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u5} m m γ) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u5, u3} m γ _inst_6 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u5, u3, u4} m R γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_6 _inst_9)) (AlgHom.comp.{u4, max u3 u1, max u3 u2, max u3 u5} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) (Matrix.{u3, u3, u5} m m γ) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u3} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u5, u3} m γ _inst_6 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u2, u3, u4} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8) (Matrix.algebra.{u5, u3, u4} m R γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_6 _inst_9) (AlgHom.mapMatrix.{u2, u5, u3, u4} m R β γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_6 _inst_8 _inst_9 f) (AlgHom.mapMatrix.{u1, u2, u3, u4} m R α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_5 _inst_7 _inst_8 g)) (AlgHom.mapMatrix.{u1, u5, u3, u4} m R α γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_6 _inst_7 _inst_9 (AlgHom.comp.{u4, u1, u2, u5} R α β γ _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 f g))
but is expected to have type
  forall {m : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} {β : Type.{u5}} {γ : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u4} α] [_inst_5 : Semiring.{u5} β] [_inst_6 : Semiring.{u2} γ] [_inst_7 : Algebra.{u3, u4} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u3, u5} R β _inst_3 _inst_5] [_inst_9 : Algebra.{u3, u2} R γ _inst_3 _inst_6] (f : AlgHom.{u3, u5, u2} R β γ _inst_3 _inst_5 _inst_6 _inst_8 _inst_9) (g : AlgHom.{u3, u4, u5} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8), Eq.{max (max (succ u4) (succ u1)) (succ u2)} (AlgHom.{u3, max u4 u1, max u2 u1} R (Matrix.{u1, u1, u4} m m α) (Matrix.{u1, u1, u2} m m γ) _inst_3 (Matrix.semiring.{u4, u1} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u1} m γ _inst_6 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u4, u1, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u2, u1, u3} m R γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_6 _inst_9)) (AlgHom.comp.{u3, max u4 u1, max u5 u1, max u2 u1} R (Matrix.{u1, u1, u4} m m α) (Matrix.{u1, u1, u5} m m β) (Matrix.{u1, u1, u2} m m γ) _inst_3 (Matrix.semiring.{u4, u1} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u5, u1} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u1} m γ _inst_6 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u4, u1, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u5, u1, u3} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8) (Matrix.instAlgebraMatrixSemiring.{u2, u1, u3} m R γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_6 _inst_9) (AlgHom.mapMatrix.{u5, u2, u1, u3} m R β γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_6 _inst_8 _inst_9 f) (AlgHom.mapMatrix.{u4, u5, u1, u3} m R α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_5 _inst_7 _inst_8 g)) (AlgHom.mapMatrix.{u4, u2, u1, u3} m R α γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_6 _inst_7 _inst_9 (AlgHom.comp.{u3, u4, u5, u2} R α β γ _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 f g))
Case conversion may be inaccurate. Consider using '#align alg_hom.map_matrix_comp AlgHom.mapMatrix_compₓ'. -/
@[simp]
theorem mapMatrix_comp (f : β →ₐ[R] γ) (g : α →ₐ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →ₐ[R] _) :=
  rfl
#align alg_hom.map_matrix_comp AlgHom.mapMatrix_comp

end AlgHom

namespace AlgEquiv

variable [Fintype m] [DecidableEq m]

variable [CommSemiring R] [Semiring α] [Semiring β] [Semiring γ]

variable [Algebra R α] [Algebra R β] [Algebra R γ]

/- warning: alg_equiv.map_matrix -> AlgEquiv.mapMatrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : CommSemiring.{u4} R] [_inst_4 : Semiring.{u1} α] [_inst_5 : Semiring.{u2} β] [_inst_7 : Algebra.{u4, u1} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u4, u2} R β _inst_3 _inst_5], (AlgEquiv.{u4, u1, u2} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8) -> (AlgEquiv.{u4, max u3 u1, max u3 u2} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u3} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u2, u3, u4} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8))
but is expected to have type
  forall {m : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : CommSemiring.{u4} R] [_inst_4 : Semiring.{u1} α] [_inst_5 : Semiring.{u2} β] [_inst_7 : Algebra.{u4, u1} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u4, u2} R β _inst_3 _inst_5], (AlgEquiv.{u4, u1, u2} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8) -> (AlgEquiv.{u4, max u1 u3, max u2 u3} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u3} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u2, u3, u4} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8))
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_matrix AlgEquiv.mapMatrixₓ'. -/
/-- The `alg_equiv` between spaces of square matrices induced by a `alg_equiv` between their
coefficients. This is `matrix.map` as a `alg_equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ₐ[R] β) : Matrix m m α ≃ₐ[R] Matrix m m β :=
  { f.toAlgHom.mapMatrix,
    f.toRingEquiv.mapMatrix with
    toFun := fun M => M.map f
    invFun := fun M => M.map f.symm }
#align alg_equiv.map_matrix AlgEquiv.mapMatrix

/- warning: alg_equiv.map_matrix_refl -> AlgEquiv.mapMatrix_refl is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u1} α] [_inst_7 : Algebra.{u3, u1} R α _inst_3 _inst_4], Eq.{succ (max u2 u1)} (AlgEquiv.{u3, max u2 u1, max u2 u1} R (Matrix.{u2, u2, u1} m m α) (Matrix.{u2, u2, u1} m m α) _inst_3 (Matrix.semiring.{u1, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u1, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u2, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u1, u2, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7)) (AlgEquiv.mapMatrix.{u1, u1, u2, u3} m R α α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_4 _inst_7 _inst_7 (AlgEquiv.refl.{u3, u1} R α _inst_3 _inst_4 _inst_7)) (AlgEquiv.refl.{u3, max u2 u1} R (Matrix.{u2, u2, u1} m m α) _inst_3 (Matrix.semiring.{u1, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u2, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7))
but is expected to have type
  forall {m : Type.{u2}} {R : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : Semiring.{u3} α] [_inst_7 : Algebra.{u1, u3} R α _inst_3 _inst_4], Eq.{max (succ u3) (succ u2)} (AlgEquiv.{u1, max u3 u2, max u3 u2} R (Matrix.{u2, u2, u3} m m α) (Matrix.{u2, u2, u3} m m α) _inst_3 (Matrix.semiring.{u3, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u3, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7)) (AlgEquiv.mapMatrix.{u3, u3, u2, u1} m R α α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_4 _inst_7 _inst_7 (AlgEquiv.refl.{u1, u3} R α _inst_3 _inst_4 _inst_7)) (AlgEquiv.refl.{u1, max u3 u2} R (Matrix.{u2, u2, u3} m m α) _inst_3 (Matrix.semiring.{u3, u2} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u2, u1} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7))
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_matrix_refl AlgEquiv.mapMatrix_reflₓ'. -/
@[simp]
theorem mapMatrix_refl : AlgEquiv.refl.mapMatrix = (AlgEquiv.refl : Matrix m m α ≃ₐ[R] _) :=
  rfl
#align alg_equiv.map_matrix_refl AlgEquiv.mapMatrix_refl

/- warning: alg_equiv.map_matrix_symm -> AlgEquiv.mapMatrix_symm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : CommSemiring.{u4} R] [_inst_4 : Semiring.{u1} α] [_inst_5 : Semiring.{u2} β] [_inst_7 : Algebra.{u4, u1} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u4, u2} R β _inst_3 _inst_5] (f : AlgEquiv.{u4, u1, u2} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8), Eq.{max (succ (max u3 u2)) (succ (max u3 u1))} (AlgEquiv.{u4, max u3 u2, max u3 u1} R (Matrix.{u3, u3, u2} m m β) (Matrix.{u3, u3, u1} m m α) _inst_3 (Matrix.semiring.{u2, u3} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u2, u3, u4} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8) (Matrix.algebra.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7)) (AlgEquiv.symm.{u4, max u3 u1, max u3 u2} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u3} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u2, u3, u4} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8) (AlgEquiv.mapMatrix.{u1, u2, u3, u4} m R α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_5 _inst_7 _inst_8 f)) (AlgEquiv.mapMatrix.{u2, u1, u3, u4} m R β α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_4 _inst_8 _inst_7 (AlgEquiv.symm.{u4, u1, u2} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8 f))
but is expected to have type
  forall {m : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : CommSemiring.{u2} R] [_inst_4 : Semiring.{u3} α] [_inst_5 : Semiring.{u4} β] [_inst_7 : Algebra.{u2, u3} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u2, u4} R β _inst_3 _inst_5] (f : AlgEquiv.{u2, u3, u4} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8), Eq.{max (max (succ u3) (succ u4)) (succ u1)} (AlgEquiv.{u2, max u4 u1, max u3 u1} R (Matrix.{u1, u1, u4} m m β) (Matrix.{u1, u1, u3} m m α) _inst_3 (Matrix.semiring.{u4, u1} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u3, u1} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u4, u1, u2} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8) (Matrix.instAlgebraMatrixSemiring.{u3, u1, u2} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7)) (AlgEquiv.symm.{u2, max u3 u1, max u4 u1} R (Matrix.{u1, u1, u3} m m α) (Matrix.{u1, u1, u4} m m β) _inst_3 (Matrix.semiring.{u3, u1} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u4, u1} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u3, u1, u2} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u4, u1, u2} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8) (AlgEquiv.mapMatrix.{u3, u4, u1, u2} m R α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_5 _inst_7 _inst_8 f)) (AlgEquiv.mapMatrix.{u4, u3, u1, u2} m R β α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_4 _inst_8 _inst_7 (AlgEquiv.symm.{u2, u3, u4} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8 f))
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_matrix_symm AlgEquiv.mapMatrix_symmₓ'. -/
@[simp]
theorem mapMatrix_symm (f : α ≃ₐ[R] β) :
    f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃ₐ[R] _) :=
  rfl
#align alg_equiv.map_matrix_symm AlgEquiv.mapMatrix_symm

/- warning: alg_equiv.map_matrix_trans -> AlgEquiv.mapMatrix_trans is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u5}} [_inst_1 : Fintype.{u3} m] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : CommSemiring.{u4} R] [_inst_4 : Semiring.{u1} α] [_inst_5 : Semiring.{u2} β] [_inst_6 : Semiring.{u5} γ] [_inst_7 : Algebra.{u4, u1} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u4, u2} R β _inst_3 _inst_5] [_inst_9 : Algebra.{u4, u5} R γ _inst_3 _inst_6] (f : AlgEquiv.{u4, u1, u2} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8) (g : AlgEquiv.{u4, u2, u5} R β γ _inst_3 _inst_5 _inst_6 _inst_8 _inst_9), Eq.{max (succ (max u3 u1)) (succ (max u3 u5))} (AlgEquiv.{u4, max u3 u1, max u3 u5} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u5} m m γ) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u5, u3} m γ _inst_6 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u5, u3, u4} m R γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_6 _inst_9)) (AlgEquiv.trans.{u4, max u3 u1, max u3 u2, max u3 u5} R (Matrix.{u3, u3, u1} m m α) (Matrix.{u3, u3, u2} m m β) (Matrix.{u3, u3, u5} m m γ) _inst_3 (Matrix.semiring.{u1, u3} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u3} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u5, u3} m γ _inst_6 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.algebra.{u1, u3, u4} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.algebra.{u2, u3, u4} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8) (Matrix.algebra.{u5, u3, u4} m R γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_6 _inst_9) (AlgEquiv.mapMatrix.{u1, u2, u3, u4} m R α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_5 _inst_7 _inst_8 f) (AlgEquiv.mapMatrix.{u2, u5, u3, u4} m R β γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_6 _inst_8 _inst_9 g)) (AlgEquiv.mapMatrix.{u1, u5, u3, u4} m R α γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_6 _inst_7 _inst_9 (AlgEquiv.trans.{u4, u1, u2, u5} R α β γ _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 f g))
but is expected to have type
  forall {m : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} {β : Type.{u5}} {γ : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : Semiring.{u4} α] [_inst_5 : Semiring.{u5} β] [_inst_6 : Semiring.{u2} γ] [_inst_7 : Algebra.{u3, u4} R α _inst_3 _inst_4] [_inst_8 : Algebra.{u3, u5} R β _inst_3 _inst_5] [_inst_9 : Algebra.{u3, u2} R γ _inst_3 _inst_6] (f : AlgEquiv.{u3, u4, u5} R α β _inst_3 _inst_4 _inst_5 _inst_7 _inst_8) (g : AlgEquiv.{u3, u5, u2} R β γ _inst_3 _inst_5 _inst_6 _inst_8 _inst_9), Eq.{max (max (succ u4) (succ u1)) (succ u2)} (AlgEquiv.{u3, max u4 u1, max u2 u1} R (Matrix.{u1, u1, u4} m m α) (Matrix.{u1, u1, u2} m m γ) _inst_3 (Matrix.semiring.{u4, u1} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u1} m γ _inst_6 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u4, u1, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u2, u1, u3} m R γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_6 _inst_9)) (AlgEquiv.trans.{u3, max u4 u1, max u5 u1, max u2 u1} R (Matrix.{u1, u1, u4} m m α) (Matrix.{u1, u1, u5} m m β) (Matrix.{u1, u1, u2} m m γ) _inst_3 (Matrix.semiring.{u4, u1} m α _inst_4 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u5, u1} m β _inst_5 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.semiring.{u2, u1} m γ _inst_6 _inst_1 (fun (a : m) (b : m) => _inst_2 a b)) (Matrix.instAlgebraMatrixSemiring.{u4, u1, u3} m R α _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_7) (Matrix.instAlgebraMatrixSemiring.{u5, u1, u3} m R β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_8) (Matrix.instAlgebraMatrixSemiring.{u2, u1, u3} m R γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_6 _inst_9) (AlgEquiv.mapMatrix.{u4, u5, u1, u3} m R α β _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_5 _inst_7 _inst_8 f) (AlgEquiv.mapMatrix.{u5, u2, u1, u3} m R β γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_5 _inst_6 _inst_8 _inst_9 g)) (AlgEquiv.mapMatrix.{u4, u2, u1, u3} m R α γ _inst_1 (fun (a : m) (b : m) => _inst_2 a b) _inst_3 _inst_4 _inst_6 _inst_7 _inst_9 (AlgEquiv.trans.{u3, u4, u5, u2} R α β γ _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 f g))
Case conversion may be inaccurate. Consider using '#align alg_equiv.map_matrix_trans AlgEquiv.mapMatrix_transₓ'. -/
@[simp]
theorem mapMatrix_trans (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃ₐ[R] _) :=
  rfl
#align alg_equiv.map_matrix_trans AlgEquiv.mapMatrix_trans

end AlgEquiv

open Matrix

namespace Matrix

#print Matrix.vecMulVec /-
/-- For two vectors `w` and `v`, `vec_mul_vec w v i j` is defined to be `w i * v j`.
    Put another way, `vec_mul_vec w v` is exactly `col w ⬝ row v`. -/
def vecMulVec [Mul α] (w : m → α) (v : n → α) : Matrix m n α :=
  of fun x y => w x * v y
#align matrix.vec_mul_vec Matrix.vecMulVec
-/

/- warning: matrix.vec_mul_vec_apply -> Matrix.vecMulVec_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Mul.{u1} α] (w : m -> α) (v : n -> α) (i : m) (j : n), Eq.{succ u1} α (Matrix.vecMulVec.{u1, u2, u3} m n α _inst_1 w v i j) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (w i) (v j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Mul.{u3} α] (w : m -> α) (v : n -> α) (i : m) (j : n), Eq.{succ u3} α (Matrix.vecMulVec.{u3, u2, u1} m n α _inst_1 w v i j) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α _inst_1) (w i) (v j))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_vec_apply Matrix.vecMulVec_applyₓ'. -/
-- TODO: set as an equation lemma for `vec_mul_vec`, see mathlib4#3024
theorem vecMulVec_apply [Mul α] (w : m → α) (v : n → α) (i j) : vecMulVec w v i j = w i * v j :=
  rfl
#align matrix.vec_mul_vec_apply Matrix.vecMulVec_apply

/- warning: matrix.vec_mul_vec_eq -> Matrix.vecMulVec_eq is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] (w : m -> α) (v : n -> α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.vecMulVec.{u1, u2, u3} m n α _inst_1 w v) (Matrix.mul.{u1, u2, 0, u3} m Unit n α PUnit.fintype.{0} _inst_1 _inst_2 (Matrix.col.{u1, u2} m α w) (Matrix.row.{u1, u3} n α v))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Mul.{u3} α] [_inst_2 : AddCommMonoid.{u3} α] (w : m -> α) (v : n -> α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.vecMulVec.{u3, u2, u1} m n α _inst_1 w v) (Matrix.mul.{u3, u2, 0, u1} m Unit n α PUnit.fintype.{0} _inst_1 _inst_2 (Matrix.col.{u3, u2} m α w) (Matrix.row.{u3, u1} n α v))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_vec_eq Matrix.vecMulVec_eqₓ'. -/
theorem vecMulVec_eq [Mul α] [AddCommMonoid α] (w : m → α) (v : n → α) :
    vecMulVec w v = col w ⬝ row v := by
  ext (i j)
  simp only [vec_mul_vec, mul_apply, Fintype.univ_punit, Finset.sum_singleton]
  rfl
#align matrix.vec_mul_vec_eq Matrix.vecMulVec_eq

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

#print Matrix.mulVec /-
/-- `mul_vec M v` is the matrix-vector product of `M` and `v`, where `v` is seen as a column matrix.
    Put another way, `mul_vec M v` is the vector whose entries
    are those of `M ⬝ col v` (see `col_mul_vec`). -/
def mulVec [Fintype n] (M : Matrix m n α) (v : n → α) : m → α
  | i => (fun j => M i j) ⬝ᵥ v
#align matrix.mul_vec Matrix.mulVec
-/

#print Matrix.vecMul /-
/-- `vec_mul v M` is the vector-matrix product of `v` and `M`, where `v` is seen as a row matrix.
    Put another way, `vec_mul v M` is the vector whose entries
    are those of `row v ⬝ M` (see `row_vec_mul`). -/
def vecMul [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
  | j => v ⬝ᵥ fun i => M i j
#align matrix.vec_mul Matrix.vecMul
-/

#print Matrix.mulVec.addMonoidHomLeft /-
/-- Left multiplication by a matrix, as an `add_monoid_hom` from vectors to vectors. -/
@[simps]
def mulVec.addMonoidHomLeft [Fintype n] (v : n → α) : Matrix m n α →+ m → α
    where
  toFun M := mulVec M v
  map_zero' := by ext <;> simp [mul_vec] <;> rfl
  map_add' x y := by
    ext m
    apply add_dot_product
#align matrix.mul_vec.add_monoid_hom_left Matrix.mulVec.addMonoidHomLeft
-/

/- warning: matrix.mul_vec_diagonal -> Matrix.mulVec_diagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (v : m -> α) (w : m -> α) (x : m), Eq.{succ u1} α (Matrix.mulVec.{u1, u2, u2} m m α _inst_1 _inst_2 (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) v) w x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (v x) (w x))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] (v : m -> α) (w : m -> α) (x : m), Eq.{succ u2} α (Matrix.mulVec.{u2, u1, u1} m m α _inst_1 _inst_2 (Matrix.diagonal.{u2, u1} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_1)) v) w x) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (v x) (w x))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_diagonal Matrix.mulVec_diagonalₓ'. -/
theorem mulVec_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) :
    mulVec (diagonal v) w x = v x * w x :=
  diagonal_dotProduct v w x
#align matrix.mul_vec_diagonal Matrix.mulVec_diagonal

/- warning: matrix.vec_mul_diagonal -> Matrix.vecMul_diagonal is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (v : m -> α) (w : m -> α) (x : m), Eq.{succ u1} α (Matrix.vecMul.{u1, u2, u2} m m α _inst_1 _inst_2 v (Matrix.diagonal.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)) w) x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (v x) (w x))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] (v : m -> α) (w : m -> α) (x : m), Eq.{succ u2} α (Matrix.vecMul.{u2, u1, u1} m m α _inst_1 _inst_2 v (Matrix.diagonal.{u2, u1} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α _inst_1)) w) x) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (v x) (w x))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_diagonal Matrix.vecMul_diagonalₓ'. -/
theorem vecMul_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) :
    vecMul v (diagonal w) x = v x * w x :=
  dotProduct_diagonal' v w x
#align matrix.vec_mul_diagonal Matrix.vecMul_diagonal

/- warning: matrix.dot_product_mul_vec -> Matrix.dotProduct_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : Fintype.{u2} n] [_inst_3 : Fintype.{u1} m] [_inst_4 : NonUnitalSemiring.{u3} R] (v : m -> R) (A : Matrix.{u1, u2, u3} m n R) (w : n -> R), Eq.{succ u3} R (Matrix.dotProduct.{u3, u1} m R _inst_3 (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) v (Matrix.mulVec.{u3, u1, u2} m n R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4) _inst_2 A w)) (Matrix.dotProduct.{u3, u2} n R _inst_2 (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) (Matrix.vecMul.{u3, u1, u2} m n R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4) _inst_3 v A) w)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u1}} [_inst_2 : Fintype.{u3} n] [_inst_3 : Fintype.{u2} m] [_inst_4 : NonUnitalSemiring.{u1} R] (v : m -> R) (A : Matrix.{u2, u3, u1} m n R) (w : n -> R), Eq.{succ u1} R (Matrix.dotProduct.{u1, u2} m R _inst_3 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_4)) v (Matrix.mulVec.{u1, u2, u3} m n R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_4) _inst_2 A w)) (Matrix.dotProduct.{u1, u3} n R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_4)) (Matrix.vecMul.{u1, u2, u3} m n R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_4) _inst_3 v A) w)
Case conversion may be inaccurate. Consider using '#align matrix.dot_product_mul_vec Matrix.dotProduct_mulVecₓ'. -/
/-- Associate the dot product of `mul_vec` to the left. -/
theorem dotProduct_mulVec [Fintype n] [Fintype m] [NonUnitalSemiring R] (v : m → R)
    (A : Matrix m n R) (w : n → R) : v ⬝ᵥ mulVec A w = vecMul v A ⬝ᵥ w := by
  simp only [dot_product, vec_mul, mul_vec, Finset.mul_sum, Finset.sum_mul, mul_assoc] <;>
    exact Finset.sum_comm
#align matrix.dot_product_mul_vec Matrix.dotProduct_mulVec

/- warning: matrix.mul_vec_zero -> Matrix.mulVec_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (A : Matrix.{u2, u3, u1} m n α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 A (OfNat.ofNat.{max u3 u1} (n -> α) 0 (OfNat.mk.{max u3 u1} (n -> α) 0 (Zero.zero.{max u3 u1} (n -> α) (Pi.instZero.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))) (OfNat.ofNat.{max u2 u1} (m -> α) 0 (OfNat.mk.{max u2 u1} (m -> α) 0 (Zero.zero.{max u2 u1} (m -> α) (Pi.instZero.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] (A : Matrix.{u1, u2, u3} m n α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.mulVec.{u3, u1, u2} m n α _inst_1 _inst_2 A (OfNat.ofNat.{max u3 u2} (n -> α) 0 (Zero.toOfNat0.{max u3 u2} (n -> α) (Pi.instZero.{u2, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17551 : n) => α) (fun (i : n) => MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)))))) (OfNat.ofNat.{max u3 u1} (m -> α) 0 (Zero.toOfNat0.{max u3 u1} (m -> α) (Pi.instZero.{u1, u3} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17554 : m) => α) (fun (i : m) => MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_zero Matrix.mulVec_zeroₓ'. -/
@[simp]
theorem mulVec_zero [Fintype n] (A : Matrix m n α) : mulVec A 0 = 0 :=
  by
  ext
  simp [mul_vec]
#align matrix.mul_vec_zero Matrix.mulVec_zero

/- warning: matrix.zero_vec_mul -> Matrix.zero_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u3, u1} m n α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u1, u2, u3} m n α _inst_1 _inst_2 (OfNat.ofNat.{max u2 u1} (m -> α) 0 (OfNat.mk.{max u2 u1} (m -> α) 0 (Zero.zero.{max u2 u1} (m -> α) (Pi.instZero.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)))))) A) (OfNat.ofNat.{max u3 u1} (n -> α) 0 (OfNat.mk.{max u3 u1} (n -> α) 0 (Zero.zero.{max u3 u1} (n -> α) (Pi.instZero.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u1, u3} m n α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u3, u2, u1} m n α _inst_1 _inst_2 (OfNat.ofNat.{max u2 u3} (m -> α) 0 (Zero.toOfNat0.{max u3 u2} (m -> α) (Pi.instZero.{u2, u3} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17605 : m) => α) (fun (i : m) => MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1))))) A) (OfNat.ofNat.{max u3 u1} (n -> α) 0 (Zero.toOfNat0.{max u3 u1} (n -> α) (Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17612 : n) => α) (fun (i : n) => MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.zero_vec_mul Matrix.zero_vecMulₓ'. -/
@[simp]
theorem zero_vecMul [Fintype m] (A : Matrix m n α) : vecMul 0 A = 0 :=
  by
  ext
  simp [vec_mul]
#align matrix.zero_vec_mul Matrix.zero_vecMul

/- warning: matrix.zero_mul_vec -> Matrix.zero_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (v : n -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1)))))) v) (OfNat.ofNat.{max u2 u1} (m -> α) 0 (OfNat.mk.{max u2 u1} (m -> α) 0 (Zero.zero.{max u2 u1} (m -> α) (Pi.instZero.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] (v : n -> α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.mulVec.{u3, u1, u2} m n α _inst_1 _inst_2 (OfNat.ofNat.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.zero.{u3, u1, u2} m n α (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1))))) v) (OfNat.ofNat.{max u3 u1} (m -> α) 0 (Zero.toOfNat0.{max u3 u1} (m -> α) (Pi.instZero.{u1, u3} m (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17554 : m) => α) (fun (i : m) => MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.zero_mul_vec Matrix.zero_mulVecₓ'. -/
@[simp]
theorem zero_mulVec [Fintype n] (v : n → α) : mulVec (0 : Matrix m n α) v = 0 :=
  by
  ext
  simp [mul_vec]
#align matrix.zero_mul_vec Matrix.zero_mulVec

/- warning: matrix.vec_mul_zero -> Matrix.vecMul_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] (v : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u1, u2, u3} m n α _inst_1 _inst_2 v (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))) (OfNat.ofNat.{max u3 u1} (n -> α) 0 (OfNat.mk.{max u3 u1} (n -> α) 0 (Zero.zero.{max u3 u1} (n -> α) (Pi.instZero.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] (v : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u3, u2, u1} m n α _inst_1 _inst_2 v (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.zero.{u3, u2, u1} m n α (MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)))))) (OfNat.ofNat.{max u3 u1} (n -> α) 0 (Zero.toOfNat0.{max u3 u1} (n -> α) (Pi.instZero.{u1, u3} n (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17612 : n) => α) (fun (i : n) => MulZeroClass.toZero.{u3} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_zero Matrix.vecMul_zeroₓ'. -/
@[simp]
theorem vecMul_zero [Fintype m] (v : m → α) : vecMul v (0 : Matrix m n α) = 0 :=
  by
  ext
  simp [vec_mul]
#align matrix.vec_mul_zero Matrix.vecMul_zero

/- warning: matrix.smul_mul_vec_assoc -> Matrix.smul_mulVec_assoc is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : Monoid.{u4} R] [_inst_4 : DistribMulAction.{u4, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))] [_inst_5 : IsScalarTower.{u4, u1, u1} R α α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u4, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u4, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4))) (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1))) (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u4, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u4, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))] (a : R) (A : Matrix.{u2, u3, u1} m n α) (b : n -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u4, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u4, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))) a A) b) (SMul.smul.{u4, max u2 u1} R (m -> α) (Function.hasSMul.{u2, u4, u1} m R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)))) (DistribSMul.toSmulZeroClass.{u4, u1} R α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1))) (DistribMulAction.toDistribSMul.{u4, u1} R α _inst_3 (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1)) _inst_4)))) a (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 A b))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} {α : Type.{u4}} [_inst_1 : NonUnitalNonAssocSemiring.{u4} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : Monoid.{u2} R] [_inst_4 : DistribMulAction.{u2, u4} R α _inst_3 (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1))] [_inst_5 : IsScalarTower.{u2, u4, u4} R α α (SMulZeroClass.toSMul.{u2, u4} R α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)) (DistribSMul.toSMulZeroClass.{u2, u4} R α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1))) (DistribMulAction.toDistribSMul.{u2, u4} R α _inst_3 (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1)) _inst_4))) (SMulZeroClass.toSMul.{u4, u4} α α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)) (SMulWithZero.toSMulZeroClass.{u4, u4} α α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)) (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)) (MulZeroClass.toSMulWithZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)))) (SMulZeroClass.toSMul.{u2, u4} R α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)) (DistribSMul.toSMulZeroClass.{u2, u4} R α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1))) (DistribMulAction.toDistribSMul.{u2, u4} R α _inst_3 (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1)) _inst_4)))] (a : R) (A : Matrix.{u1, u3, u4} m n α) (b : n -> α), Eq.{max (succ u4) (succ u1)} (m -> α) (Matrix.mulVec.{u4, u1, u3} m n α _inst_1 _inst_2 (HSMul.hSMul.{u2, max (max u4 u1) u3, max (max u4 u1) u3} R (Matrix.{u1, u3, u4} m n α) (Matrix.{u1, u3, u4} m n α) (instHSMul.{u2, max (max u4 u1) u3} R (Matrix.{u1, u3, u4} m n α) (Matrix.smul.{u4, u1, u3, u2} m n R α (SMulZeroClass.toSMul.{u2, u4} R α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)) (DistribSMul.toSMulZeroClass.{u2, u4} R α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1))) (DistribMulAction.toDistribSMul.{u2, u4} R α _inst_3 (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1)) _inst_4))))) a A) b) (HSMul.hSMul.{u2, max u4 u1, max u4 u1} R (m -> α) (m -> α) (instHSMul.{u2, max u4 u1} R (m -> α) (Pi.instSMul.{u1, u4, u2} m R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17554 : m) => α) (fun (i : m) => SMulZeroClass.toSMul.{u2, u4} R α (MulZeroClass.toZero.{u4} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u4} α _inst_1)) (DistribSMul.toSMulZeroClass.{u2, u4} R α (AddMonoid.toAddZeroClass.{u4} α (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1))) (DistribMulAction.toDistribSMul.{u2, u4} R α _inst_3 (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α _inst_1)) _inst_4))))) a (Matrix.mulVec.{u4, u1, u3} m n α _inst_1 _inst_2 A b))
Case conversion may be inaccurate. Consider using '#align matrix.smul_mul_vec_assoc Matrix.smul_mulVec_assocₓ'. -/
theorem smul_mulVec_assoc [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α]
    (a : R) (A : Matrix m n α) (b : n → α) : (a • A).mulVec b = a • A.mulVec b :=
  by
  ext
  apply smul_dot_product
#align matrix.smul_mul_vec_assoc Matrix.smul_mulVec_assoc

/- warning: matrix.mul_vec_add -> Matrix.mulVec_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (A : Matrix.{u2, u3, u1} m n α) (x : n -> α) (y : n -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 A (HAdd.hAdd.{max u3 u1, max u3 u1, max u3 u1} (n -> α) (n -> α) (n -> α) (instHAdd.{max u3 u1} (n -> α) (Pi.instAdd.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) x y)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 A x) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 A y))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] (A : Matrix.{u1, u2, u3} m n α) (x : n -> α) (y : n -> α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.mulVec.{u3, u1, u2} m n α _inst_1 _inst_2 A (HAdd.hAdd.{max u3 u2, max u3 u2, max u3 u2} (n -> α) (n -> α) (n -> α) (instHAdd.{max u3 u2} (n -> α) (Pi.instAdd.{u2, u3} n (fun (ᾰ : n) => α) (fun (i : n) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_1)))) x y)) (HAdd.hAdd.{max u3 u1, max u3 u1, max u3 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u3 u1} (m -> α) (Pi.instAdd.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_1)))) (Matrix.mulVec.{u3, u1, u2} m n α _inst_1 _inst_2 A x) (Matrix.mulVec.{u3, u1, u2} m n α _inst_1 _inst_2 A y))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_add Matrix.mulVec_addₓ'. -/
theorem mulVec_add [Fintype n] (A : Matrix m n α) (x y : n → α) :
    A.mulVec (x + y) = A.mulVec x + A.mulVec y :=
  by
  ext
  apply dot_product_add
#align matrix.mul_vec_add Matrix.mulVec_add

/- warning: matrix.add_mul_vec -> Matrix.add_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) (x : n -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) A B) x) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 A x) (Matrix.mulVec.{u1, u2, u3} m n α _inst_1 _inst_2 B x))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] (A : Matrix.{u1, u2, u3} m n α) (B : Matrix.{u1, u2, u3} m n α) (x : n -> α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.mulVec.{u3, u1, u2} m n α _inst_1 _inst_2 (HAdd.hAdd.{max (max u3 u1) u2, max (max u3 u1) u2, max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (instHAdd.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.add.{u3, u1, u2} m n α (Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_1)))) A B) x) (HAdd.hAdd.{max u3 u1, max u3 u1, max u3 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u3 u1} (m -> α) (Pi.instAdd.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_1)))) (Matrix.mulVec.{u3, u1, u2} m n α _inst_1 _inst_2 A x) (Matrix.mulVec.{u3, u1, u2} m n α _inst_1 _inst_2 B x))
Case conversion may be inaccurate. Consider using '#align matrix.add_mul_vec Matrix.add_mulVecₓ'. -/
theorem add_mulVec [Fintype n] (A B : Matrix m n α) (x : n → α) :
    (A + B).mulVec x = A.mulVec x + B.mulVec x :=
  by
  ext
  apply add_dot_product
#align matrix.add_mul_vec Matrix.add_mulVec

/- warning: matrix.vec_mul_add -> Matrix.vecMul_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) (x : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u1, u2, u3} m n α _inst_1 _inst_2 x (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) A B)) (HAdd.hAdd.{max u3 u1, max u3 u1, max u3 u1} (n -> α) (n -> α) (n -> α) (instHAdd.{max u3 u1} (n -> α) (Pi.instAdd.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) (Matrix.vecMul.{u1, u2, u3} m n α _inst_1 _inst_2 x A) (Matrix.vecMul.{u1, u2, u3} m n α _inst_1 _inst_2 x B))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u1, u3} m n α) (B : Matrix.{u2, u1, u3} m n α) (x : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u3, u2, u1} m n α _inst_1 _inst_2 x (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α (Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_1)))) A B)) (HAdd.hAdd.{max u3 u1, max u3 u1, max u3 u1} (n -> α) (n -> α) (n -> α) (instHAdd.{max u3 u1} (n -> α) (Pi.instAdd.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_1)))) (Matrix.vecMul.{u3, u2, u1} m n α _inst_1 _inst_2 x A) (Matrix.vecMul.{u3, u2, u1} m n α _inst_1 _inst_2 x B))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_add Matrix.vecMul_addₓ'. -/
theorem vecMul_add [Fintype m] (A B : Matrix m n α) (x : m → α) :
    vecMul x (A + B) = vecMul x A + vecMul x B :=
  by
  ext
  apply dot_product_add
#align matrix.vec_mul_add Matrix.vecMul_add

/- warning: matrix.add_vec_mul -> Matrix.add_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u3, u1} m n α) (x : m -> α) (y : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u1, u2, u3} m n α _inst_1 _inst_2 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) x y) A) (HAdd.hAdd.{max u3 u1, max u3 u1, max u3 u1} (n -> α) (n -> α) (n -> α) (instHAdd.{max u3 u1} (n -> α) (Pi.instAdd.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)))) (Matrix.vecMul.{u1, u2, u3} m n α _inst_1 _inst_2 x A) (Matrix.vecMul.{u1, u2, u3} m n α _inst_1 _inst_2 y A))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u1, u3} m n α) (x : m -> α) (y : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u3, u2, u1} m n α _inst_1 _inst_2 (HAdd.hAdd.{max u3 u2, max u3 u2, max u3 u2} (m -> α) (m -> α) (m -> α) (instHAdd.{max u3 u2} (m -> α) (Pi.instAdd.{u2, u3} m (fun (ᾰ : m) => α) (fun (i : m) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_1)))) x y) A) (HAdd.hAdd.{max u3 u1, max u3 u1, max u3 u1} (n -> α) (n -> α) (n -> α) (instHAdd.{max u3 u1} (n -> α) (Pi.instAdd.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => Distrib.toAdd.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_1)))) (Matrix.vecMul.{u3, u2, u1} m n α _inst_1 _inst_2 x A) (Matrix.vecMul.{u3, u2, u1} m n α _inst_1 _inst_2 y A))
Case conversion may be inaccurate. Consider using '#align matrix.add_vec_mul Matrix.add_vecMulₓ'. -/
theorem add_vecMul [Fintype m] (A : Matrix m n α) (x y : m → α) :
    vecMul (x + y) A = vecMul x A + vecMul y A :=
  by
  ext
  apply add_dot_product
#align matrix.add_vec_mul Matrix.add_vecMul

/- warning: matrix.vec_mul_smul -> Matrix.vecMul_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} {S : Type.{u4}} [_inst_2 : Fintype.{u2} n] [_inst_3 : Monoid.{u3} R] [_inst_4 : NonUnitalNonAssocSemiring.{u4} S] [_inst_5 : DistribMulAction.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))] [_inst_6 : IsScalarTower.{u3, u4, u4} R S S (SMulZeroClass.toHasSmul.{u3, u4} R S (AddZeroClass.toHasZero.{u4} S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)))) (DistribSMul.toSmulZeroClass.{u3, u4} R S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)) _inst_5))) (Mul.toSMul.{u4} S (Distrib.toHasMul.{u4} S (NonUnitalNonAssocSemiring.toDistrib.{u4} S _inst_4))) (SMulZeroClass.toHasSmul.{u3, u4} R S (AddZeroClass.toHasZero.{u4} S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)))) (DistribSMul.toSmulZeroClass.{u3, u4} R S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)) _inst_5)))] (M : Matrix.{u2, u1, u4} n m S) (b : R) (v : n -> S), Eq.{max (succ u1) (succ u4)} (m -> S) (Matrix.vecMul.{u4, u2, u1} n m S _inst_4 _inst_2 (SMul.smul.{u3, max u2 u4} R (n -> S) (Function.hasSMul.{u2, u3, u4} n R S (SMulZeroClass.toHasSmul.{u3, u4} R S (AddZeroClass.toHasZero.{u4} S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)))) (DistribSMul.toSmulZeroClass.{u3, u4} R S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)) _inst_5)))) b v) M) (SMul.smul.{u3, max u1 u4} R (m -> S) (Function.hasSMul.{u1, u3, u4} m R S (SMulZeroClass.toHasSmul.{u3, u4} R S (AddZeroClass.toHasZero.{u4} S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)))) (DistribSMul.toSmulZeroClass.{u3, u4} R S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)) _inst_5)))) b (Matrix.vecMul.{u4, u2, u1} n m S _inst_4 _inst_2 v M))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u4}} {R : Type.{u3}} {S : Type.{u2}} [_inst_2 : Fintype.{u4} n] [_inst_3 : Monoid.{u3} R] [_inst_4 : NonUnitalNonAssocSemiring.{u2} S] [_inst_5 : DistribMulAction.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))] [_inst_6 : IsScalarTower.{u3, u2, u2} R S S (SMulZeroClass.toSMul.{u3, u2} R S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} R S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4)) _inst_5))) (SMulZeroClass.toSMul.{u2, u2} S S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (SMulWithZero.toSMulZeroClass.{u2, u2} S S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (MulZeroClass.toSMulWithZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)))) (SMulZeroClass.toSMul.{u3, u2} R S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} R S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4)) _inst_5)))] (M : Matrix.{u4, u1, u2} n m S) (b : R) (v : n -> S), Eq.{max (succ u1) (succ u2)} (m -> S) (Matrix.vecMul.{u2, u4, u1} n m S _inst_4 _inst_2 (HSMul.hSMul.{u3, max u4 u2, max u4 u2} R (n -> S) (n -> S) (instHSMul.{u3, max u4 u2} R (n -> S) (Pi.instSMul.{u4, u2, u3} n R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18375 : n) => S) (fun (i : n) => SMulZeroClass.toSMul.{u3, u2} R S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} R S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4)) _inst_5))))) b v) M) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} R (m -> S) (m -> S) (instHSMul.{u3, max u1 u2} R (m -> S) (Pi.instSMul.{u1, u2, u3} m R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17612 : m) => S) (fun (i : m) => SMulZeroClass.toSMul.{u3, u2} R S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} R S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4)) _inst_5))))) b (Matrix.vecMul.{u2, u4, u1} n m S _inst_4 _inst_2 v M))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_smul Matrix.vecMul_smulₓ'. -/
theorem vecMul_smul [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring S] [DistribMulAction R S]
    [IsScalarTower R S S] (M : Matrix n m S) (b : R) (v : n → S) :
    M.vecMul (b • v) = b • M.vecMul v := by
  ext i
  simp only [vec_mul, dot_product, Finset.smul_sum, Pi.smul_apply, smul_mul_assoc]
#align matrix.vec_mul_smul Matrix.vecMul_smul

/- warning: matrix.mul_vec_smul -> Matrix.mulVec_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} {S : Type.{u4}} [_inst_2 : Fintype.{u2} n] [_inst_3 : Monoid.{u3} R] [_inst_4 : NonUnitalNonAssocSemiring.{u4} S] [_inst_5 : DistribMulAction.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))] [_inst_6 : SMulCommClass.{u3, u4, u4} R S S (SMulZeroClass.toHasSmul.{u3, u4} R S (AddZeroClass.toHasZero.{u4} S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)))) (DistribSMul.toSmulZeroClass.{u3, u4} R S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)) _inst_5))) (Mul.toSMul.{u4} S (Distrib.toHasMul.{u4} S (NonUnitalNonAssocSemiring.toDistrib.{u4} S _inst_4)))] (M : Matrix.{u1, u2, u4} m n S) (b : R) (v : n -> S), Eq.{max (succ u1) (succ u4)} (m -> S) (Matrix.mulVec.{u4, u1, u2} m n S _inst_4 _inst_2 M (SMul.smul.{u3, max u2 u4} R (n -> S) (Function.hasSMul.{u2, u3, u4} n R S (SMulZeroClass.toHasSmul.{u3, u4} R S (AddZeroClass.toHasZero.{u4} S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)))) (DistribSMul.toSmulZeroClass.{u3, u4} R S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)) _inst_5)))) b v)) (SMul.smul.{u3, max u1 u4} R (m -> S) (Function.hasSMul.{u1, u3, u4} m R S (SMulZeroClass.toHasSmul.{u3, u4} R S (AddZeroClass.toHasZero.{u4} S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)))) (DistribSMul.toSmulZeroClass.{u3, u4} R S (AddMonoid.toAddZeroClass.{u4} S (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u4} R S _inst_3 (AddCommMonoid.toAddMonoid.{u4} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} S _inst_4)) _inst_5)))) b (Matrix.mulVec.{u4, u1, u2} m n S _inst_4 _inst_2 M v))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u4}} {R : Type.{u3}} {S : Type.{u2}} [_inst_2 : Fintype.{u4} n] [_inst_3 : Monoid.{u3} R] [_inst_4 : NonUnitalNonAssocSemiring.{u2} S] [_inst_5 : DistribMulAction.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))] [_inst_6 : SMulCommClass.{u3, u2, u2} R S S (SMulZeroClass.toSMul.{u3, u2} R S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} R S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4)) _inst_5))) (SMulZeroClass.toSMul.{u2, u2} S S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (SMulWithZero.toSMulZeroClass.{u2, u2} S S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (MulZeroClass.toSMulWithZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4))))] (M : Matrix.{u1, u4, u2} m n S) (b : R) (v : n -> S), Eq.{max (succ u1) (succ u2)} (m -> S) (Matrix.mulVec.{u2, u1, u4} m n S _inst_4 _inst_2 M (HSMul.hSMul.{u3, max u4 u2, max u4 u2} R (n -> S) (n -> S) (instHSMul.{u3, max u4 u2} R (n -> S) (Pi.instSMul.{u4, u2, u3} n R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.18442 : n) => S) (fun (i : n) => SMulZeroClass.toSMul.{u3, u2} R S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} R S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4)) _inst_5))))) b v)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} R (m -> S) (m -> S) (instHSMul.{u3, max u1 u2} R (m -> S) (Pi.instSMul.{u1, u2, u3} m R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17554 : m) => S) (fun (i : m) => SMulZeroClass.toSMul.{u3, u2} R S (MulZeroClass.toZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S _inst_4)) (DistribSMul.toSMulZeroClass.{u3, u2} R S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4))) (DistribMulAction.toDistribSMul.{u3, u2} R S _inst_3 (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S _inst_4)) _inst_5))))) b (Matrix.mulVec.{u2, u1, u4} m n S _inst_4 _inst_2 M v))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_smul Matrix.mulVec_smulₓ'. -/
theorem mulVec_smul [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring S] [DistribMulAction R S]
    [SMulCommClass R S S] (M : Matrix m n S) (b : R) (v : n → S) :
    M.mulVec (b • v) = b • M.mulVec v := by
  ext i
  simp only [mul_vec, dot_product, Finset.smul_sum, Pi.smul_apply, mul_smul_comm]
#align matrix.mul_vec_smul Matrix.mulVec_smul

/- warning: matrix.mul_vec_single -> Matrix.mulVec_single is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : NonUnitalNonAssocSemiring.{u3} R] (M : Matrix.{u1, u2, u3} m n R) (j : n) (x : R), Eq.{max (succ u1) (succ u3)} (m -> R) (Matrix.mulVec.{u3, u1, u2} m n R _inst_4 _inst_2 M (Pi.single.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toHasZero.{u3} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R _inst_4)) j x)) (fun (i : m) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R _inst_4))) (M i j) x)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : Fintype.{u3} n] [_inst_3 : DecidableEq.{succ u3} n] [_inst_4 : NonUnitalNonAssocSemiring.{u2} R] (M : Matrix.{u1, u3, u2} m n R) (j : n) (x : R), Eq.{max (succ u1) (succ u2)} (m -> R) (Matrix.mulVec.{u2, u1, u3} m n R _inst_4 _inst_2 M (Pi.single.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_4)) j x)) (fun (i : m) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_4)) (M i j) x)
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_single Matrix.mulVec_singleₓ'. -/
@[simp]
theorem mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (j : n) (x : R) : M.mulVec (Pi.single j x) = fun i => M i j * x :=
  funext fun i => dotProduct_single _ _ _
#align matrix.mul_vec_single Matrix.mulVec_single

/- warning: matrix.single_vec_mul -> Matrix.single_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] [_inst_4 : NonUnitalNonAssocSemiring.{u3} R] (M : Matrix.{u1, u2, u3} m n R) (i : m) (x : R), Eq.{max (succ u2) (succ u3)} (n -> R) (Matrix.vecMul.{u3, u1, u2} m n R _inst_4 _inst_2 (Pi.single.{u1, u3} m (fun (i : m) => R) (fun (a : m) (b : m) => _inst_3 a b) (fun (i : m) => MulZeroClass.toHasZero.{u3} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R _inst_4)) i x) M) (fun (j : n) => HMul.hMul.{u3, u3, u3} R R R (instHMul.{u3} R (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R _inst_4))) x (M i j))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u3} m] [_inst_3 : DecidableEq.{succ u3} m] [_inst_4 : NonUnitalNonAssocSemiring.{u2} R] (M : Matrix.{u3, u1, u2} m n R) (i : m) (x : R), Eq.{max (succ u1) (succ u2)} (n -> R) (Matrix.vecMul.{u2, u3, u1} m n R _inst_4 _inst_2 (Pi.single.{u3, u2} m (fun (i : m) => R) (fun (a : m) (b : m) => _inst_3 a b) (fun (i : m) => MulZeroClass.toZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_4)) i x) M) (fun (j : n) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_4)) x (M i j))
Case conversion may be inaccurate. Consider using '#align matrix.single_vec_mul Matrix.single_vecMulₓ'. -/
@[simp]
theorem single_vecMul [Fintype m] [DecidableEq m] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (i : m) (x : R) : vecMul (Pi.single i x) M = fun j => x * M i j :=
  funext fun i => single_dotProduct _ _ _
#align matrix.single_vec_mul Matrix.single_vecMul

/- warning: matrix.diagonal_mul_vec_single -> Matrix.diagonal_mulVec_single is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : NonUnitalNonAssocSemiring.{u2} R] (v : n -> R) (j : n) (x : R), Eq.{max (succ u1) (succ u2)} (n -> R) (Matrix.mulVec.{u2, u1, u1} n n R _inst_4 _inst_2 (Matrix.diagonal.{u2, u1} n R (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_4)) v) (Pi.single.{u1, u2} n (fun (ᾰ : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_4)) j x)) (Pi.single.{u1, u2} n (fun (ᾰ : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_4)) j (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_4))) (v j) x))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : NonUnitalNonAssocSemiring.{u1} R] (v : n -> R) (j : n) (x : R), Eq.{max (succ u2) (succ u1)} (n -> R) (Matrix.mulVec.{u1, u2, u2} n n R _inst_4 _inst_2 (Matrix.diagonal.{u1, u2} n R (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_4)) v) (Pi.single.{u2, u1} n (fun (ᾰ : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_4)) j x)) (Pi.single.{u2, u1} n (fun (ᾰ : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_4)) j (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_4)) (v j) x))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_mul_vec_single Matrix.diagonal_mulVec_singleₓ'. -/
@[simp]
theorem diagonal_mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : (diagonal v).mulVec (Pi.single j x) = Pi.single j (v j * x) :=
  by
  ext i
  rw [mul_vec_diagonal]
  exact Pi.apply_single (fun i x => v i * x) (fun i => MulZeroClass.mul_zero _) j x i
#align matrix.diagonal_mul_vec_single Matrix.diagonal_mulVec_single

/- warning: matrix.single_vec_mul_diagonal -> Matrix.single_vecMul_diagonal is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : Fintype.{u1} n] [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : NonUnitalNonAssocSemiring.{u2} R] (v : n -> R) (j : n) (x : R), Eq.{max (succ u1) (succ u2)} (n -> R) (Matrix.vecMul.{u2, u1, u1} n n R _inst_4 _inst_2 (Pi.single.{u1, u2} n (fun (j : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_4)) j x) (Matrix.diagonal.{u2, u1} n R (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_4)) v)) (Pi.single.{u1, u2} n (fun (ᾰ : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_4)) j (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_4))) x (v j)))
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : Fintype.{u2} n] [_inst_3 : DecidableEq.{succ u2} n] [_inst_4 : NonUnitalNonAssocSemiring.{u1} R] (v : n -> R) (j : n) (x : R), Eq.{max (succ u2) (succ u1)} (n -> R) (Matrix.vecMul.{u1, u2, u2} n n R _inst_4 _inst_2 (Pi.single.{u2, u1} n (fun (j : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_4)) j x) (Matrix.diagonal.{u1, u2} n R (fun (a : n) (b : n) => _inst_3 a b) (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_4)) v)) (Pi.single.{u2, u1} n (fun (ᾰ : n) => R) (fun (a : n) (b : n) => _inst_3 a b) (fun (i : n) => MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_4)) j (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_4)) x (v j)))
Case conversion may be inaccurate. Consider using '#align matrix.single_vec_mul_diagonal Matrix.single_vecMul_diagonalₓ'. -/
@[simp]
theorem single_vecMul_diagonal [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n → R)
    (j : n) (x : R) : vecMul (Pi.single j x) (diagonal v) = Pi.single j (x * v j) :=
  by
  ext i
  rw [vec_mul_diagonal]
  exact Pi.apply_single (fun i x => x * v i) (fun i => MulZeroClass.zero_mul _) j x i
#align matrix.single_vec_mul_diagonal Matrix.single_vecMul_diagonal

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α]

/- warning: matrix.vec_mul_vec_mul -> Matrix.vecMul_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : Fintype.{u2} m] (v : m -> α) (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u3, u4, u1} n o α), Eq.{max (succ u4) (succ u1)} (o -> α) (Matrix.vecMul.{u1, u3, u4} n o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_3 v M) N) (Matrix.vecMul.{u1, u2, u4} m o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_3 v (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) M N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalSemiring.{u4} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : Fintype.{u2} m] (v : m -> α) (M : Matrix.{u2, u3, u4} m n α) (N : Matrix.{u3, u1, u4} n o α), Eq.{max (succ u4) (succ u1)} (o -> α) (Matrix.vecMul.{u4, u3, u1} n o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) _inst_2 (Matrix.vecMul.{u4, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) _inst_3 v M) N) (Matrix.vecMul.{u4, u2, u1} m o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) _inst_3 v (Matrix.mul.{u4, u2, u3, u1} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M N))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_vec_mul Matrix.vecMul_vecMulₓ'. -/
@[simp]
theorem vecMul_vecMul [Fintype n] [Fintype m] (v : m → α) (M : Matrix m n α) (N : Matrix n o α) :
    vecMul (vecMul v M) N = vecMul v (M ⬝ N) := by
  ext
  apply dot_product_assoc
#align matrix.vec_mul_vec_mul Matrix.vecMul_vecMul

/- warning: matrix.mul_vec_mul_vec -> Matrix.mulVec_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : Fintype.{u4} o] (v : o -> α) (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u3, u4, u1} n o α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 M (Matrix.mulVec.{u1, u3, u4} n o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_3 N v)) (Matrix.mulVec.{u1, u2, u4} m o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_3 (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) M N) v)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u3}} {o : Type.{u2}} {α : Type.{u4}} [_inst_1 : NonUnitalSemiring.{u4} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : Fintype.{u2} o] (v : o -> α) (M : Matrix.{u1, u3, u4} m n α) (N : Matrix.{u3, u2, u4} n o α), Eq.{max (succ u4) (succ u1)} (m -> α) (Matrix.mulVec.{u4, u1, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) _inst_2 M (Matrix.mulVec.{u4, u3, u2} n o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) _inst_3 N v)) (Matrix.mulVec.{u4, u1, u2} m o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1) _inst_3 (Matrix.mul.{u4, u1, u3, u2} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_1)) M N) v)
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_mul_vec Matrix.mulVec_mulVecₓ'. -/
@[simp]
theorem mulVec_mulVec [Fintype n] [Fintype o] (v : o → α) (M : Matrix m n α) (N : Matrix n o α) :
    mulVec M (mulVec N v) = mulVec (M ⬝ N) v := by
  ext
  symm
  apply dot_product_assoc
#align matrix.mul_vec_mul_vec Matrix.mulVec_mulVec

/- warning: matrix.star_mul_vec -> Matrix.star_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : StarRing.{u1} α _inst_1] (M : Matrix.{u2, u3, u1} m n α) (v : n -> α), Eq.{succ (max u2 u1)} (m -> α) (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3)))) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 M v)) (Matrix.vecMul.{u1, u3, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 (Star.star.{max u3 u1} (n -> α) (Pi.hasStar.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3)))) v) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3))) M))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : StarRing.{u3} α _inst_1] (M : Matrix.{u1, u2, u3} m n α) (v : n -> α), Eq.{max (succ u3) (succ u1)} (m -> α) (Star.star.{max u3 u1} (m -> α) (Pi.instStarForAll.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3)))) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 M v)) (Matrix.vecMul.{u3, u2, u1} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 (Star.star.{max u2 u3} (n -> α) (Pi.instStarForAll.{u2, u3} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3)))) v) (Matrix.conjTranspose.{u3, u1, u2} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3))) M))
Case conversion may be inaccurate. Consider using '#align matrix.star_mul_vec Matrix.star_mulVecₓ'. -/
theorem star_mulVec [Fintype n] [StarRing α] (M : Matrix m n α) (v : n → α) :
    star (M.mulVec v) = vecMul (star v) Mᴴ :=
  funext fun i => (star_dotProduct_star _ _).symm
#align matrix.star_mul_vec Matrix.star_mulVec

/- warning: matrix.star_vec_mul -> Matrix.star_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : StarRing.{u1} α _inst_1] (M : Matrix.{u2, u3, u1} m n α) (v : m -> α), Eq.{succ (max u3 u1)} (n -> α) (Star.star.{max u3 u1} (n -> α) (Pi.hasStar.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3)))) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 v M)) (Matrix.mulVec.{u1, u3, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3))) M) (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3)))) v))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : StarRing.{u3} α _inst_1] (M : Matrix.{u2, u1, u3} m n α) (v : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Star.star.{max u1 u3} (n -> α) (Pi.instStarForAll.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3)))) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 v M)) (Matrix.mulVec.{u3, u1, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3))) M) (Star.star.{max u3 u2} (m -> α) (Pi.instStarForAll.{u2, u3} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3)))) v))
Case conversion may be inaccurate. Consider using '#align matrix.star_vec_mul Matrix.star_vecMulₓ'. -/
theorem star_vecMul [Fintype m] [StarRing α] (M : Matrix m n α) (v : m → α) :
    star (M.vecMul v) = Mᴴ.mulVec (star v) :=
  funext fun i => (star_dotProduct_star _ _).symm
#align matrix.star_vec_mul Matrix.star_vecMul

/- warning: matrix.mul_vec_conj_transpose -> Matrix.mulVec_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : StarRing.{u1} α _inst_1] (A : Matrix.{u2, u3, u1} m n α) (x : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.mulVec.{u1, u3, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3))) A) x) (Star.star.{max u3 u1} (n -> α) (Pi.hasStar.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3)))) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3)))) x) A))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : StarRing.{u3} α _inst_1] (A : Matrix.{u2, u1, u3} m n α) (x : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.mulVec.{u3, u1, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3))) A) x) (Star.star.{max u1 u3} (n -> α) (Pi.instStarForAll.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3)))) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 (Star.star.{max u2 u3} (m -> α) (Pi.instStarForAll.{u2, u3} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3)))) x) A))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_conj_transpose Matrix.mulVec_conjTransposeₓ'. -/
theorem mulVec_conjTranspose [Fintype m] [StarRing α] (A : Matrix m n α) (x : m → α) :
    mulVec Aᴴ x = star (vecMul (star x) A) :=
  funext fun i => star_dotProduct _ _
#align matrix.mul_vec_conj_transpose Matrix.mulVec_conjTranspose

/- warning: matrix.vec_mul_conj_transpose -> Matrix.vecMul_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : StarRing.{u1} α _inst_1] (A : Matrix.{u2, u3, u1} m n α) (x : n -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.vecMul.{u1, u3, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 x (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3))) A)) (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3)))) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 A (Star.star.{max u3 u1} (n -> α) (Pi.hasStar.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (StarRing.toStarAddMonoid.{u1} α _inst_1 _inst_3)))) x)))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] [_inst_3 : StarRing.{u3} α _inst_1] (A : Matrix.{u1, u2, u3} m n α) (x : n -> α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.vecMul.{u3, u2, u1} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 x (Matrix.conjTranspose.{u3, u1, u2} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3))) A)) (Star.star.{max u1 u3} (m -> α) (Pi.instStarForAll.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3)))) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 A (Star.star.{max u3 u2} (n -> α) (Pi.instStarForAll.{u2, u3} n (fun (ᾰ : n) => α) (fun (i : n) => InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α _inst_1))) (StarRing.toStarAddMonoid.{u3} α _inst_1 _inst_3)))) x)))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_conj_transpose Matrix.vecMul_conjTransposeₓ'. -/
theorem vecMul_conjTranspose [Fintype n] [StarRing α] (A : Matrix m n α) (x : n → α) :
    vecMul x Aᴴ = star (mulVec A (star x)) :=
  funext fun i => dotProduct_star _ _
#align matrix.vec_mul_conj_transpose Matrix.vecMul_conjTranspose

/- warning: matrix.mul_mul_apply -> Matrix.mul_mul_apply is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : NonUnitalSemiring.{u1} α] [_inst_2 : Fintype.{u2} n] (A : Matrix.{u2, u2, u1} n n α) (B : Matrix.{u2, u2, u1} n n α) (C : Matrix.{u2, u2, u1} n n α) (i : n) (j : n), Eq.{succ u1} α (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) A B) C i j) (Matrix.dotProduct.{u1, u2} n α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (A i) (Matrix.mulVec.{u1, u2, u2} n n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 B (Matrix.transpose.{u1, u2, u2} n n α C j)))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalSemiring.{u2} α] [_inst_2 : Fintype.{u1} n] (A : Matrix.{u1, u1, u2} n n α) (B : Matrix.{u1, u1, u2} n n α) (C : Matrix.{u1, u1, u2} n n α) (i : n) (j : n), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1)) (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1)) A B) C i j) (Matrix.dotProduct.{u2, u1} n α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1)) (A i) (Matrix.mulVec.{u2, u1, u1} n n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_1) _inst_2 B (Matrix.transpose.{u2, u1, u1} n n α C j)))
Case conversion may be inaccurate. Consider using '#align matrix.mul_mul_apply Matrix.mul_mul_applyₓ'. -/
theorem mul_mul_apply [Fintype n] (A B C : Matrix n n α) (i j : n) :
    (A ⬝ B ⬝ C) i j = A i ⬝ᵥ B.mulVec (Cᵀ j) :=
  by
  rw [Matrix.mul_assoc]
  simpa only [mul_apply, dot_product, mul_vec]
#align matrix.mul_mul_apply Matrix.mul_mul_apply

end NonUnitalSemiring

section NonAssocSemiring

variable [Fintype m] [DecidableEq m] [NonAssocSemiring α]

/- warning: matrix.one_mul_vec -> Matrix.one_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : NonAssocSemiring.{u1} α] (v : m -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u2} m m α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3) _inst_1 (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasOne.{u1, u2} m α (fun (a : m) (b : m) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_3))))))) v) v
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : NonAssocSemiring.{u2} α] (v : m -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u2, u1, u1} m m α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3) _inst_1 (OfNat.ofNat.{max u1 u2} (Matrix.{u1, u1, u2} m m α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.one.{u2, u1} m α (fun (a : m) (b : m) => _inst_2 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3)))) v) v
Case conversion may be inaccurate. Consider using '#align matrix.one_mul_vec Matrix.one_mulVecₓ'. -/
@[simp]
theorem one_mulVec (v : m → α) : mulVec 1 v = v :=
  by
  ext
  rw [← diagonal_one, mul_vec_diagonal, one_mul]
#align matrix.one_mul_vec Matrix.one_mulVec

/- warning: matrix.vec_mul_one -> Matrix.vecMul_one is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : NonAssocSemiring.{u1} α] (v : m -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.vecMul.{u1, u2, u2} m m α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3) _inst_1 v (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} m m α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasOne.{u1, u2} m α (fun (a : m) (b : m) => _inst_2 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_3)))))))) v
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : DecidableEq.{succ u1} m] [_inst_3 : NonAssocSemiring.{u2} α] (v : m -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.vecMul.{u2, u1, u1} m m α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3) _inst_1 v (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} m m α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.one.{u2, u1} m α (fun (a : m) (b : m) => _inst_2 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3))))) v
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_one Matrix.vecMul_oneₓ'. -/
@[simp]
theorem vecMul_one (v : m → α) : vecMul v 1 = v :=
  by
  ext
  rw [← diagonal_one, vec_mul_diagonal, mul_one]
#align matrix.vec_mul_one Matrix.vecMul_one

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/- warning: matrix.neg_vec_mul -> Matrix.neg_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u2} m] (v : m -> α) (A : Matrix.{u2, u3, u1} m n α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 (Neg.neg.{max u2 u1} (m -> α) (Pi.instNeg.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) v) A) (Neg.neg.{max u3 u1} (n -> α) (Pi.instNeg.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 v A))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocRing.{u3} α] [_inst_2 : Fintype.{u2} m] (v : m -> α) (A : Matrix.{u2, u1, u3} m n α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 (Neg.neg.{max u3 u2} (m -> α) (Pi.instNeg.{u2, u3} m (fun (ᾰ : m) => α) (fun (i : m) => NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1))))))) v) A) (Neg.neg.{max u3 u1} (n -> α) (Pi.instNeg.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1))))))) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 v A))
Case conversion may be inaccurate. Consider using '#align matrix.neg_vec_mul Matrix.neg_vecMulₓ'. -/
theorem neg_vecMul [Fintype m] (v : m → α) (A : Matrix m n α) : vecMul (-v) A = -vecMul v A :=
  by
  ext
  apply neg_dot_product
#align matrix.neg_vec_mul Matrix.neg_vecMul

/- warning: matrix.vec_mul_neg -> Matrix.vecMul_neg is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u2} m] (v : m -> α) (A : Matrix.{u2, u3, u1} m n α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 v (Neg.neg.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasNeg.{u1, u2, u3} m n α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) A)) (Neg.neg.{max u3 u1} (n -> α) (Pi.instNeg.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 v A))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocRing.{u3} α] [_inst_2 : Fintype.{u2} m] (v : m -> α) (A : Matrix.{u2, u1, u3} m n α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 v (Neg.neg.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.neg.{u3, u2, u1} m n α (NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1))))))) A)) (Neg.neg.{max u3 u1} (n -> α) (Pi.instNeg.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1))))))) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 v A))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_neg Matrix.vecMul_negₓ'. -/
theorem vecMul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : vecMul v (-A) = -vecMul v A :=
  by
  ext
  apply dot_product_neg
#align matrix.vec_mul_neg Matrix.vecMul_neg

/- warning: matrix.neg_mul_vec -> Matrix.neg_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u3} n] (v : n -> α) (A : Matrix.{u2, u3, u1} m n α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 (Neg.neg.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasNeg.{u1, u2, u3} m n α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) A) v) (Neg.neg.{max u2 u1} (m -> α) (Pi.instNeg.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 A v))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocRing.{u3} α] [_inst_2 : Fintype.{u2} n] (v : n -> α) (A : Matrix.{u1, u2, u3} m n α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 (Neg.neg.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.neg.{u3, u1, u2} m n α (NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1))))))) A) v) (Neg.neg.{max u3 u1} (m -> α) (Pi.instNeg.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1))))))) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 A v))
Case conversion may be inaccurate. Consider using '#align matrix.neg_mul_vec Matrix.neg_mulVecₓ'. -/
theorem neg_mulVec [Fintype n] (v : n → α) (A : Matrix m n α) : mulVec (-A) v = -mulVec A v :=
  by
  ext
  apply neg_dot_product
#align matrix.neg_mul_vec Matrix.neg_mulVec

/- warning: matrix.mul_vec_neg -> Matrix.mulVec_neg is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u3} n] (v : n -> α) (A : Matrix.{u2, u3, u1} m n α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 A (Neg.neg.{max u3 u1} (n -> α) (Pi.instNeg.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) v)) (Neg.neg.{max u2 u1} (m -> α) (Pi.instNeg.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 A v))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocRing.{u3} α] [_inst_2 : Fintype.{u2} n] (v : n -> α) (A : Matrix.{u1, u2, u3} m n α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 A (Neg.neg.{max u3 u2} (n -> α) (Pi.instNeg.{u2, u3} n (fun (ᾰ : n) => α) (fun (i : n) => NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1))))))) v)) (Neg.neg.{max u3 u1} (m -> α) (Pi.instNeg.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1))))))) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 A v))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_neg Matrix.mulVec_negₓ'. -/
theorem mulVec_neg [Fintype n] (v : n → α) (A : Matrix m n α) : mulVec A (-v) = -mulVec A v :=
  by
  ext
  apply dot_product_neg
#align matrix.mul_vec_neg Matrix.mulVec_neg

/- warning: matrix.sub_mul_vec -> Matrix.sub_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u3} n] (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) (x : n -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 (HSub.hSub.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHSub.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasSub.{u1, u2, u3} m n α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)))))) A B) x) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHSub.{max u2 u1} (m -> α) (Pi.instSub.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)))))) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 A x) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 B x))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocRing.{u3} α] [_inst_2 : Fintype.{u2} n] (A : Matrix.{u1, u2, u3} m n α) (B : Matrix.{u1, u2, u3} m n α) (x : n -> α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 (HSub.hSub.{max (max u3 u1) u2, max (max u3 u1) u2, max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (Matrix.{u1, u2, u3} m n α) (instHSub.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.sub.{u3, u1, u2} m n α (SubNegMonoid.toSub.{u3} α (AddGroup.toSubNegMonoid.{u3} α (AddCommGroup.toAddGroup.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1)))))) A B) x) (HSub.hSub.{max u3 u1, max u3 u1, max u3 u1} (m -> α) (m -> α) (m -> α) (instHSub.{max u3 u1} (m -> α) (Pi.instSub.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => SubNegMonoid.toSub.{u3} α (AddGroup.toSubNegMonoid.{u3} α (AddCommGroup.toAddGroup.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1)))))) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 A x) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 B x))
Case conversion may be inaccurate. Consider using '#align matrix.sub_mul_vec Matrix.sub_mulVecₓ'. -/
theorem sub_mulVec [Fintype n] (A B : Matrix m n α) (x : n → α) :
    mulVec (A - B) x = mulVec A x - mulVec B x := by simp [sub_eq_add_neg, add_mul_vec, neg_mul_vec]
#align matrix.sub_mul_vec Matrix.sub_mulVec

/- warning: matrix.vec_mul_sub -> Matrix.vecMul_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u3, u1} m n α) (x : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 x (HSub.hSub.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHSub.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasSub.{u1, u2, u3} m n α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)))))) A B)) (HSub.hSub.{max u3 u1, max u3 u1, max u3 u1} (n -> α) (n -> α) (n -> α) (instHSub.{max u3 u1} (n -> α) (Pi.instSub.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1)))))) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 x A) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1) _inst_2 x B))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalNonAssocRing.{u3} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u1, u3} m n α) (B : Matrix.{u2, u1, u3} m n α) (x : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 x (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSub.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.sub.{u3, u2, u1} m n α (SubNegMonoid.toSub.{u3} α (AddGroup.toSubNegMonoid.{u3} α (AddCommGroup.toAddGroup.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1)))))) A B)) (HSub.hSub.{max u3 u1, max u3 u1, max u3 u1} (n -> α) (n -> α) (n -> α) (instHSub.{max u3 u1} (n -> α) (Pi.instSub.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => SubNegMonoid.toSub.{u3} α (AddGroup.toSubNegMonoid.{u3} α (AddCommGroup.toAddGroup.{u3} α (NonUnitalNonAssocRing.toAddCommGroup.{u3} α _inst_1)))))) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 x A) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α _inst_1) _inst_2 x B))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_sub Matrix.vecMul_subₓ'. -/
theorem vecMul_sub [Fintype m] (A B : Matrix m n α) (x : m → α) :
    vecMul x (A - B) = vecMul x A - vecMul x B := by simp [sub_eq_add_neg, vec_mul_add, vec_mul_neg]
#align matrix.vec_mul_sub Matrix.vecMul_sub

end NonUnitalNonAssocRing

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

/- warning: matrix.mul_vec_transpose -> Matrix.mulVec_transpose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalCommSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u3, u1} m n α) (x : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.mulVec.{u1, u3, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_2 (Matrix.transpose.{u1, u2, u3} m n α A) x) (Matrix.vecMul.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_2 x A)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : NonUnitalCommSemiring.{u3} α] [_inst_2 : Fintype.{u2} m] (A : Matrix.{u2, u1, u3} m n α) (x : m -> α), Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.mulVec.{u3, u1, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u3} α _inst_1)) _inst_2 (Matrix.transpose.{u3, u2, u1} m n α A) x) (Matrix.vecMul.{u3, u2, u1} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u3} α _inst_1)) _inst_2 x A)
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_transpose Matrix.mulVec_transposeₓ'. -/
theorem mulVec_transpose [Fintype m] (A : Matrix m n α) (x : m → α) : mulVec Aᵀ x = vecMul x A :=
  by
  ext
  apply dot_product_comm
#align matrix.mul_vec_transpose Matrix.mulVec_transpose

/- warning: matrix.vec_mul_transpose -> Matrix.vecMul_transpose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : NonUnitalCommSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (A : Matrix.{u2, u3, u1} m n α) (x : n -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.vecMul.{u1, u3, u2} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_2 x (Matrix.transpose.{u1, u2, u3} m n α A)) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_2 A x)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : NonUnitalCommSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] (A : Matrix.{u1, u2, u3} m n α) (x : n -> α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.vecMul.{u3, u2, u1} n m α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u3} α _inst_1)) _inst_2 x (Matrix.transpose.{u3, u1, u2} m n α A)) (Matrix.mulVec.{u3, u1, u2} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u3} α _inst_1)) _inst_2 A x)
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_transpose Matrix.vecMul_transposeₓ'. -/
theorem vecMul_transpose [Fintype n] (A : Matrix m n α) (x : n → α) : vecMul x Aᵀ = mulVec A x :=
  by
  ext
  apply dot_product_comm
#align matrix.vec_mul_transpose Matrix.vecMul_transpose

/- warning: matrix.mul_vec_vec_mul -> Matrix.mulVec_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalCommSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : Fintype.{u4} o] (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u4, u3, u1} o n α) (x : o -> α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_2 A (Matrix.vecMul.{u1, u4, u3} o n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_3 x B)) (Matrix.mulVec.{u1, u2, u4} m o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_3 (Matrix.mul.{u1, u2, u3, u4} m n o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1))) A (Matrix.transpose.{u1, u4, u3} o n α B)) x)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u3}} {o : Type.{u2}} {α : Type.{u4}} [_inst_1 : NonUnitalCommSemiring.{u4} α] [_inst_2 : Fintype.{u3} n] [_inst_3 : Fintype.{u2} o] (A : Matrix.{u1, u3, u4} m n α) (B : Matrix.{u2, u3, u4} o n α) (x : o -> α), Eq.{max (succ u4) (succ u1)} (m -> α) (Matrix.mulVec.{u4, u1, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1)) _inst_2 A (Matrix.vecMul.{u4, u2, u3} o n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1)) _inst_3 x B)) (Matrix.mulVec.{u4, u1, u2} m o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1)) _inst_3 (Matrix.mul.{u4, u1, u3, u2} m n o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1))) A (Matrix.transpose.{u4, u2, u3} o n α B)) x)
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_vec_mul Matrix.mulVec_vecMulₓ'. -/
theorem mulVec_vecMul [Fintype n] [Fintype o] (A : Matrix m n α) (B : Matrix o n α) (x : o → α) :
    mulVec A (vecMul x B) = mulVec (A ⬝ Bᵀ) x := by rw [← mul_vec_mul_vec, mul_vec_transpose]
#align matrix.mul_vec_vec_mul Matrix.mulVec_vecMul

/- warning: matrix.vec_mul_mul_vec -> Matrix.vecMul_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {o : Type.{u4}} {α : Type.{u1}} [_inst_1 : NonUnitalCommSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : Fintype.{u3} n] (A : Matrix.{u2, u3, u1} m n α) (B : Matrix.{u2, u4, u1} m o α) (x : n -> α), Eq.{max (succ u4) (succ u1)} (o -> α) (Matrix.vecMul.{u1, u2, u4} m o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_2 (Matrix.mulVec.{u1, u2, u3} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_3 A x) B) (Matrix.vecMul.{u1, u3, u4} n o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)) _inst_3 x (Matrix.mul.{u1, u3, u2, u4} n m o α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1))) (Matrix.transpose.{u1, u2, u3} m n α A) B))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} [_inst_1 : NonUnitalCommSemiring.{u4} α] [_inst_2 : Fintype.{u3} m] [_inst_3 : Fintype.{u2} n] (A : Matrix.{u3, u2, u4} m n α) (B : Matrix.{u3, u1, u4} m o α) (x : n -> α), Eq.{max (succ u4) (succ u1)} (o -> α) (Matrix.vecMul.{u4, u3, u1} m o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1)) _inst_2 (Matrix.mulVec.{u4, u3, u2} m n α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1)) _inst_3 A x) B) (Matrix.vecMul.{u4, u2, u1} n o α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1)) _inst_3 x (Matrix.mul.{u4, u2, u3, u1} n m o α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} α _inst_1))) (Matrix.transpose.{u4, u3, u2} m n α A) B))
Case conversion may be inaccurate. Consider using '#align matrix.vec_mul_mul_vec Matrix.vecMul_mulVecₓ'. -/
theorem vecMul_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (B : Matrix m o α) (x : n → α) :
    vecMul (mulVec A x) B = vecMul x (Aᵀ ⬝ B) := by rw [← vec_mul_vec_mul, vec_mul_transpose]
#align matrix.vec_mul_mul_vec Matrix.vecMul_mulVec

end NonUnitalCommSemiring

section CommSemiring

variable [CommSemiring α]

/- warning: matrix.mul_vec_smul_assoc -> Matrix.mulVec_smul_assoc is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] [_inst_2 : Fintype.{u3} n] (A : Matrix.{u2, u3, u1} m n α) (b : n -> α) (a : α), Eq.{max (succ u2) (succ u1)} (m -> α) (Matrix.mulVec.{u1, u2, u3} m n α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))) _inst_2 A (SMul.smul.{u1, max u3 u1} α (n -> α) (Function.hasSMul.{u3, u1, u1} n α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))))) a b)) (SMul.smul.{u1, max u2 u1} α (m -> α) (Function.hasSMul.{u2, u1, u1} m α α (Mul.toSMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))))) a (Matrix.mulVec.{u1, u2, u3} m n α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))) _inst_2 A b))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : CommSemiring.{u3} α] [_inst_2 : Fintype.{u2} n] (A : Matrix.{u1, u2, u3} m n α) (b : n -> α) (a : α), Eq.{max (succ u3) (succ u1)} (m -> α) (Matrix.mulVec.{u3, u1, u2} m n α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α (CommSemiring.toSemiring.{u3} α _inst_1))) _inst_2 A (HSMul.hSMul.{u3, max u3 u2, max u3 u2} α (n -> α) (n -> α) (instHSMul.{u3, max u3 u2} α (n -> α) (Pi.instSMul.{u2, u3, u3} n α (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.20169 : n) => α) (fun (i : n) => Algebra.toSMul.{u3, u3} α α _inst_1 (CommSemiring.toSemiring.{u3} α _inst_1) (Algebra.id.{u3} α _inst_1)))) a b)) (HSMul.hSMul.{u3, max u3 u1, max u3 u1} α (m -> α) (m -> α) (instHSMul.{u3, max u3 u1} α (m -> α) (Pi.instSMul.{u1, u3, u3} m α (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.17554 : m) => α) (fun (i : m) => Algebra.toSMul.{u3, u3} α α _inst_1 (CommSemiring.toSemiring.{u3} α _inst_1) (Algebra.id.{u3} α _inst_1)))) a (Matrix.mulVec.{u3, u1, u2} m n α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} α (Semiring.toNonAssocSemiring.{u3} α (CommSemiring.toSemiring.{u3} α _inst_1))) _inst_2 A b))
Case conversion may be inaccurate. Consider using '#align matrix.mul_vec_smul_assoc Matrix.mulVec_smul_assocₓ'. -/
theorem mulVec_smul_assoc [Fintype n] (A : Matrix m n α) (b : n → α) (a : α) :
    A.mulVec (a • b) = a • A.mulVec b := by
  ext
  apply dot_product_smul
#align matrix.mul_vec_smul_assoc Matrix.mulVec_smul_assoc

end CommSemiring

section Transpose

open Matrix

/- warning: matrix.transpose_transpose -> Matrix.transpose_transpose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.transpose.{u1, u3, u2} n m α (Matrix.transpose.{u1, u2, u3} m n α M)) M
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.transpose.{u3, u1, u2} n m α (Matrix.transpose.{u3, u2, u1} m n α M)) M
Case conversion may be inaccurate. Consider using '#align matrix.transpose_transpose Matrix.transpose_transposeₓ'. -/
@[simp]
theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by ext <;> rfl
#align matrix.transpose_transpose Matrix.transpose_transpose

/- warning: matrix.transpose_zero -> Matrix.transpose_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α], Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α _inst_1))))) (OfNat.ofNat.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) 0 (OfNat.mk.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) 0 (Zero.zero.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasZero.{u1, u3, u2} n m α _inst_1))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.transpose.{u3, u2, u1} m n α (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.zero.{u3, u2, u1} m n α _inst_1)))) (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.zero.{u3, u1, u2} n m α _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_zero Matrix.transpose_zeroₓ'. -/
@[simp]
theorem transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0 := by ext (i j) <;> rfl
#align matrix.transpose_zero Matrix.transpose_zero

/- warning: matrix.transpose_one -> Matrix.transpose_one is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] [_inst_3 : One.{u1} α], Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.transpose.{u1, u2, u2} n n α (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3))))) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] [_inst_3 : One.{u2} α], Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.transpose.{u2, u1, u1} n n α (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)))) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_one Matrix.transpose_oneₓ'. -/
@[simp]
theorem transpose_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α)ᵀ = 1 :=
  by
  ext (i j)
  rw [transpose_apply, ← diagonal_one]
  by_cases i = j
  · simp only [h, diagonal_apply_eq]
  · simp only [diagonal_apply_ne _ h, diagonal_apply_ne' _ h]
#align matrix.transpose_one Matrix.transpose_one

/- warning: matrix.transpose_add -> Matrix.transpose_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Add.{u1} α] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α _inst_1)) M N)) (HAdd.hAdd.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.{u3, u2, u1} n m α) (Matrix.{u3, u2, u1} n m α) (instHAdd.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasAdd.{u1, u3, u2} n m α _inst_1)) (Matrix.transpose.{u1, u2, u3} m n α M) (Matrix.transpose.{u1, u2, u3} m n α N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Add.{u3} α] (M : Matrix.{u2, u1, u3} m n α) (N : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.transpose.{u3, u2, u1} m n α (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α _inst_1)) M N)) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.add.{u3, u1, u2} n m α _inst_1)) (Matrix.transpose.{u3, u2, u1} m n α M) (Matrix.transpose.{u3, u2, u1} m n α N))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_add Matrix.transpose_addₓ'. -/
@[simp]
theorem transpose_add [Add α] (M : Matrix m n α) (N : Matrix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ :=
  by
  ext (i j)
  simp
#align matrix.transpose_add Matrix.transpose_add

/- warning: matrix.transpose_sub -> Matrix.transpose_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Sub.{u1} α] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α (HSub.hSub.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHSub.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasSub.{u1, u2, u3} m n α _inst_1)) M N)) (HSub.hSub.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.{u3, u2, u1} n m α) (Matrix.{u3, u2, u1} n m α) (instHSub.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasSub.{u1, u3, u2} n m α _inst_1)) (Matrix.transpose.{u1, u2, u3} m n α M) (Matrix.transpose.{u1, u2, u3} m n α N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Sub.{u3} α] (M : Matrix.{u2, u1, u3} m n α) (N : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.transpose.{u3, u2, u1} m n α (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSub.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.sub.{u3, u2, u1} m n α _inst_1)) M N)) (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (instHSub.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.sub.{u3, u1, u2} n m α _inst_1)) (Matrix.transpose.{u3, u2, u1} m n α M) (Matrix.transpose.{u3, u2, u1} m n α N))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_sub Matrix.transpose_subₓ'. -/
@[simp]
theorem transpose_sub [Sub α] (M : Matrix m n α) (N : Matrix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ :=
  by
  ext (i j)
  simp
#align matrix.transpose_sub Matrix.transpose_sub

/- warning: matrix.transpose_mul -> Matrix.transpose_mul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : Fintype.{u4} n] (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u4, u2, u1} n l α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} l m α) (Matrix.transpose.{u1, u3, u2} m l α (Matrix.mul.{u1, u3, u4, u2} m n l α _inst_3 (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1 M N)) (Matrix.mul.{u1, u2, u4, u3} l n m α _inst_3 (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1 (Matrix.transpose.{u1, u4, u2} n l α N) (Matrix.transpose.{u1, u3, u4} m n α M))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u4}} [_inst_1 : AddCommMonoid.{u4} α] [_inst_2 : CommSemigroup.{u4} α] [_inst_3 : Fintype.{u3} n] (M : Matrix.{u2, u3, u4} m n α) (N : Matrix.{u3, u1, u4} n l α), Eq.{max (max (succ u4) (succ u1)) (succ u2)} (Matrix.{u1, u2, u4} l m α) (Matrix.transpose.{u4, u2, u1} m l α (Matrix.mul.{u4, u2, u3, u1} m n l α _inst_3 (Semigroup.toMul.{u4} α (CommSemigroup.toSemigroup.{u4} α _inst_2)) _inst_1 M N)) (Matrix.mul.{u4, u1, u3, u2} l n m α _inst_3 (Semigroup.toMul.{u4} α (CommSemigroup.toSemigroup.{u4} α _inst_2)) _inst_1 (Matrix.transpose.{u4, u3, u1} n l α N) (Matrix.transpose.{u4, u2, u3} m n α M))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_mul Matrix.transpose_mulₓ'. -/
@[simp]
theorem transpose_mul [AddCommMonoid α] [CommSemigroup α] [Fintype n] (M : Matrix m n α)
    (N : Matrix n l α) : (M ⬝ N)ᵀ = Nᵀ ⬝ Mᵀ :=
  by
  ext (i j)
  apply dot_product_comm
#align matrix.transpose_mul Matrix.transpose_mul

/- warning: matrix.transpose_smul -> Matrix.transpose_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {R : Type.{u4}} [_inst_1 : SMul.{u4, u1} R α] (c : R) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α _inst_1) c M)) (SMul.smul.{u4, max u3 u2 u1} R (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u4} n m R α _inst_1) c (Matrix.transpose.{u1, u2, u3} m n α M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u4}} {R : Type.{u3}} [_inst_1 : SMul.{u3, u4} R α] (c : R) (M : Matrix.{u2, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.transpose.{u4, u2, u1} m n α (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_1)) c M)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.{u1, u2, u4} n m α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.smul.{u4, u1, u2, u3} n m R α _inst_1)) c (Matrix.transpose.{u4, u2, u1} m n α M))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_smul Matrix.transpose_smulₓ'. -/
@[simp]
theorem transpose_smul {R : Type _} [SMul R α] (c : R) (M : Matrix m n α) : (c • M)ᵀ = c • Mᵀ :=
  by
  ext (i j)
  rfl
#align matrix.transpose_smul Matrix.transpose_smul

/- warning: matrix.transpose_neg -> Matrix.transpose_neg is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Neg.{u1} α] (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α (Neg.neg.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasNeg.{u1, u2, u3} m n α _inst_1) M)) (Neg.neg.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasNeg.{u1, u3, u2} n m α _inst_1) (Matrix.transpose.{u1, u2, u3} m n α M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Neg.{u3} α] (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.transpose.{u3, u2, u1} m n α (Neg.neg.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.neg.{u3, u2, u1} m n α _inst_1) M)) (Neg.neg.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.neg.{u3, u1, u2} n m α _inst_1) (Matrix.transpose.{u3, u2, u1} m n α M))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_neg Matrix.transpose_negₓ'. -/
@[simp]
theorem transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ = -Mᵀ := by ext (i j) <;> rfl
#align matrix.transpose_neg Matrix.transpose_neg

/- warning: matrix.transpose_map -> Matrix.transpose_map is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {M : Matrix.{u3, u4, u1} m n α}, Eq.{succ (max u4 u3 u2)} (Matrix.{u4, u3, u2} n m β) (Matrix.map.{u1, u2, u4, u3} n m α β (Matrix.transpose.{u1, u3, u4} m n α M) f) (Matrix.transpose.{u2, u3, u4} m n β (Matrix.map.{u1, u2, u3, u4} m n α β M f))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} {f : α -> β} {M : Matrix.{u2, u1, u3} m n α}, Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m β) (Matrix.map.{u3, u4, u1, u2} n m α β (Matrix.transpose.{u3, u2, u1} m n α M) f) (Matrix.transpose.{u4, u2, u1} m n β (Matrix.map.{u3, u4, u2, u1} m n α β M f))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_map Matrix.transpose_mapₓ'. -/
theorem transpose_map {f : α → β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ :=
  by
  ext
  rfl
#align matrix.transpose_map Matrix.transpose_map

variable (m n α)

#print Matrix.transposeAddEquiv /-
/-- `matrix.transpose` as an `add_equiv` -/
@[simps apply]
def transposeAddEquiv [Add α] : Matrix m n α ≃+ Matrix n m α
    where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  map_add' := transpose_add
#align matrix.transpose_add_equiv Matrix.transposeAddEquiv
-/

/- warning: matrix.transpose_add_equiv_symm -> Matrix.transposeAddEquiv_symm is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2}) (n : Type.{u3}) (α : Type.{u1}) [_inst_1 : Add.{u1} α], Eq.{max (succ (max u3 u2 u1)) (succ (max u2 u3 u1))} (AddEquiv.{max u3 u2 u1, max u2 u3 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u3, u2} n m α _inst_1) (Matrix.hasAdd.{u1, u2, u3} m n α _inst_1)) (AddEquiv.symm.{max u2 u3 u1, max u3 u2 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (Matrix.hasAdd.{u1, u2, u3} m n α _inst_1) (Matrix.hasAdd.{u1, u3, u2} n m α _inst_1) (Matrix.transposeAddEquiv.{u1, u2, u3} m n α _inst_1)) (Matrix.transposeAddEquiv.{u1, u3, u2} n m α _inst_1)
but is expected to have type
  forall (m : Type.{u2}) (n : Type.{u1}) (α : Type.{u3}) [_inst_1 : Add.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AddEquiv.{max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u1, u2} n m α _inst_1) (Matrix.add.{u3, u2, u1} m n α _inst_1)) (AddEquiv.symm.{max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u1, u2, u3} n m α) (Matrix.add.{u3, u2, u1} m n α _inst_1) (Matrix.add.{u3, u1, u2} n m α _inst_1) (Matrix.transposeAddEquiv.{u3, u2, u1} m n α _inst_1)) (Matrix.transposeAddEquiv.{u3, u1, u2} n m α _inst_1)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_add_equiv_symm Matrix.transposeAddEquiv_symmₓ'. -/
@[simp]
theorem transposeAddEquiv_symm [Add α] : (transposeAddEquiv m n α).symm = transposeAddEquiv n m α :=
  rfl
#align matrix.transpose_add_equiv_symm Matrix.transposeAddEquiv_symm

variable {m n α}

/- warning: matrix.transpose_list_sum -> Matrix.transpose_list_sum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] (l : List.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α)), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α (List.sum.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.hasZero.{u1, u2, u3} m n α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) l)) (List.sum.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasAdd.{u1, u3, u2} n m α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.hasZero.{u1, u3, u2} n m α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (List.map.{max u2 u3 u1, max u3 u2 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α) l))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : AddMonoid.{u3} α] (l : List.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} m n α)), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} n m α) (Matrix.transpose.{u3, u1, u2} m n α (List.sum.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.add.{u3, u1, u2} m n α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1))) (Matrix.zero.{u3, u1, u2} m n α (AddMonoid.toZero.{u3} α _inst_1)) l)) (List.sum.{max (max u3 u1) u2} (Matrix.{u2, u1, u3} n m α) (Matrix.add.{u3, u2, u1} n m α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1))) (Matrix.zero.{u3, u2, u1} n m α (AddMonoid.toZero.{u3} α _inst_1)) (List.map.{max (max u2 u1) u3, max (max u2 u1) u3} (Matrix.{u1, u2, u3} m n α) (Matrix.{u2, u1, u3} n m α) (Matrix.transpose.{u3, u1, u2} m n α) l))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_list_sum Matrix.transpose_list_sumₓ'. -/
theorem transpose_list_sum [AddMonoid α] (l : List (Matrix m n α)) :
    l.Sumᵀ = (l.map transpose).Sum :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_list_sum l
#align matrix.transpose_list_sum Matrix.transpose_list_sum

/- warning: matrix.transpose_multiset_sum -> Matrix.transpose_multiset_sum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] (s : Multiset.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α)), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α (Multiset.sum.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_1) s)) (Multiset.sum.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.addCommMonoid.{u1, u3, u2} n m α _inst_1) (Multiset.map.{max u2 u3 u1, max u3 u2 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α) s))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : AddCommMonoid.{u3} α] (s : Multiset.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} m n α)), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} n m α) (Matrix.transpose.{u3, u1, u2} m n α (Multiset.sum.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.addCommMonoid.{u3, u1, u2} m n α _inst_1) s)) (Multiset.sum.{max (max u3 u1) u2} (Matrix.{u2, u1, u3} n m α) (Matrix.addCommMonoid.{u3, u2, u1} n m α _inst_1) (Multiset.map.{max (max u2 u1) u3, max (max u2 u1) u3} (Matrix.{u1, u2, u3} m n α) (Matrix.{u2, u1, u3} n m α) (Matrix.transpose.{u3, u1, u2} m n α) s))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_multiset_sum Matrix.transpose_multiset_sumₓ'. -/
theorem transpose_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix m n α)) :
    s.Sumᵀ = (s.map transpose).Sum :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s
#align matrix.transpose_multiset_sum Matrix.transpose_multiset_sum

/- warning: matrix.transpose_sum -> Matrix.transpose_sum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] {ι : Type.{u4}} (s : Finset.{u4} ι) (M : ι -> (Matrix.{u2, u3, u1} m n α)), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.transpose.{u1, u2, u3} m n α (Finset.sum.{max u2 u3 u1, u4} (Matrix.{u2, u3, u1} m n α) ι (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_1) s (fun (i : ι) => M i))) (Finset.sum.{max u3 u2 u1, u4} (Matrix.{u3, u2, u1} n m α) ι (Matrix.addCommMonoid.{u1, u3, u2} n m α _inst_1) s (fun (i : ι) => Matrix.transpose.{u1, u2, u3} m n α (M i)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u4}} [_inst_1 : AddCommMonoid.{u4} α] {ι : Type.{u3}} (s : Finset.{u3} ι) (M : ι -> (Matrix.{u2, u1, u4} m n α)), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.transpose.{u4, u2, u1} m n α (Finset.sum.{max (max u1 u2) u4, u3} (Matrix.{u2, u1, u4} m n α) ι (Matrix.addCommMonoid.{u4, u2, u1} m n α _inst_1) s (fun (i : ι) => M i))) (Finset.sum.{max (max u1 u2) u4, u3} (Matrix.{u1, u2, u4} n m α) ι (Matrix.addCommMonoid.{u4, u1, u2} n m α _inst_1) s (fun (i : ι) => Matrix.transpose.{u4, u2, u1} m n α (M i)))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_sum Matrix.transpose_sumₓ'. -/
theorem transpose_sum [AddCommMonoid α] {ι : Type _} (s : Finset ι) (M : ι → Matrix m n α) :
    (∑ i in s, M i)ᵀ = ∑ i in s, (M i)ᵀ :=
  (transposeAddEquiv m n α).toAddMonoidHom.map_sum _ s
#align matrix.transpose_sum Matrix.transpose_sum

variable (m n R α)

#print Matrix.transposeLinearEquiv /-
/-- `matrix.transpose` as a `linear_map` -/
@[simps apply]
def transposeLinearEquiv [Semiring R] [AddCommMonoid α] [Module R α] :
    Matrix m n α ≃ₗ[R] Matrix n m α :=
  { transposeAddEquiv m n α with map_smul' := transpose_smul }
#align matrix.transpose_linear_equiv Matrix.transposeLinearEquiv
-/

/- warning: matrix.transpose_linear_equiv_symm -> Matrix.transposeLinearEquiv_symm is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2}) (n : Type.{u3}) (R : Type.{u4}) (α : Type.{u1}) [_inst_1 : Semiring.{u4} R] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : Module.{u4, u1} R α _inst_1 _inst_2], Eq.{max (succ (max u3 u2 u1)) (succ (max u2 u3 u1))} (LinearEquiv.{u4, u4, max u3 u2 u1, max u2 u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (Matrix.{u3, u2, u1} n m α) (Matrix.{u2, u3, u1} m n α) (Matrix.addCommMonoid.{u1, u3, u2} n m α _inst_2) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_2) (Matrix.module.{u1, u3, u2, u4} n m R α _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_3)) (LinearEquiv.symm.{u4, u4, max u2 u3 u1, max u3 u2 u1} R R (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) _inst_1 _inst_1 (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_2) (Matrix.addCommMonoid.{u1, u3, u2} n m α _inst_2) (Matrix.module.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_3) (Matrix.module.{u1, u3, u2, u4} n m R α _inst_1 _inst_2 _inst_3) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) (RingHomInvPair.ids.{u4} R _inst_1) (RingHomInvPair.ids.{u4} R _inst_1) (Matrix.transposeLinearEquiv.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_3)) (Matrix.transposeLinearEquiv.{u1, u3, u2, u4} n m R α _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall (m : Type.{u2}) (n : Type.{u1}) (R : Type.{u3}) (α : Type.{u4}) [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} α] [_inst_3 : Module.{u3, u4} R α _inst_1 _inst_2], Eq.{max (max (succ u4) (succ u2)) (succ u1)} (LinearEquiv.{u3, u3, max (max u4 u2) u1, max (max u4 u2) u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (Matrix.{u1, u2, u4} n m α) (Matrix.{u2, u1, u4} m n α) (Matrix.addCommMonoid.{u4, u1, u2} n m α _inst_2) (Matrix.addCommMonoid.{u4, u2, u1} m n α _inst_2) (Matrix.module.{u4, u1, u2, u3} n m R α _inst_1 _inst_2 _inst_3) (Matrix.module.{u4, u2, u1, u3} m n R α _inst_1 _inst_2 _inst_3)) (LinearEquiv.symm.{u3, u3, max (max u4 u2) u1, max (max u4 u2) u1} R R (Matrix.{u2, u1, u4} m n α) (Matrix.{u1, u2, u4} n m α) _inst_1 _inst_1 (Matrix.addCommMonoid.{u4, u2, u1} m n α _inst_2) (Matrix.addCommMonoid.{u4, u1, u2} n m α _inst_2) (Matrix.module.{u4, u2, u1, u3} m n R α _inst_1 _inst_2 _inst_3) (Matrix.module.{u4, u1, u2, u3} n m R α _inst_1 _inst_2 _inst_3) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (Matrix.transposeLinearEquiv.{u4, u2, u1, u3} m n R α _inst_1 _inst_2 _inst_3)) (Matrix.transposeLinearEquiv.{u4, u1, u2, u3} n m R α _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_linear_equiv_symm Matrix.transposeLinearEquiv_symmₓ'. -/
@[simp]
theorem transposeLinearEquiv_symm [Semiring R] [AddCommMonoid α] [Module R α] :
    (transposeLinearEquiv m n R α).symm = transposeLinearEquiv n m R α :=
  rfl
#align matrix.transpose_linear_equiv_symm Matrix.transposeLinearEquiv_symm

variable {m n R α}

variable (m α)

/- warning: matrix.transpose_ring_equiv -> Matrix.transposeRingEquiv is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2}) (α : Type.{u1}) [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : Fintype.{u2} m], RingEquiv.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} m m α) (MulOpposite.{max u2 u1} (Matrix.{u2, u2, u1} m m α)) (Matrix.hasMul.{u1, u2} m α _inst_3 (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1) (Matrix.hasAdd.{u1, u2, u2} m m α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (MulOpposite.hasMul.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasMul.{u1, u2} m α _inst_3 (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1)) (MulOpposite.hasAdd.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasAdd.{u1, u2, u2} m m α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))
but is expected to have type
  forall (m : Type.{u2}) (α : Type.{u1}) [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : Fintype.{u2} m], RingEquiv.{max u1 u2, max u1 u2} (Matrix.{u2, u2, u1} m m α) (MulOpposite.{max u1 u2} (Matrix.{u2, u2, u1} m m α)) (Matrix.instMulMatrix.{u1, u2} m α _inst_3 (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1) (MulOpposite.mul.{max u1 u2} (Matrix.{u2, u2, u1} m m α) (Matrix.instMulMatrix.{u1, u2} m α _inst_3 (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1)) (Matrix.add.{u1, u2, u2} m m α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))) (MulOpposite.add.{max u1 u2} (Matrix.{u2, u2, u1} m m α) (Matrix.add.{u1, u2, u2} m m α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_ring_equiv Matrix.transposeRingEquivₓ'. -/
/-- `matrix.transpose` as a `ring_equiv` to the opposite ring -/
@[simps]
def transposeRingEquiv [AddCommMonoid α] [CommSemigroup α] [Fintype m] :
    Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ :=
  {
    (transposeAddEquiv m m α).trans
      MulOpposite.opAddEquiv with
    toFun := fun M => MulOpposite.op Mᵀ
    invFun := fun M => M.unopᵀ
    map_mul' := fun M N =>
      (congr_arg MulOpposite.op (transpose_mul M N)).trans (MulOpposite.op_mul _ _)
    left_inv := fun M => transpose_transpose M
    right_inv := fun M => MulOpposite.unop_injective <| transpose_transpose M.unop }
#align matrix.transpose_ring_equiv Matrix.transposeRingEquiv

variable {m α}

/- warning: matrix.transpose_pow -> Matrix.transpose_pow is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (M : Matrix.{u2, u2, u1} m m α) (k : Nat), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} m m α) (Matrix.transpose.{u1, u2, u2} m m α (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u2, u2, u1} m m α) Nat (Matrix.{u2, u2, u1} m m α) (instHPow.{max u2 u1, 0} (Matrix.{u2, u2, u1} m m α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.semiring.{u1, u2} m α (CommSemiring.toSemiring.{u1} α _inst_1) _inst_2 (fun (a : m) (b : m) => _inst_3 a b)))))) M k)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u2, u2, u1} m m α) Nat (Matrix.{u2, u2, u1} m m α) (instHPow.{max u2 u1, 0} (Matrix.{u2, u2, u1} m m α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.semiring.{u1, u2} m α (CommSemiring.toSemiring.{u1} α _inst_1) _inst_2 (fun (a : m) (b : m) => _inst_3 a b)))))) (Matrix.transpose.{u1, u2, u2} m m α M) k)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommSemiring.{u2} α] [_inst_2 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] (M : Matrix.{u1, u1, u2} m m α) (k : Nat), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} m m α) (Matrix.transpose.{u2, u1, u1} m m α (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u1, u1, u2} m m α) Nat (Matrix.{u1, u1, u2} m m α) (instHPow.{max u2 u1, 0} (Matrix.{u1, u1, u2} m m α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.semiring.{u2, u1} m α (CommSemiring.toSemiring.{u2} α _inst_1) _inst_2 (fun (a : m) (b : m) => _inst_3 a b)))))) M k)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u1, u1, u2} m m α) Nat (Matrix.{u1, u1, u2} m m α) (instHPow.{max u2 u1, 0} (Matrix.{u1, u1, u2} m m α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.semiring.{u2, u1} m α (CommSemiring.toSemiring.{u2} α _inst_1) _inst_2 (fun (a : m) (b : m) => _inst_3 a b)))))) (Matrix.transpose.{u2, u1, u1} m m α M) k)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_pow Matrix.transpose_powₓ'. -/
@[simp]
theorem transpose_pow [CommSemiring α] [Fintype m] [DecidableEq m] (M : Matrix m m α) (k : ℕ) :
    (M ^ k)ᵀ = Mᵀ ^ k :=
  MulOpposite.op_injective <| map_pow (transposeRingEquiv m α) M k
#align matrix.transpose_pow Matrix.transpose_pow

/- warning: matrix.transpose_list_prod -> Matrix.transpose_list_prod is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] [_inst_2 : Fintype.{u2} m] [_inst_3 : DecidableEq.{succ u2} m] (l : List.{max u2 u1} (Matrix.{u2, u2, u1} m m α)), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} m m α) (Matrix.transpose.{u1, u2, u2} m m α (List.prod.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasMul.{u1, u2} m α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (Matrix.hasOne.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) l)) (List.prod.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasMul.{u1, u2} m α _inst_2 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (Matrix.hasOne.{u1, u2} m α (fun (a : m) (b : m) => _inst_3 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (List.reverse.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (List.map.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.{u2, u2, u1} m m α) (Matrix.transpose.{u1, u2, u2} m m α) l)))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommSemiring.{u2} α] [_inst_2 : Fintype.{u1} m] [_inst_3 : DecidableEq.{succ u1} m] (l : List.{max u2 u1} (Matrix.{u1, u1, u2} m m α)), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} m m α) (Matrix.transpose.{u2, u1, u1} m m α (List.prod.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.instMulMatrix.{u2, u1} m α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1))))) (Matrix.one.{u2, u1} m α (fun (a : m) (b : m) => _inst_3 a b) (CommMonoidWithZero.toZero.{u2} α (CommSemiring.toCommMonoidWithZero.{u2} α _inst_1)) (Semiring.toOne.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1))) l)) (List.prod.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.instMulMatrix.{u2, u1} m α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1))))) (Matrix.one.{u2, u1} m α (fun (a : m) (b : m) => _inst_3 a b) (CommMonoidWithZero.toZero.{u2} α (CommSemiring.toCommMonoidWithZero.{u2} α _inst_1)) (Semiring.toOne.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1))) (List.reverse.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (List.map.{max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} m m α) (Matrix.{u1, u1, u2} m m α) (Matrix.transpose.{u2, u1, u1} m m α) l)))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_list_prod Matrix.transpose_list_prodₓ'. -/
theorem transpose_list_prod [CommSemiring α] [Fintype m] [DecidableEq m] (l : List (Matrix m m α)) :
    l.Prodᵀ = (l.map transpose).reverse.Prod :=
  (transposeRingEquiv m α).unop_map_list_prod l
#align matrix.transpose_list_prod Matrix.transpose_list_prod

variable (R m α)

/- warning: matrix.transpose_alg_equiv -> Matrix.transposeAlgEquiv is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2}) (R : Type.{u3}) (α : Type.{u1}) [_inst_1 : CommSemiring.{u3} R] [_inst_2 : CommSemiring.{u1} α] [_inst_3 : Fintype.{u2} m] [_inst_4 : DecidableEq.{succ u2} m] [_inst_5 : Algebra.{u3, u1} R α _inst_1 (CommSemiring.toSemiring.{u1} α _inst_2)], AlgEquiv.{u3, max u2 u1, max u2 u1} R (Matrix.{u2, u2, u1} m m α) (MulOpposite.{max u2 u1} (Matrix.{u2, u2, u1} m m α)) _inst_1 (Matrix.semiring.{u1, u2} m α (CommSemiring.toSemiring.{u1} α _inst_2) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (MulOpposite.semiring.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.semiring.{u1, u2} m α (CommSemiring.toSemiring.{u1} α _inst_2) _inst_3 (fun (a : m) (b : m) => _inst_4 a b))) (Matrix.algebra.{u1, u2, u3} m R α _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} α _inst_2) _inst_5) (MulOpposite.algebra.{u3, max u2 u1} R (Matrix.{u2, u2, u1} m m α) _inst_1 (Matrix.semiring.{u1, u2} m α (CommSemiring.toSemiring.{u1} α _inst_2) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.algebra.{u1, u2, u3} m R α _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} α _inst_2) _inst_5))
but is expected to have type
  forall (m : Type.{u2}) (R : Type.{u3}) (α : Type.{u1}) [_inst_1 : CommSemiring.{u3} R] [_inst_2 : CommSemiring.{u1} α] [_inst_3 : Fintype.{u2} m] [_inst_4 : DecidableEq.{succ u2} m] [_inst_5 : Algebra.{u3, u1} R α _inst_1 (CommSemiring.toSemiring.{u1} α _inst_2)], AlgEquiv.{u3, max u1 u2, max u1 u2} R (Matrix.{u2, u2, u1} m m α) (MulOpposite.{max u1 u2} (Matrix.{u2, u2, u1} m m α)) _inst_1 (Matrix.semiring.{u1, u2} m α (CommSemiring.toSemiring.{u1} α _inst_2) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (MulOpposite.semiring.{max u1 u2} (Matrix.{u2, u2, u1} m m α) (Matrix.semiring.{u1, u2} m α (CommSemiring.toSemiring.{u1} α _inst_2) _inst_3 (fun (a : m) (b : m) => _inst_4 a b))) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u3} m R α _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} α _inst_2) _inst_5) (MulOpposite.instAlgebraMulOppositeSemiring.{u3, max u1 u2} R (Matrix.{u2, u2, u1} m m α) _inst_1 (Matrix.semiring.{u1, u2} m α (CommSemiring.toSemiring.{u1} α _inst_2) _inst_3 (fun (a : m) (b : m) => _inst_4 a b)) (Matrix.instAlgebraMatrixSemiring.{u1, u2, u3} m R α _inst_3 (fun (a : m) (b : m) => _inst_4 a b) _inst_1 (CommSemiring.toSemiring.{u1} α _inst_2) _inst_5))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_alg_equiv Matrix.transposeAlgEquivₓ'. -/
/-- `matrix.transpose` as an `alg_equiv` to the opposite ring -/
@[simps]
def transposeAlgEquiv [CommSemiring R] [CommSemiring α] [Fintype m] [DecidableEq m] [Algebra R α] :
    Matrix m m α ≃ₐ[R] (Matrix m m α)ᵐᵒᵖ :=
  { (transposeAddEquiv m m α).trans MulOpposite.opAddEquiv,
    transposeRingEquiv m α with
    toFun := fun M => MulOpposite.op Mᵀ
    commutes' := fun r => by
      simp only [algebra_map_eq_diagonal, diagonal_transpose, MulOpposite.algebraMap_apply] }
#align matrix.transpose_alg_equiv Matrix.transposeAlgEquiv

variable {R m α}

end Transpose

section ConjTranspose

open Matrix

/- warning: matrix.conj_transpose_apply -> Matrix.conjTranspose_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Star.{u1} α] (M : Matrix.{u2, u3, u1} m n α) (i : m) (j : n), Eq.{succ u1} α (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_1 M j i) (Star.star.{u1} α _inst_1 (M i j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Star.{u3} α] (M : Matrix.{u2, u1, u3} m n α) (i : m) (j : n), Eq.{succ u3} α (Matrix.conjTranspose.{u3, u2, u1} m n α _inst_1 M j i) (Star.star.{u3} α _inst_1 (M i j))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_apply Matrix.conjTranspose_applyₓ'. -/
/-- Tell `simp` what the entries are in a conjugate transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp]
theorem conjTranspose_apply [Star α] (M : Matrix m n α) (i j) :
    M.conjTranspose j i = star (M i j) :=
  rfl
#align matrix.conj_transpose_apply Matrix.conjTranspose_apply

/- warning: matrix.conj_transpose_conj_transpose -> Matrix.conjTranspose_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : InvolutiveStar.{u1} α] (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.conjTranspose.{u1, u3, u2} n m α (InvolutiveStar.toHasStar.{u1} α _inst_1) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α _inst_1) M)) M
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : InvolutiveStar.{u3} α] (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.conjTranspose.{u3, u1, u2} n m α (InvolutiveStar.toStar.{u3} α _inst_1) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α _inst_1) M)) M
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_conj_transpose Matrix.conjTranspose_conjTransposeₓ'. -/
@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar α] (M : Matrix m n α) : Mᴴᴴ = M :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_conj_transpose Matrix.conjTranspose_conjTranspose

/- warning: matrix.conj_transpose_zero -> Matrix.conjTranspose_zero is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1], Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) (OfNat.ofNat.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (OfNat.mk.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) 0 (Zero.zero.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasZero.{u1, u2, u3} m n α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))))))) (OfNat.ofNat.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) 0 (OfNat.mk.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) 0 (Zero.zero.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasZero.{u1, u3, u2} n m α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddMonoid.{u3} α] [_inst_2 : StarAddMonoid.{u3} α _inst_1], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α _inst_1 _inst_2)) (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.zero.{u3, u2, u1} m n α (AddMonoid.toZero.{u3} α _inst_1))))) (OfNat.ofNat.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) 0 (Zero.toOfNat0.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.zero.{u3, u1, u2} n m α (AddMonoid.toZero.{u3} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_zero Matrix.conjTranspose_zeroₓ'. -/
@[simp]
theorem conjTranspose_zero [AddMonoid α] [StarAddMonoid α] : (0 : Matrix m n α)ᴴ = 0 :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_zero Matrix.conjTranspose_zero

/- warning: matrix.conj_transpose_one -> Matrix.conjTranspose_one is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Semiring.{u1} α] [_inst_3 : StarRing.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_2)], Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.conjTranspose.{u1, u2, u2} n n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_2)))) (StarRing.toStarAddMonoid.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_2) _inst_3))) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))))))) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} n n α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasOne.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))))))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Semiring.{u2} α] [_inst_3 : StarRing.{u2} α (Semiring.toNonUnitalSemiring.{u2} α _inst_2)], Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.conjTranspose.{u2, u1, u1} n n α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_2)))) (StarRing.toStarAddMonoid.{u2} α (Semiring.toNonUnitalSemiring.{u2} α _inst_2) _inst_3))) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_2)) (Semiring.toOne.{u2} α _inst_2))))) (OfNat.ofNat.{max u2 u1} (Matrix.{u1, u1, u2} n n α) 1 (One.toOfNat1.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.one.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_2)) (Semiring.toOne.{u2} α _inst_2))))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_one Matrix.conjTranspose_oneₓ'. -/
@[simp]
theorem conjTranspose_one [DecidableEq n] [Semiring α] [StarRing α] : (1 : Matrix n n α)ᴴ = 1 := by
  simp [conj_transpose]
#align matrix.conj_transpose_one Matrix.conjTranspose_one

/- warning: matrix.conj_transpose_add -> Matrix.conjTranspose_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) (HAdd.hAdd.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHAdd.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))) M N)) (HAdd.hAdd.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.{u3, u2, u1} n m α) (Matrix.{u3, u2, u1} n m α) (instHAdd.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasAdd.{u1, u3, u2} n m α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) M) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddMonoid.{u3} α] [_inst_2 : StarAddMonoid.{u3} α _inst_1] (M : Matrix.{u2, u1, u3} m n α) (N : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α _inst_1 _inst_2)) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u2, u1} m n α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1)))) M N)) (HAdd.hAdd.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (instHAdd.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.add.{u3, u1, u2} n m α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1)))) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α _inst_1 _inst_2)) M) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α _inst_1 _inst_2)) N))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_add Matrix.conjTranspose_addₓ'. -/
@[simp]
theorem conjTranspose_add [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M + N)ᴴ = Mᴴ + Nᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_add Matrix.conjTranspose_add

/- warning: matrix.conj_transpose_sub -> Matrix.conjTranspose_sub is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : StarAddMonoid.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))] (M : Matrix.{u2, u3, u1} m n α) (N : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2)) (HSub.hSub.{max u2 u3 u1, max u2 u3 u1, max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α) (instHSub.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasSub.{u1, u2, u3} m n α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))) M N)) (HSub.hSub.{max u3 u2 u1, max u3 u2 u1, max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.{u3, u2, u1} n m α) (Matrix.{u3, u2, u1} n m α) (instHSub.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasSub.{u1, u3, u2} n m α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2)) M) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2)) N))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddGroup.{u3} α] [_inst_2 : StarAddMonoid.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1))] (M : Matrix.{u2, u1, u3} m n α) (N : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)) _inst_2)) (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSub.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.sub.{u3, u2, u1} m n α (SubNegMonoid.toSub.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)))) M N)) (HSub.hSub.{max (max u3 u2) u1, max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (instHSub.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.sub.{u3, u1, u2} n m α (SubNegMonoid.toSub.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)))) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)) _inst_2)) M) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)) _inst_2)) N))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_sub Matrix.conjTranspose_subₓ'. -/
@[simp]
theorem conjTranspose_sub [AddGroup α] [StarAddMonoid α] (M N : Matrix m n α) :
    (M - N)ᴴ = Mᴴ - Nᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_sub Matrix.conjTranspose_sub

/- warning: matrix.conj_transpose_smul -> Matrix.conjTranspose_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : Star.{u4} R] [_inst_2 : Star.{u1} α] [_inst_3 : SMul.{u4, u1} R α] [_inst_4 : StarModule.{u4, u1} R α _inst_1 _inst_2 _inst_3] (c : R) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_2 (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α _inst_3) c M)) (SMul.smul.{u4, max u3 u2 u1} R (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u4} n m R α _inst_3) (Star.star.{u4} R _inst_1 c) (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_2 M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} [_inst_1 : Star.{u3} R] [_inst_2 : Star.{u4} α] [_inst_3 : SMul.{u3, u4} R α] [_inst_4 : StarModule.{u3, u4} R α _inst_1 _inst_2 _inst_3] (c : R) (M : Matrix.{u2, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.conjTranspose.{u4, u2, u1} m n α _inst_2 (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_3)) c M)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.{u1, u2, u4} n m α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.smul.{u4, u1, u2, u3} n m R α _inst_3)) (Star.star.{u3} R _inst_1 c) (Matrix.conjTranspose.{u4, u2, u1} m n α _inst_2 M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_smul Matrix.conjTranspose_smulₓ'. -/
/-- Note that `star_module` is quite a strong requirement; as such we also provide the following
variants which this lemma would not apply to:
* `matrix.conj_transpose_smul_non_comm`
* `matrix.conj_transpose_nsmul`
* `matrix.conj_transpose_zsmul`
* `matrix.conj_transpose_nat_cast_smul`
* `matrix.conj_transpose_int_cast_smul`
* `matrix.conj_transpose_inv_nat_cast_smul`
* `matrix.conj_transpose_inv_int_cast_smul`
* `matrix.conj_transpose_rat_smul`
* `matrix.conj_transpose_rat_cast_smul`
-/
@[simp]
theorem conjTranspose_smul [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ :=
  Matrix.ext fun i j => star_smul _ _
#align matrix.conj_transpose_smul Matrix.conjTranspose_smul

/- warning: matrix.conj_transpose_smul_non_comm -> Matrix.conjTranspose_smul_non_comm is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : Star.{u4} R] [_inst_2 : Star.{u1} α] [_inst_3 : SMul.{u4, u1} R α] [_inst_4 : SMul.{u4, u1} (MulOpposite.{u4} R) α] (c : R) (M : Matrix.{u2, u3, u1} m n α), (forall (r : R) (a : α), Eq.{succ u1} α (Star.star.{u1} α _inst_2 (SMul.smul.{u4, u1} R α _inst_3 r a)) (SMul.smul.{u4, u1} (MulOpposite.{u4} R) α _inst_4 (MulOpposite.op.{u4} R (Star.star.{u4} R _inst_1 r)) (Star.star.{u1} α _inst_2 a))) -> (Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_2 (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α _inst_3) c M)) (SMul.smul.{u4, max u3 u2 u1} (MulOpposite.{u4} R) (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u4} n m (MulOpposite.{u4} R) α _inst_4) (MulOpposite.op.{u4} R (Star.star.{u4} R _inst_1 c)) (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_2 M)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} [_inst_1 : Star.{u3} R] [_inst_2 : Star.{u4} α] [_inst_3 : SMul.{u3, u4} R α] [_inst_4 : SMul.{u3, u4} (MulOpposite.{u3} R) α] (c : R) (M : Matrix.{u2, u1, u4} m n α), (forall (r : R) (a : α), Eq.{succ u4} α (Star.star.{u4} α _inst_2 (HSMul.hSMul.{u3, u4, u4} R α α (instHSMul.{u3, u4} R α _inst_3) r a)) (HSMul.hSMul.{u3, u4, u4} (MulOpposite.{u3} R) α α (instHSMul.{u3, u4} (MulOpposite.{u3} R) α _inst_4) (MulOpposite.op.{u3} R (Star.star.{u3} R _inst_1 r)) (Star.star.{u4} α _inst_2 a))) -> (Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.conjTranspose.{u4, u2, u1} m n α _inst_2 (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α _inst_3)) c M)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} (MulOpposite.{u3} R) (Matrix.{u1, u2, u4} n m α) (Matrix.{u1, u2, u4} n m α) (instHSMul.{u3, max (max u4 u2) u1} (MulOpposite.{u3} R) (Matrix.{u1, u2, u4} n m α) (Matrix.smul.{u4, u1, u2, u3} n m (MulOpposite.{u3} R) α _inst_4)) (MulOpposite.op.{u3} R (Star.star.{u3} R _inst_1 c)) (Matrix.conjTranspose.{u4, u2, u1} m n α _inst_2 M)))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_smul_non_comm Matrix.conjTranspose_smul_non_commₓ'. -/
@[simp]
theorem conjTranspose_smul_non_comm [Star R] [Star α] [SMul R α] [SMul Rᵐᵒᵖ α] (c : R)
    (M : Matrix m n α) (h : ∀ (r : R) (a : α), star (r • a) = MulOpposite.op (star r) • star a) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  Matrix.ext <| by simp [h]
#align matrix.conj_transpose_smul_non_comm Matrix.conjTranspose_smul_non_comm

/- warning: matrix.conj_transpose_smul_self -> Matrix.conjTranspose_smul_self is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : StarSemigroup.{u1} α _inst_1] (c : α) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarSemigroup.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) (SMul.smul.{u1, max u2 u3 u1} α (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u1} m n α α (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) c M)) (SMul.smul.{u1, max u3 u2 u1} (MulOpposite.{u1} α) (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u1} n m (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (MulOpposite.op.{u1} α (Star.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarSemigroup.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) c)) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarSemigroup.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Semigroup.{u3} α] [_inst_2 : StarSemigroup.{u3} α _inst_1] (c : α) (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarSemigroup.toInvolutiveStar.{u3} α _inst_1 _inst_2)) (HSMul.hSMul.{u3, max (max u3 u2) u1, max (max u3 u2) u1} α (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSMul.{u3, max (max u3 u2) u1} α (Matrix.{u2, u1, u3} m n α) (Matrix.smul.{u3, u2, u1, u3} m n α α (Mul.toSMul.{u3} α (Semigroup.toMul.{u3} α _inst_1)))) c M)) (HSMul.hSMul.{u3, max (max u1 u2) u3, max (max u3 u2) u1} (MulOpposite.{u3} α) (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (instHSMul.{u3, max (max u3 u2) u1} (MulOpposite.{u3} α) (Matrix.{u1, u2, u3} n m α) (Matrix.smul.{u3, u1, u2, u3} n m (MulOpposite.{u3} α) α (Mul.toHasOppositeSMul.{u3} α (Semigroup.toMul.{u3} α _inst_1)))) (MulOpposite.op.{u3} α (Star.star.{u3} α (InvolutiveStar.toStar.{u3} α (StarSemigroup.toInvolutiveStar.{u3} α _inst_1 _inst_2)) c)) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarSemigroup.toInvolutiveStar.{u3} α _inst_1 _inst_2)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_smul_self Matrix.conjTranspose_smul_selfₓ'. -/
@[simp]
theorem conjTranspose_smul_self [Semigroup α] [StarSemigroup α] (c : α) (M : Matrix m n α) :
    (c • M)ᴴ = MulOpposite.op (star c) • Mᴴ :=
  conjTranspose_smul_non_comm c M star_mul
#align matrix.conj_transpose_smul_self Matrix.conjTranspose_smul_self

/- warning: matrix.conj_transpose_nsmul -> Matrix.conjTranspose_nsmul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1] (c : Nat) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) (SMul.smul.{0, max u2 u3 u1} Nat (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, 0} m n Nat α (AddMonoid.SMul.{u1} α _inst_1)) c M)) (SMul.smul.{0, max u3 u2 u1} Nat (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, 0} n m Nat α (AddMonoid.SMul.{u1} α _inst_1)) c (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddMonoid.{u3} α] [_inst_2 : StarAddMonoid.{u3} α _inst_1] (c : Nat) (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α _inst_1 _inst_2)) (HSMul.hSMul.{0, max (max u3 u2) u1, max (max u3 u2) u1} Nat (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSMul.{0, max (max u3 u2) u1} Nat (Matrix.{u2, u1, u3} m n α) (AddMonoid.SMul.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.addMonoid.{u3, u2, u1} m n α _inst_1))) c M)) (HSMul.hSMul.{0, max (max u1 u2) u3, max (max u3 u2) u1} Nat (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (instHSMul.{0, max (max u3 u2) u1} Nat (Matrix.{u1, u2, u3} n m α) (AddMonoid.SMul.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.addMonoid.{u3, u1, u2} n m α _inst_1))) c (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α _inst_1 _inst_2)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_nsmul Matrix.conjTranspose_nsmulₓ'. -/
@[simp]
theorem conjTranspose_nsmul [AddMonoid α] [StarAddMonoid α] (c : ℕ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_nsmul Matrix.conjTranspose_nsmul

/- warning: matrix.conj_transpose_zsmul -> Matrix.conjTranspose_zsmul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : StarAddMonoid.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))] (c : Int) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2)) (SMul.smul.{0, max u2 u3 u1} Int (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, 0} m n Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c M)) (SMul.smul.{0, max u3 u2 u1} Int (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, 0} n m Int α (SubNegMonoid.SMulInt.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) c (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddGroup.{u3} α] [_inst_2 : StarAddMonoid.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1))] (c : Int) (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)) _inst_2)) (HSMul.hSMul.{0, max (max u3 u2) u1, max (max u3 u2) u1} Int (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSMul.{0, max (max u3 u2) u1} Int (Matrix.{u2, u1, u3} m n α) (SubNegMonoid.SMulInt.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (AddGroup.toSubNegMonoid.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.addGroup.{u3, u2, u1} m n α _inst_1)))) c M)) (HSMul.hSMul.{0, max (max u1 u2) u3, max (max u3 u2) u1} Int (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (instHSMul.{0, max (max u3 u2) u1} Int (Matrix.{u1, u2, u3} n m α) (SubNegMonoid.SMulInt.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (AddGroup.toSubNegMonoid.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.addGroup.{u3, u1, u2} n m α _inst_1)))) c (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)) _inst_2)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_zsmul Matrix.conjTranspose_zsmulₓ'. -/
@[simp]
theorem conjTranspose_zsmul [AddGroup α] [StarAddMonoid α] (c : ℤ) (M : Matrix m n α) :
    (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_zsmul Matrix.conjTranspose_zsmul

/- warning: matrix.conj_transpose_nat_cast_smul -> Matrix.conjTranspose_natCast_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : Semiring.{u4} R] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)] [_inst_4 : Module.{u4, u1} R α _inst_1 _inst_2] (c : Nat) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2) _inst_3)) (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R _inst_1)))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R _inst_1) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (Module.toMulActionWithZero.{u4, u1} R α _inst_1 _inst_2 _inst_4))))) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u4} Nat R (CoeTCₓ.coe.{1, succ u4} Nat R (Nat.castCoe.{u4} R (AddMonoidWithOne.toNatCast.{u4} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u4} R (NonAssocSemiring.toAddCommMonoidWithOne.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))))))) c) M)) (SMul.smul.{u4, max u3 u2 u1} R (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u4} n m R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R _inst_1)))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R _inst_1) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (Module.toMulActionWithZero.{u4, u1} R α _inst_1 _inst_2 _inst_4))))) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u4} Nat R (CoeTCₓ.coe.{1, succ u4} Nat R (Nat.castCoe.{u4} R (AddMonoidWithOne.toNatCast.{u4} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u4} R (NonAssocSemiring.toAddCommMonoidWithOne.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))))))) c) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2) _inst_3)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} α] [_inst_3 : StarAddMonoid.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)] [_inst_4 : Module.{u3, u4} R α _inst_1 _inst_2] (c : Nat) (M : Matrix.{u2, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2) _inst_3)) (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α (SMulZeroClass.toSMul.{u3, u4} R α (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (Module.toMulActionWithZero.{u3, u4} R α _inst_1 _inst_2 _inst_4)))))) (Nat.cast.{u3} R (Semiring.toNatCast.{u3} R _inst_1) c) M)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.{u1, u2, u4} n m α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.smul.{u4, u1, u2, u3} n m R α (SMulZeroClass.toSMul.{u3, u4} R α (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (Module.toMulActionWithZero.{u3, u4} R α _inst_1 _inst_2 _inst_4)))))) (Nat.cast.{u3} R (Semiring.toNatCast.{u3} R _inst_1) c) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2) _inst_3)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_nat_cast_smul Matrix.conjTranspose_natCast_smulₓ'. -/
@[simp]
theorem conjTranspose_natCast_smul [Semiring R] [AddCommMonoid α] [StarAddMonoid α] [Module R α]
    (c : ℕ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_nat_cast_smul Matrix.conjTranspose_natCast_smul

/- warning: matrix.conj_transpose_int_cast_smul -> Matrix.conjTranspose_intCast_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : Ring.{u4} R] [_inst_2 : AddCommGroup.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2)))] [_inst_4 : Module.{u4, u1} R α (Ring.toSemiring.{u4} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)] (c : Int) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))) _inst_3)) (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_1))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_1)) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (Module.toMulActionWithZero.{u4, u1} R α (Ring.toSemiring.{u4} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2) _inst_4))))) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Int R (HasLiftT.mk.{1, succ u4} Int R (CoeTCₓ.coe.{1, succ u4} Int R (Int.castCoe.{u4} R (AddGroupWithOne.toHasIntCast.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_1)))))) c) M)) (SMul.smul.{u4, max u3 u2 u1} R (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u4} n m R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_1))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_1)) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (Module.toMulActionWithZero.{u4, u1} R α (Ring.toSemiring.{u4} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2) _inst_4))))) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Int R (HasLiftT.mk.{1, succ u4} Int R (CoeTCₓ.coe.{1, succ u4} Int R (Int.castCoe.{u4} R (AddGroupWithOne.toHasIntCast.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_1)))))) c) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))) _inst_3)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} [_inst_1 : Ring.{u3} R] [_inst_2 : AddCommGroup.{u4} α] [_inst_3 : StarAddMonoid.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2)))] [_inst_4 : Module.{u3, u4} R α (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2)] (c : Int) (M : Matrix.{u2, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2))) _inst_3)) (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α (SMulZeroClass.toSMul.{u3, u4} R α (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1)) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (Module.toMulActionWithZero.{u3, u4} R α (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2) _inst_4)))))) (Int.cast.{u3} R (Ring.toIntCast.{u3} R _inst_1) c) M)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.{u1, u2, u4} n m α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.smul.{u4, u1, u2, u3} n m R α (SMulZeroClass.toSMul.{u3, u4} R α (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_1)) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (Module.toMulActionWithZero.{u3, u4} R α (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2) _inst_4)))))) (Int.cast.{u3} R (Ring.toIntCast.{u3} R _inst_1) c) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2))) _inst_3)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_int_cast_smul Matrix.conjTranspose_intCast_smulₓ'. -/
@[simp]
theorem conjTranspose_intCast_smul [Ring R] [AddCommGroup α] [StarAddMonoid α] [Module R α] (c : ℤ)
    (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_int_cast_smul Matrix.conjTranspose_intCast_smul

/- warning: matrix.conj_transpose_inv_nat_cast_smul -> Matrix.conjTranspose_inv_natCast_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : DivisionSemiring.{u4} R] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)] [_inst_4 : Module.{u4, u1} R α (DivisionSemiring.toSemiring.{u4} R _inst_1) _inst_2] (c : Nat) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2) _inst_3)) (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (DivisionSemiring.toSemiring.{u4} R _inst_1))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (DivisionSemiring.toSemiring.{u4} R _inst_1)) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (Module.toMulActionWithZero.{u4, u1} R α (DivisionSemiring.toSemiring.{u4} R _inst_1) _inst_2 _inst_4))))) (Inv.inv.{u4} R (DivInvMonoid.toHasInv.{u4} R (GroupWithZero.toDivInvMonoid.{u4} R (DivisionSemiring.toGroupWithZero.{u4} R _inst_1))) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u4} Nat R (CoeTCₓ.coe.{1, succ u4} Nat R (Nat.castCoe.{u4} R (AddMonoidWithOne.toNatCast.{u4} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u4} R (NonAssocSemiring.toAddCommMonoidWithOne.{u4} R (Semiring.toNonAssocSemiring.{u4} R (DivisionSemiring.toSemiring.{u4} R _inst_1)))))))) c)) M)) (SMul.smul.{u4, max u3 u2 u1} R (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u4} n m R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (DivisionSemiring.toSemiring.{u4} R _inst_1))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (DivisionSemiring.toSemiring.{u4} R _inst_1)) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (Module.toMulActionWithZero.{u4, u1} R α (DivisionSemiring.toSemiring.{u4} R _inst_1) _inst_2 _inst_4))))) (Inv.inv.{u4} R (DivInvMonoid.toHasInv.{u4} R (GroupWithZero.toDivInvMonoid.{u4} R (DivisionSemiring.toGroupWithZero.{u4} R _inst_1))) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u4} Nat R (CoeTCₓ.coe.{1, succ u4} Nat R (Nat.castCoe.{u4} R (AddMonoidWithOne.toNatCast.{u4} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u4} R (NonAssocSemiring.toAddCommMonoidWithOne.{u4} R (Semiring.toNonAssocSemiring.{u4} R (DivisionSemiring.toSemiring.{u4} R _inst_1)))))))) c)) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2) _inst_3)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} [_inst_1 : DivisionSemiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} α] [_inst_3 : StarAddMonoid.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)] [_inst_4 : Module.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R _inst_1) _inst_2] (c : Nat) (M : Matrix.{u2, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2) _inst_3)) (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α (SMulZeroClass.toSMul.{u3, u4} R α (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R _inst_1))) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R _inst_1)) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (Module.toMulActionWithZero.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_4)))))) (Inv.inv.{u3} R (DivisionSemiring.toInv.{u3} R _inst_1) (Nat.cast.{u3} R (Semiring.toNatCast.{u3} R (DivisionSemiring.toSemiring.{u3} R _inst_1)) c)) M)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.{u1, u2, u4} n m α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.smul.{u4, u1, u2, u3} n m R α (SMulZeroClass.toSMul.{u3, u4} R α (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R _inst_1))) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R _inst_1)) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2)) (Module.toMulActionWithZero.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R _inst_1) _inst_2 _inst_4)))))) (Inv.inv.{u3} R (DivisionSemiring.toInv.{u3} R _inst_1) (Nat.cast.{u3} R (Semiring.toNatCast.{u3} R (DivisionSemiring.toSemiring.{u3} R _inst_1)) c)) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_2) _inst_3)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_inv_nat_cast_smul Matrix.conjTranspose_inv_natCast_smulₓ'. -/
@[simp]
theorem conjTranspose_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] (c : ℕ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_inv_nat_cast_smul Matrix.conjTranspose_inv_natCast_smul

/- warning: matrix.conj_transpose_inv_int_cast_smul -> Matrix.conjTranspose_inv_intCast_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : DivisionRing.{u4} R] [_inst_2 : AddCommGroup.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2)))] [_inst_4 : Module.{u4, u1} R α (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)] (c : Int) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))) _inst_3)) (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (Module.toMulActionWithZero.{u4, u1} R α (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2) _inst_4))))) (Inv.inv.{u4} R (DivInvMonoid.toHasInv.{u4} R (DivisionRing.toDivInvMonoid.{u4} R _inst_1)) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Int R (HasLiftT.mk.{1, succ u4} Int R (CoeTCₓ.coe.{1, succ u4} Int R (Int.castCoe.{u4} R (AddGroupWithOne.toHasIntCast.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R (DivisionRing.toRing.{u4} R _inst_1))))))) c)) M)) (SMul.smul.{u4, max u3 u2 u1} R (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u4} n m R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (Module.toMulActionWithZero.{u4, u1} R α (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2) _inst_4))))) (Inv.inv.{u4} R (DivInvMonoid.toHasInv.{u4} R (DivisionRing.toDivInvMonoid.{u4} R _inst_1)) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Int R (HasLiftT.mk.{1, succ u4} Int R (CoeTCₓ.coe.{1, succ u4} Int R (Int.castCoe.{u4} R (AddGroupWithOne.toHasIntCast.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R (DivisionRing.toRing.{u4} R _inst_1))))))) c)) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))) _inst_3)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} [_inst_1 : DivisionRing.{u3} R] [_inst_2 : AddCommGroup.{u4} α] [_inst_3 : StarAddMonoid.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2)))] [_inst_4 : Module.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2)] (c : Int) (M : Matrix.{u2, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2))) _inst_3)) (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α (SMulZeroClass.toSMul.{u3, u4} R α (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (Module.toMulActionWithZero.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2) _inst_4)))))) (Inv.inv.{u3} R (DivisionRing.toInv.{u3} R _inst_1) (Int.cast.{u3} R (Ring.toIntCast.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) c)) M)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.{u1, u2, u4} n m α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.smul.{u4, u1, u2, u3} n m R α (SMulZeroClass.toSMul.{u3, u4} R α (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (Module.toMulActionWithZero.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2) _inst_4)))))) (Inv.inv.{u3} R (DivisionRing.toInv.{u3} R _inst_1) (Int.cast.{u3} R (Ring.toIntCast.{u3} R (DivisionRing.toRing.{u3} R _inst_1)) c)) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2))) _inst_3)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_inv_int_cast_smul Matrix.conjTranspose_inv_intCast_smulₓ'. -/
@[simp]
theorem conjTranspose_inv_intCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α]
    [Module R α] (c : ℤ) (M : Matrix m n α) : ((c : R)⁻¹ • M)ᴴ = (c : R)⁻¹ • Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_inv_int_cast_smul Matrix.conjTranspose_inv_intCast_smul

/- warning: matrix.conj_transpose_rat_cast_smul -> Matrix.conjTranspose_ratCast_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} {α : Type.{u1}} [_inst_1 : DivisionRing.{u4} R] [_inst_2 : AddCommGroup.{u1} α] [_inst_3 : StarAddMonoid.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2)))] [_inst_4 : Module.{u4, u1} R α (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)] (c : Rat) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))) _inst_3)) (SMul.smul.{u4, max u2 u3 u1} R (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, u4} m n R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (Module.toMulActionWithZero.{u4, u1} R α (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2) _inst_4))))) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u4} Rat R (CoeTCₓ.coe.{1, succ u4} Rat R (Rat.castCoe.{u4} R (DivisionRing.toHasRatCast.{u4} R _inst_1)))) c) M)) (SMul.smul.{u4, max u3 u2 u1} R (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, u4} n m R α (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_2)))) (Module.toMulActionWithZero.{u4, u1} R α (Ring.toSemiring.{u4} R (DivisionRing.toRing.{u4} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} α _inst_2) _inst_4))))) ((fun (a : Type) (b : Type.{u4}) [self : HasLiftT.{1, succ u4} a b] => self.0) Rat R (HasLiftT.mk.{1, succ u4} Rat R (CoeTCₓ.coe.{1, succ u4} Rat R (Rat.castCoe.{u4} R (DivisionRing.toHasRatCast.{u4} R _inst_1)))) c) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_2))) _inst_3)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u3}} {α : Type.{u4}} [_inst_1 : DivisionRing.{u3} R] [_inst_2 : AddCommGroup.{u4} α] [_inst_3 : StarAddMonoid.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2)))] [_inst_4 : Module.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2)] (c : Rat) (M : Matrix.{u2, u1, u4} m n α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2))) _inst_3)) (HSMul.hSMul.{u3, max (max u4 u2) u1, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.{u2, u1, u4} m n α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u2, u1, u4} m n α) (Matrix.smul.{u4, u2, u1, u3} m n R α (SMulZeroClass.toSMul.{u3, u4} R α (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (Module.toMulActionWithZero.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2) _inst_4)))))) (Rat.cast.{u3} R (DivisionRing.toRatCast.{u3} R _inst_1) c) M)) (HSMul.hSMul.{u3, max (max u1 u2) u4, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.{u1, u2, u4} n m α) (instHSMul.{u3, max (max u4 u2) u1} R (Matrix.{u1, u2, u4} n m α) (Matrix.smul.{u4, u1, u2, u3} n m R α (SMulZeroClass.toSMul.{u3, u4} R α (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u4} α (SubNegZeroMonoid.toNegZeroClass.{u4} α (SubtractionMonoid.toSubNegZeroMonoid.{u4} α (SubtractionCommMonoid.toSubtractionMonoid.{u4} α (AddCommGroup.toDivisionAddCommMonoid.{u4} α _inst_2))))) (Module.toMulActionWithZero.{u3, u4} R α (DivisionSemiring.toSemiring.{u3} R (DivisionRing.toDivisionSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} α _inst_2) _inst_4)))))) (Rat.cast.{u3} R (DivisionRing.toRatCast.{u3} R _inst_1) c) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (SubNegMonoid.toAddMonoid.{u4} α (AddGroup.toSubNegMonoid.{u4} α (AddCommGroup.toAddGroup.{u4} α _inst_2))) _inst_3)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_rat_cast_smul Matrix.conjTranspose_ratCast_smulₓ'. -/
@[simp]
theorem conjTranspose_ratCast_smul [DivisionRing R] [AddCommGroup α] [StarAddMonoid α] [Module R α]
    (c : ℚ) (M : Matrix m n α) : ((c : R) • M)ᴴ = (c : R) • Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_rat_cast_smul Matrix.conjTranspose_ratCast_smul

/- warning: matrix.conj_transpose_rat_smul -> Matrix.conjTranspose_rat_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddCommGroup.{u1} α] [_inst_2 : StarAddMonoid.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1)))] [_inst_3 : Module.{0, u1} Rat α Rat.semiring (AddCommGroup.toAddCommMonoid.{u1} α _inst_1)] (c : Rat) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) _inst_2)) (SMul.smul.{0, max u2 u3 u1} Rat (Matrix.{u2, u3, u1} m n α) (Matrix.hasSmul.{u1, u2, u3, 0} m n Rat α (SMulZeroClass.toHasSmul.{0, u1} Rat α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Rat α (MulZeroClass.toHasZero.{0} Rat (MulZeroOneClass.toMulZeroClass.{0} Rat (MonoidWithZero.toMulZeroOneClass.{0} Rat (Semiring.toMonoidWithZero.{0} Rat Rat.semiring)))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Rat α (Semiring.toMonoidWithZero.{0} Rat Rat.semiring) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1)))) (Module.toMulActionWithZero.{0, u1} Rat α Rat.semiring (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_3))))) c M)) (SMul.smul.{0, max u3 u2 u1} Rat (Matrix.{u3, u2, u1} n m α) (Matrix.hasSmul.{u1, u3, u2, 0} n m Rat α (SMulZeroClass.toHasSmul.{0, u1} Rat α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Rat α (MulZeroClass.toHasZero.{0} Rat (MulZeroOneClass.toMulZeroClass.{0} Rat (MonoidWithZero.toMulZeroOneClass.{0} Rat (Semiring.toMonoidWithZero.{0} Rat Rat.semiring)))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Rat α (Semiring.toMonoidWithZero.{0} Rat Rat.semiring) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α _inst_1)))) (Module.toMulActionWithZero.{0, u1} Rat α Rat.semiring (AddCommGroup.toAddCommMonoid.{u1} α _inst_1) _inst_3))))) c (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α _inst_1))) _inst_2)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddCommGroup.{u3} α] [_inst_2 : StarAddMonoid.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α (AddCommGroup.toAddGroup.{u3} α _inst_1)))] [_inst_3 : Module.{0, u3} Rat α Rat.semiring (AddCommGroup.toAddCommMonoid.{u3} α _inst_1)] (c : Rat) (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α (AddCommGroup.toAddGroup.{u3} α _inst_1))) _inst_2)) (HSMul.hSMul.{0, max (max u3 u2) u1, max (max u3 u2) u1} Rat (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α) (instHSMul.{0, max (max u3 u2) u1} Rat (Matrix.{u2, u1, u3} m n α) (Matrix.smul.{u3, u2, u1, 0} m n Rat α (SMulZeroClass.toSMul.{0, u3} Rat α (NegZeroClass.toZero.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u3} Rat α (CommMonoidWithZero.toZero.{0} Rat (CommGroupWithZero.toCommMonoidWithZero.{0} Rat Rat.commGroupWithZero)) (NegZeroClass.toZero.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u3} Rat α (Semiring.toMonoidWithZero.{0} Rat Rat.semiring) (NegZeroClass.toZero.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α _inst_1))))) (Module.toMulActionWithZero.{0, u3} Rat α Rat.semiring (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) _inst_3)))))) c M)) (HSMul.hSMul.{0, max (max u1 u2) u3, max (max u3 u2) u1} Rat (Matrix.{u1, u2, u3} n m α) (Matrix.{u1, u2, u3} n m α) (instHSMul.{0, max (max u3 u2) u1} Rat (Matrix.{u1, u2, u3} n m α) (Matrix.smul.{u3, u1, u2, 0} n m Rat α (SMulZeroClass.toSMul.{0, u3} Rat α (NegZeroClass.toZero.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u3} Rat α (CommMonoidWithZero.toZero.{0} Rat (CommGroupWithZero.toCommMonoidWithZero.{0} Rat Rat.commGroupWithZero)) (NegZeroClass.toZero.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u3} Rat α (Semiring.toMonoidWithZero.{0} Rat Rat.semiring) (NegZeroClass.toZero.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (SubtractionCommMonoid.toSubtractionMonoid.{u3} α (AddCommGroup.toDivisionAddCommMonoid.{u3} α _inst_1))))) (Module.toMulActionWithZero.{0, u3} Rat α Rat.semiring (AddCommGroup.toAddCommMonoid.{u3} α _inst_1) _inst_3)))))) c (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α (AddCommGroup.toAddGroup.{u3} α _inst_1))) _inst_2)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_rat_smul Matrix.conjTranspose_rat_smulₓ'. -/
@[simp]
theorem conjTranspose_rat_smul [AddCommGroup α] [StarAddMonoid α] [Module ℚ α] (c : ℚ)
    (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_rat_smul Matrix.conjTranspose_rat_smul

/- warning: matrix.conj_transpose_mul -> Matrix.conjTranspose_mul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} [_inst_1 : Fintype.{u4} n] [_inst_2 : NonUnitalSemiring.{u1} α] [_inst_3 : StarRing.{u1} α _inst_2] (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u4, u2, u1} n l α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} l m α) (Matrix.conjTranspose.{u1, u3, u2} m l α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (StarRing.toStarAddMonoid.{u1} α _inst_2 _inst_3))) (Matrix.mul.{u1, u3, u4, u2} m n l α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2)) M N)) (Matrix.mul.{u1, u2, u4, u3} l n m α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2)) (Matrix.conjTranspose.{u1, u4, u2} n l α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (StarRing.toStarAddMonoid.{u1} α _inst_2 _inst_3))) N) (Matrix.conjTranspose.{u1, u3, u4} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (StarRing.toStarAddMonoid.{u1} α _inst_2 _inst_3))) M))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u4}} [_inst_1 : Fintype.{u3} n] [_inst_2 : NonUnitalSemiring.{u4} α] [_inst_3 : StarRing.{u4} α _inst_2] (M : Matrix.{u2, u3, u4} m n α) (N : Matrix.{u3, u1, u4} n l α), Eq.{max (max (succ u4) (succ u1)) (succ u2)} (Matrix.{u1, u2, u4} l m α) (Matrix.conjTranspose.{u4, u2, u1} m l α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2))) (StarRing.toStarAddMonoid.{u4} α _inst_2 _inst_3))) (Matrix.mul.{u4, u2, u3, u1} m n l α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) M N)) (Matrix.mul.{u4, u1, u3, u2} l n m α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) (Matrix.conjTranspose.{u4, u3, u1} n l α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2))) (StarRing.toStarAddMonoid.{u4} α _inst_2 _inst_3))) N) (Matrix.conjTranspose.{u4, u2, u3} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2))) (StarRing.toStarAddMonoid.{u4} α _inst_2 _inst_3))) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_mul Matrix.conjTranspose_mulₓ'. -/
@[simp]
theorem conjTranspose_mul [Fintype n] [NonUnitalSemiring α] [StarRing α] (M : Matrix m n α)
    (N : Matrix n l α) : (M ⬝ N)ᴴ = Nᴴ ⬝ Mᴴ :=
  Matrix.ext <| by simp [mul_apply]
#align matrix.conj_transpose_mul Matrix.conjTranspose_mul

/- warning: matrix.conj_transpose_neg -> Matrix.conjTranspose_neg is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] [_inst_2 : StarAddMonoid.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))] (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2)) (Neg.neg.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasNeg.{u1, u2, u3} m n α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) M)) (Neg.neg.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasNeg.{u1, u3, u2} n m α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) _inst_2)) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddGroup.{u3} α] [_inst_2 : StarAddMonoid.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1))] (M : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)) _inst_2)) (Neg.neg.{max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.neg.{u3, u2, u1} m n α (NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (AddGroup.toSubtractionMonoid.{u3} α _inst_1))))) M)) (Neg.neg.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.neg.{u3, u1, u2} n m α (NegZeroClass.toNeg.{u3} α (SubNegZeroMonoid.toNegZeroClass.{u3} α (SubtractionMonoid.toSubNegZeroMonoid.{u3} α (AddGroup.toSubtractionMonoid.{u3} α _inst_1))))) (Matrix.conjTranspose.{u3, u2, u1} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (SubNegMonoid.toAddMonoid.{u3} α (AddGroup.toSubNegMonoid.{u3} α _inst_1)) _inst_2)) M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_neg Matrix.conjTranspose_negₓ'. -/
@[simp]
theorem conjTranspose_neg [AddGroup α] [StarAddMonoid α] (M : Matrix m n α) : (-M)ᴴ = -Mᴴ :=
  Matrix.ext <| by simp
#align matrix.conj_transpose_neg Matrix.conjTranspose_neg

/- warning: matrix.conj_transpose_map -> Matrix.conjTranspose_map is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Star.{u1} α] [_inst_2 : Star.{u2} β] {A : Matrix.{u3, u4, u1} m n α} (f : α -> β), (Function.Semiconj.{u1, u2} α β f (Star.star.{u1} α _inst_1) (Star.star.{u2} β _inst_2)) -> (Eq.{succ (max u4 u3 u2)} (Matrix.{u4, u3, u2} n m β) (Matrix.map.{u1, u2, u4, u3} n m α β (Matrix.conjTranspose.{u1, u3, u4} m n α _inst_1 A) f) (Matrix.conjTranspose.{u2, u3, u4} m n β _inst_2 (Matrix.map.{u1, u2, u3, u4} m n α β A f)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : Star.{u3} α] [_inst_2 : Star.{u4} β] {A : Matrix.{u2, u1, u3} m n α} (f : α -> β), (Function.Semiconj.{u3, u4} α β f (Star.star.{u3} α _inst_1) (Star.star.{u4} β _inst_2)) -> (Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m β) (Matrix.map.{u3, u4, u1, u2} n m α β (Matrix.conjTranspose.{u3, u2, u1} m n α _inst_1 A) f) (Matrix.conjTranspose.{u4, u2, u1} m n β _inst_2 (Matrix.map.{u3, u4, u2, u1} m n α β A f)))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_map Matrix.conjTranspose_mapₓ'. -/
theorem conjTranspose_map [Star α] [Star β] {A : Matrix m n α} (f : α → β)
    (hf : Function.Semiconj f star star) : Aᴴ.map f = (A.map f)ᴴ :=
  Matrix.ext fun i j => hf _
#align matrix.conj_transpose_map Matrix.conjTranspose_map

variable (m n α)

/- warning: matrix.conj_transpose_add_equiv -> Matrix.conjTransposeAddEquiv is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2}) (n : Type.{u3}) (α : Type.{u1}) [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1], AddEquiv.{max u2 u3 u1, max u3 u2 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (Matrix.hasAdd.{u1, u2, u3} m n α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.hasAdd.{u1, u3, u2} n m α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))
but is expected to have type
  forall (m : Type.{u2}) (n : Type.{u3}) (α : Type.{u1}) [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1], AddEquiv.{max (max u1 u3) u2, max (max u1 u2) u3} (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (Matrix.add.{u1, u2, u3} m n α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.add.{u1, u3, u2} n m α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_add_equiv Matrix.conjTransposeAddEquivₓ'. -/
/-- `matrix.conj_transpose` as an `add_equiv` -/
@[simps apply]
def conjTransposeAddEquiv [AddMonoid α] [StarAddMonoid α] : Matrix m n α ≃+ Matrix n m α
    where
  toFun := conjTranspose
  invFun := conjTranspose
  left_inv := conjTranspose_conjTranspose
  right_inv := conjTranspose_conjTranspose
  map_add' := conjTranspose_add
#align matrix.conj_transpose_add_equiv Matrix.conjTransposeAddEquiv

/- warning: matrix.conj_transpose_add_equiv_symm -> Matrix.conjTransposeAddEquiv_symm is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2}) (n : Type.{u3}) (α : Type.{u1}) [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1], Eq.{max (succ (max u3 u2 u1)) (succ (max u2 u3 u1))} (AddEquiv.{max u3 u2 u1, max u2 u3 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u3, u2} n m α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.hasAdd.{u1, u2, u3} m n α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))) (AddEquiv.symm.{max u2 u3 u1, max u3 u2 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (Matrix.hasAdd.{u1, u2, u3} m n α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.hasAdd.{u1, u3, u2} n m α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.conjTransposeAddEquiv.{u1, u2, u3} m n α _inst_1 _inst_2)) (Matrix.conjTransposeAddEquiv.{u1, u3, u2} n m α _inst_1 _inst_2)
but is expected to have type
  forall (m : Type.{u2}) (n : Type.{u1}) (α : Type.{u3}) [_inst_1 : AddMonoid.{u3} α] [_inst_2 : StarAddMonoid.{u3} α _inst_1], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AddEquiv.{max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u1, u2, u3} n m α) (Matrix.{u2, u1, u3} m n α) (Matrix.add.{u3, u1, u2} n m α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1))) (Matrix.add.{u3, u2, u1} m n α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1)))) (AddEquiv.symm.{max (max u3 u2) u1, max (max u3 u2) u1} (Matrix.{u2, u1, u3} m n α) (Matrix.{u1, u2, u3} n m α) (Matrix.add.{u3, u2, u1} m n α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1))) (Matrix.add.{u3, u1, u2} n m α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1))) (Matrix.conjTransposeAddEquiv.{u3, u2, u1} m n α _inst_1 _inst_2)) (Matrix.conjTransposeAddEquiv.{u3, u1, u2} n m α _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_add_equiv_symm Matrix.conjTransposeAddEquiv_symmₓ'. -/
@[simp]
theorem conjTransposeAddEquiv_symm [AddMonoid α] [StarAddMonoid α] :
    (conjTransposeAddEquiv m n α).symm = conjTransposeAddEquiv n m α :=
  rfl
#align matrix.conj_transpose_add_equiv_symm Matrix.conjTransposeAddEquiv_symm

variable {m n α}

/- warning: matrix.conj_transpose_list_sum -> Matrix.conjTranspose_list_sum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1] (l : List.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α)), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2)) (List.sum.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.hasAdd.{u1, u2, u3} m n α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.hasZero.{u1, u2, u3} m n α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) l)) (List.sum.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.hasAdd.{u1, u3, u2} n m α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (Matrix.hasZero.{u1, u3, u2} n m α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1))) (List.map.{max u2 u3 u1, max u3 u2 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2))) l))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : AddMonoid.{u3} α] [_inst_2 : StarAddMonoid.{u3} α _inst_1] (l : List.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} m n α)), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} n m α) (Matrix.conjTranspose.{u3, u1, u2} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α _inst_1 _inst_2)) (List.sum.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.add.{u3, u1, u2} m n α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1))) (Matrix.zero.{u3, u1, u2} m n α (AddMonoid.toZero.{u3} α _inst_1)) l)) (List.sum.{max (max u3 u1) u2} (Matrix.{u2, u1, u3} n m α) (Matrix.add.{u3, u2, u1} n m α (AddZeroClass.toAdd.{u3} α (AddMonoid.toAddZeroClass.{u3} α _inst_1))) (Matrix.zero.{u3, u2, u1} n m α (AddMonoid.toZero.{u3} α _inst_1)) (List.map.{max (max u2 u1) u3, max (max u2 u1) u3} (Matrix.{u1, u2, u3} m n α) (Matrix.{u2, u1, u3} n m α) (Matrix.conjTranspose.{u3, u1, u2} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α _inst_1 _inst_2))) l))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_list_sum Matrix.conjTranspose_list_sumₓ'. -/
theorem conjTranspose_list_sum [AddMonoid α] [StarAddMonoid α] (l : List (Matrix m n α)) :
    l.Sumᴴ = (l.map conjTranspose).Sum :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_list_sum l
#align matrix.conj_transpose_list_sum Matrix.conjTranspose_list_sum

/- warning: matrix.conj_transpose_multiset_sum -> Matrix.conjTranspose_multiset_sum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] (s : Multiset.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α)), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_2)) (Multiset.sum.{max u2 u3 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_1) s)) (Multiset.sum.{max u3 u2 u1} (Matrix.{u3, u2, u1} n m α) (Matrix.addCommMonoid.{u1, u3, u2} n m α _inst_1) (Multiset.map.{max u2 u3 u1, max u3 u2 u1} (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_2))) s))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : AddCommMonoid.{u3} α] [_inst_2 : StarAddMonoid.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1)] (s : Multiset.{max (max u3 u2) u1} (Matrix.{u1, u2, u3} m n α)), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} n m α) (Matrix.conjTranspose.{u3, u1, u2} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1) _inst_2)) (Multiset.sum.{max (max u3 u1) u2} (Matrix.{u1, u2, u3} m n α) (Matrix.addCommMonoid.{u3, u1, u2} m n α _inst_1) s)) (Multiset.sum.{max (max u3 u1) u2} (Matrix.{u2, u1, u3} n m α) (Matrix.addCommMonoid.{u3, u2, u1} n m α _inst_1) (Multiset.map.{max (max u2 u1) u3, max (max u2 u1) u3} (Matrix.{u1, u2, u3} m n α) (Matrix.{u2, u1, u3} n m α) (Matrix.conjTranspose.{u3, u1, u2} m n α (InvolutiveStar.toStar.{u3} α (StarAddMonoid.toInvolutiveStar.{u3} α (AddCommMonoid.toAddMonoid.{u3} α _inst_1) _inst_2))) s))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_multiset_sum Matrix.conjTranspose_multiset_sumₓ'. -/
theorem conjTranspose_multiset_sum [AddCommMonoid α] [StarAddMonoid α]
    (s : Multiset (Matrix m n α)) : s.Sumᴴ = (s.map conjTranspose).Sum :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_multiset_sum s
#align matrix.conj_transpose_multiset_sum Matrix.conjTranspose_multiset_sum

/- warning: matrix.conj_transpose_sum -> Matrix.conjTranspose_sum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)] {ι : Type.{u4}} (s : Finset.{u4} ι) (M : ι -> (Matrix.{u2, u3, u1} m n α)), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_2)) (Finset.sum.{max u2 u3 u1, u4} (Matrix.{u2, u3, u1} m n α) ι (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_1) s (fun (i : ι) => M i))) (Finset.sum.{max u3 u2 u1, u4} (Matrix.{u3, u2, u1} n m α) ι (Matrix.addCommMonoid.{u1, u3, u2} n m α _inst_1) s (fun (i : ι) => Matrix.conjTranspose.{u1, u2, u3} m n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1) _inst_2)) (M i)))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u4}} [_inst_1 : AddCommMonoid.{u4} α] [_inst_2 : StarAddMonoid.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_1)] {ι : Type.{u3}} (s : Finset.{u3} ι) (M : ι -> (Matrix.{u2, u1, u4} m n α)), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u1, u2, u4} n m α) (Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_1) _inst_2)) (Finset.sum.{max (max u1 u2) u4, u3} (Matrix.{u2, u1, u4} m n α) ι (Matrix.addCommMonoid.{u4, u2, u1} m n α _inst_1) s (fun (i : ι) => M i))) (Finset.sum.{max (max u1 u2) u4, u3} (Matrix.{u1, u2, u4} n m α) ι (Matrix.addCommMonoid.{u4, u1, u2} n m α _inst_1) s (fun (i : ι) => Matrix.conjTranspose.{u4, u2, u1} m n α (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_1) _inst_2)) (M i)))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_sum Matrix.conjTranspose_sumₓ'. -/
theorem conjTranspose_sum [AddCommMonoid α] [StarAddMonoid α] {ι : Type _} (s : Finset ι)
    (M : ι → Matrix m n α) : (∑ i in s, M i)ᴴ = ∑ i in s, (M i)ᴴ :=
  (conjTransposeAddEquiv m n α).toAddMonoidHom.map_sum _ s
#align matrix.conj_transpose_sum Matrix.conjTranspose_sum

variable (m n R α)

#print Matrix.conjTransposeLinearEquiv /-
/-- `matrix.conj_transpose` as a `linear_map` -/
@[simps apply]
def conjTransposeLinearEquiv [CommSemiring R] [StarRing R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] [StarModule R α] : Matrix m n α ≃ₗ⋆[R] Matrix n m α :=
  { conjTransposeAddEquiv m n α with map_smul' := conjTranspose_smul }
#align matrix.conj_transpose_linear_equiv Matrix.conjTransposeLinearEquiv
-/

/- warning: matrix.conj_transpose_linear_equiv_symm -> Matrix.conjTransposeLinearEquiv_symm is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2}) (n : Type.{u3}) (R : Type.{u4}) (α : Type.{u1}) [_inst_1 : CommSemiring.{u4} R] [_inst_2 : StarRing.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R (CommSemiring.toNonUnitalCommSemiring.{u4} R _inst_1))] [_inst_3 : AddCommMonoid.{u1} α] [_inst_4 : StarAddMonoid.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3)] [_inst_5 : Module.{u4, u1} R α (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3] [_inst_6 : StarModule.{u4, u1} R α (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R (CommSemiring.toNonUnitalCommSemiring.{u4} R _inst_1))))) (StarRing.toStarAddMonoid.{u4} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u4} R (CommSemiring.toNonUnitalCommSemiring.{u4} R _inst_1)) _inst_2))) (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3) _inst_4)) (SMulZeroClass.toHasSmul.{u4, u1} R α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (SMulWithZero.toSmulZeroClass.{u4, u1} R α (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1))))) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (MulActionWithZero.toSMulWithZero.{u4, u1} R α (Semiring.toMonoidWithZero.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1)) (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_3))) (Module.toMulActionWithZero.{u4, u1} R α (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_5))))], Eq.{max (succ (max u3 u2 u1)) (succ (max u2 u3 u1))} (LinearEquiv.{u4, u4, max u3 u2 u1, max u2 u3 u1} R R (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) (starRingEnd.{u4} R _inst_1 _inst_2) (starRingEnd.{u4} R _inst_1 _inst_2) (RingHomInvPair.StarRingEnd.ringHomInvPair.{u4} R _inst_1 _inst_2) (RingHomInvPair.StarRingEnd.ringHomInvPair.{u4} R _inst_1 _inst_2) (Matrix.{u3, u2, u1} n m α) (Matrix.{u2, u3, u1} m n α) (Matrix.addCommMonoid.{u1, u3, u2} n m α _inst_3) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_3) (Matrix.module.{u1, u3, u2, u4} n m R α (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_5) (Matrix.module.{u1, u2, u3, u4} m n R α (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_5)) (LinearEquiv.symm.{u4, u4, max u2 u3 u1, max u3 u2 u1} R R (Matrix.{u2, u3, u1} m n α) (Matrix.{u3, u2, u1} n m α) (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) (Matrix.addCommMonoid.{u1, u2, u3} m n α _inst_3) (Matrix.addCommMonoid.{u1, u3, u2} n m α _inst_3) (Matrix.module.{u1, u2, u3, u4} m n R α (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_5) (Matrix.module.{u1, u3, u2, u4} n m R α (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_5) (starRingEnd.{u4} R _inst_1 _inst_2) (starRingEnd.{u4} R _inst_1 _inst_2) (RingHomInvPair.StarRingEnd.ringHomInvPair.{u4} R _inst_1 _inst_2) (RingHomInvPair.StarRingEnd.ringHomInvPair.{u4} R _inst_1 _inst_2) (Matrix.conjTransposeLinearEquiv.{u1, u2, u3, u4} m n R α _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)) (Matrix.conjTransposeLinearEquiv.{u1, u3, u2, u4} n m R α _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)
but is expected to have type
  forall (m : Type.{u2}) (n : Type.{u1}) (R : Type.{u3}) (α : Type.{u4}) [_inst_1 : CommSemiring.{u3} R] [_inst_2 : StarRing.{u3} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u3} R (CommSemiring.toNonUnitalCommSemiring.{u3} R _inst_1))] [_inst_3 : AddCommMonoid.{u4} α] [_inst_4 : StarAddMonoid.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)] [_inst_5 : Module.{u3, u4} R α (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3] [_inst_6 : StarModule.{u3, u4} R α (InvolutiveStar.toStar.{u3} R (StarAddMonoid.toInvolutiveStar.{u3} R (AddMonoidWithOne.toAddMonoid.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (StarRing.toStarAddMonoid.{u3} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u3} R (CommSemiring.toNonUnitalCommSemiring.{u3} R _inst_1)) _inst_2))) (InvolutiveStar.toStar.{u4} α (StarAddMonoid.toInvolutiveStar.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3) _inst_4)) (SMulZeroClass.toSMul.{u3, u4} R α (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (SMulWithZero.toSMulZeroClass.{u3, u4} R α (CommMonoidWithZero.toZero.{u3} R (CommSemiring.toCommMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (MulActionWithZero.toSMulWithZero.{u3, u4} R α (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (AddMonoid.toZero.{u4} α (AddCommMonoid.toAddMonoid.{u4} α _inst_3)) (Module.toMulActionWithZero.{u3, u4} R α (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 _inst_5))))], Eq.{max (max (succ u4) (succ u2)) (succ u1)} (LinearEquiv.{u3, u3, max (max u4 u2) u1, max (max u4 u2) u1} R R (CommSemiring.toSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u3} R _inst_1) (starRingEnd.{u3} R _inst_1 _inst_2) (starRingEnd.{u3} R _inst_1 _inst_2) (RingHomInvPair.instRingHomInvPairToSemiringStarRingEnd.{u3} R _inst_1 _inst_2) (RingHomInvPair.instRingHomInvPairToSemiringStarRingEnd.{u3} R _inst_1 _inst_2) (Matrix.{u1, u2, u4} n m α) (Matrix.{u2, u1, u4} m n α) (Matrix.addCommMonoid.{u4, u1, u2} n m α _inst_3) (Matrix.addCommMonoid.{u4, u2, u1} m n α _inst_3) (Matrix.module.{u4, u1, u2, u3} n m R α (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 _inst_5) (Matrix.module.{u4, u2, u1, u3} m n R α (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 _inst_5)) (LinearEquiv.symm.{u3, u3, max (max u4 u2) u1, max (max u4 u2) u1} R R (Matrix.{u2, u1, u4} m n α) (Matrix.{u1, u2, u4} n m α) (CommSemiring.toSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u3} R _inst_1) (Matrix.addCommMonoid.{u4, u2, u1} m n α _inst_3) (Matrix.addCommMonoid.{u4, u1, u2} n m α _inst_3) (Matrix.module.{u4, u2, u1, u3} m n R α (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 _inst_5) (Matrix.module.{u4, u1, u2, u3} n m R α (CommSemiring.toSemiring.{u3} R _inst_1) _inst_3 _inst_5) (starRingEnd.{u3} R _inst_1 _inst_2) (starRingEnd.{u3} R _inst_1 _inst_2) (RingHomInvPair.instRingHomInvPairToSemiringStarRingEnd.{u3} R _inst_1 _inst_2) (RingHomInvPair.instRingHomInvPairToSemiringStarRingEnd.{u3} R _inst_1 _inst_2) (Matrix.conjTransposeLinearEquiv.{u4, u2, u1, u3} m n R α _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)) (Matrix.conjTransposeLinearEquiv.{u4, u1, u2, u3} n m R α _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_linear_equiv_symm Matrix.conjTransposeLinearEquiv_symmₓ'. -/
@[simp]
theorem conjTransposeLinearEquiv_symm [CommSemiring R] [StarRing R] [AddCommMonoid α]
    [StarAddMonoid α] [Module R α] [StarModule R α] :
    (conjTransposeLinearEquiv m n R α).symm = conjTransposeLinearEquiv n m R α :=
  rfl
#align matrix.conj_transpose_linear_equiv_symm Matrix.conjTransposeLinearEquiv_symm

variable {m n R α}

variable (m α)

/- warning: matrix.conj_transpose_ring_equiv -> Matrix.conjTransposeRingEquiv is a dubious translation:
lean 3 declaration is
  forall (m : Type.{u2}) (α : Type.{u1}) [_inst_1 : Semiring.{u1} α] [_inst_2 : StarRing.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)] [_inst_3 : Fintype.{u2} m], RingEquiv.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} m m α) (MulOpposite.{max u2 u1} (Matrix.{u2, u2, u1} m m α)) (Matrix.hasMul.{u1, u2} m α _inst_3 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (Matrix.hasAdd.{u1, u2, u2} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (MulOpposite.hasMul.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasMul.{u1, u2} m α _inst_3 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (MulOpposite.hasAdd.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasAdd.{u1, u2, u2} m m α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))
but is expected to have type
  forall (m : Type.{u2}) (α : Type.{u1}) [_inst_1 : Semiring.{u1} α] [_inst_2 : StarRing.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)] [_inst_3 : Fintype.{u2} m], RingEquiv.{max u1 u2, max u1 u2} (Matrix.{u2, u2, u1} m m α) (MulOpposite.{max u1 u2} (Matrix.{u2, u2, u1} m m α)) (Matrix.instMulMatrix.{u1, u2} m α _inst_3 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (MulOpposite.mul.{max u1 u2} (Matrix.{u2, u2, u1} m m α) (Matrix.instMulMatrix.{u1, u2} m α _inst_3 (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (Matrix.add.{u1, u2, u2} m m α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (MulOpposite.add.{max u1 u2} (Matrix.{u2, u2, u1} m m α) (Matrix.add.{u1, u2, u2} m m α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_ring_equiv Matrix.conjTransposeRingEquivₓ'. -/
/-- `matrix.conj_transpose` as a `ring_equiv` to the opposite ring -/
@[simps]
def conjTransposeRingEquiv [Semiring α] [StarRing α] [Fintype m] :
    Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ :=
  {
    (conjTransposeAddEquiv m m α).trans
      MulOpposite.opAddEquiv with
    toFun := fun M => MulOpposite.op Mᴴ
    invFun := fun M => M.unopᴴ
    map_mul' := fun M N =>
      (congr_arg MulOpposite.op (conjTranspose_mul M N)).trans (MulOpposite.op_mul _ _) }
#align matrix.conj_transpose_ring_equiv Matrix.conjTransposeRingEquiv

variable {m α}

/- warning: matrix.conj_transpose_pow -> Matrix.conjTranspose_pow is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : StarRing.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)] [_inst_3 : Fintype.{u2} m] [_inst_4 : DecidableEq.{succ u2} m] (M : Matrix.{u2, u2, u1} m m α) (k : Nat), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} m m α) (Matrix.conjTranspose.{u1, u2, u2} m m α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) (StarRing.toStarAddMonoid.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1) _inst_2))) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u2, u2, u1} m m α) Nat (Matrix.{u2, u2, u1} m m α) (instHPow.{max u2 u1, 0} (Matrix.{u2, u2, u1} m m α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.semiring.{u1, u2} m α _inst_1 _inst_3 (fun (a : m) (b : m) => _inst_4 a b)))))) M k)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u2, u2, u1} m m α) Nat (Matrix.{u2, u2, u1} m m α) (instHPow.{max u2 u1, 0} (Matrix.{u2, u2, u1} m m α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.semiring.{u1, u2} m α _inst_1 _inst_3 (fun (a : m) (b : m) => _inst_4 a b)))))) (Matrix.conjTranspose.{u1, u2, u2} m m α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) (StarRing.toStarAddMonoid.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1) _inst_2))) M) k)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] [_inst_2 : StarRing.{u2} α (Semiring.toNonUnitalSemiring.{u2} α _inst_1)] [_inst_3 : Fintype.{u1} m] [_inst_4 : DecidableEq.{succ u1} m] (M : Matrix.{u1, u1, u2} m m α) (k : Nat), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} m m α) (Matrix.conjTranspose.{u2, u1, u1} m m α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)))) (StarRing.toStarAddMonoid.{u2} α (Semiring.toNonUnitalSemiring.{u2} α _inst_1) _inst_2))) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u1, u1, u2} m m α) Nat (Matrix.{u1, u1, u2} m m α) (instHPow.{max u2 u1, 0} (Matrix.{u1, u1, u2} m m α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.semiring.{u2, u1} m α _inst_1 _inst_3 (fun (a : m) (b : m) => _inst_4 a b)))))) M k)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u1, u1, u2} m m α) Nat (Matrix.{u1, u1, u2} m m α) (instHPow.{max u2 u1, 0} (Matrix.{u1, u1, u2} m m α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.semiring.{u2, u1} m α _inst_1 _inst_3 (fun (a : m) (b : m) => _inst_4 a b)))))) (Matrix.conjTranspose.{u2, u1, u1} m m α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)))) (StarRing.toStarAddMonoid.{u2} α (Semiring.toNonUnitalSemiring.{u2} α _inst_1) _inst_2))) M) k)
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_pow Matrix.conjTranspose_powₓ'. -/
@[simp]
theorem conjTranspose_pow [Semiring α] [StarRing α] [Fintype m] [DecidableEq m] (M : Matrix m m α)
    (k : ℕ) : (M ^ k)ᴴ = Mᴴ ^ k :=
  MulOpposite.op_injective <| map_pow (conjTransposeRingEquiv m α) M k
#align matrix.conj_transpose_pow Matrix.conjTranspose_pow

/- warning: matrix.conj_transpose_list_prod -> Matrix.conjTranspose_list_prod is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : StarRing.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)] [_inst_3 : Fintype.{u2} m] [_inst_4 : DecidableEq.{succ u2} m] (l : List.{max u2 u1} (Matrix.{u2, u2, u1} m m α)), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} m m α) (Matrix.conjTranspose.{u1, u2, u2} m m α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) (StarRing.toStarAddMonoid.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1) _inst_2))) (List.prod.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasMul.{u1, u2} m α _inst_3 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (Matrix.hasOne.{u1, u2} m α (fun (a : m) (b : m) => _inst_4 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) l)) (List.prod.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasMul.{u1, u2} m α _inst_3 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (Matrix.hasOne.{u1, u2} m α (fun (a : m) (b : m) => _inst_4 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (List.reverse.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (List.map.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.{u2, u2, u1} m m α) (Matrix.conjTranspose.{u1, u2, u2} m m α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) (StarRing.toStarAddMonoid.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1) _inst_2)))) l)))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] [_inst_2 : StarRing.{u2} α (Semiring.toNonUnitalSemiring.{u2} α _inst_1)] [_inst_3 : Fintype.{u1} m] [_inst_4 : DecidableEq.{succ u1} m] (l : List.{max u2 u1} (Matrix.{u1, u1, u2} m m α)), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} m m α) (Matrix.conjTranspose.{u2, u1, u1} m m α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)))) (StarRing.toStarAddMonoid.{u2} α (Semiring.toNonUnitalSemiring.{u2} α _inst_1) _inst_2))) (List.prod.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.instMulMatrix.{u2, u1} m α _inst_3 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)))) (Matrix.one.{u2, u1} m α (fun (a : m) (b : m) => _inst_4 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (Semiring.toOne.{u2} α _inst_1)) l)) (List.prod.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.instMulMatrix.{u2, u1} m α _inst_3 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)))) (Matrix.one.{u2, u1} m α (fun (a : m) (b : m) => _inst_4 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_1)) (Semiring.toOne.{u2} α _inst_1)) (List.reverse.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (List.map.{max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} m m α) (Matrix.{u1, u1, u2} m m α) (Matrix.conjTranspose.{u2, u1, u1} m m α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1)))) (StarRing.toStarAddMonoid.{u2} α (Semiring.toNonUnitalSemiring.{u2} α _inst_1) _inst_2)))) l)))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_list_prod Matrix.conjTranspose_list_prodₓ'. -/
theorem conjTranspose_list_prod [Semiring α] [StarRing α] [Fintype m] [DecidableEq m]
    (l : List (Matrix m m α)) : l.Prodᴴ = (l.map conjTranspose).reverse.Prod :=
  (conjTransposeRingEquiv m α).unop_map_list_prod l
#align matrix.conj_transpose_list_prod Matrix.conjTranspose_list_prod

end ConjTranspose

section Star

/-- When `α` has a star operation, square matrices `matrix n n α` have a star
operation equal to `matrix.conj_transpose`. -/
instance [Star α] : Star (Matrix n n α) where unit := conjTranspose

/- warning: matrix.star_eq_conj_transpose -> Matrix.star_eq_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Star.{u1} α] (M : Matrix.{u2, u2, u1} m m α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} m m α) (Star.star.{max u2 u1} (Matrix.{u2, u2, u1} m m α) (Matrix.hasStar.{u1, u2} m α _inst_1) M) (Matrix.conjTranspose.{u1, u2, u2} m m α _inst_1 M)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Star.{u2} α] (M : Matrix.{u1, u1, u2} m m α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} m m α) (Star.star.{max u2 u1} (Matrix.{u1, u1, u2} m m α) (Matrix.instStarMatrix.{u2, u1} m α _inst_1) M) (Matrix.conjTranspose.{u2, u1, u1} m m α _inst_1 M)
Case conversion may be inaccurate. Consider using '#align matrix.star_eq_conj_transpose Matrix.star_eq_conjTransposeₓ'. -/
theorem star_eq_conjTranspose [Star α] (M : Matrix m m α) : star M = Mᴴ :=
  rfl
#align matrix.star_eq_conj_transpose Matrix.star_eq_conjTranspose

/- warning: matrix.star_apply -> Matrix.star_apply is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Star.{u1} α] (M : Matrix.{u2, u2, u1} n n α) (i : n) (j : n), Eq.{succ u1} α (Star.star.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasStar.{u1, u2} n α _inst_1) M i j) (Star.star.{u1} α _inst_1 (M j i))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Star.{u2} α] (M : Matrix.{u1, u1, u2} n n α) (i : n) (j : n), Eq.{succ u2} α (Star.star.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.instStarMatrix.{u2, u1} n α _inst_1) M i j) (Star.star.{u2} α _inst_1 (M j i))
Case conversion may be inaccurate. Consider using '#align matrix.star_apply Matrix.star_applyₓ'. -/
@[simp]
theorem star_apply [Star α] (M : Matrix n n α) (i j) : (star M) i j = star (M j i) :=
  rfl
#align matrix.star_apply Matrix.star_apply

instance [InvolutiveStar α] : InvolutiveStar (Matrix n n α)
    where star_involutive := conjTranspose_conjTranspose

/-- When `α` is a `*`-additive monoid, `matrix.has_star` is also a `*`-additive monoid. -/
instance [AddMonoid α] [StarAddMonoid α] : StarAddMonoid (Matrix n n α)
    where star_add := conjTranspose_add

instance [Star α] [Star β] [SMul α β] [StarModule α β] : StarModule α (Matrix n n β)
    where star_smul := conjTranspose_smul

/-- When `α` is a `*`-(semi)ring, `matrix.has_star` is also a `*`-(semi)ring. -/
instance [Fintype n] [NonUnitalSemiring α] [StarRing α] : StarRing (Matrix n n α)
    where
  star_add := conjTranspose_add
  star_mul := conjTranspose_mul

/- warning: matrix.star_mul -> Matrix.star_mul is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} n] [_inst_2 : NonUnitalSemiring.{u1} α] [_inst_3 : StarRing.{u1} α _inst_2] (M : Matrix.{u2, u2, u1} n n α) (N : Matrix.{u2, u2, u1} n n α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Star.star.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasStar.{u1, u2} n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (StarRing.toStarAddMonoid.{u1} α _inst_2 _inst_3)))) (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2)) M N)) (Matrix.mul.{u1, u2, u2, u2} n n n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2)) (Star.star.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasStar.{u1, u2} n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (StarRing.toStarAddMonoid.{u1} α _inst_2 _inst_3)))) N) (Star.star.{max u2 u1} (Matrix.{u2, u2, u1} n n α) (Matrix.hasStar.{u1, u2} n α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (StarRing.toStarAddMonoid.{u1} α _inst_2 _inst_3)))) M))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} n] [_inst_2 : NonUnitalSemiring.{u2} α] [_inst_3 : StarRing.{u2} α _inst_2] (M : Matrix.{u1, u1, u2} n n α) (N : Matrix.{u1, u1, u2} n n α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Star.star.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.instStarMatrix.{u2, u1} n α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_2))) (StarRing.toStarAddMonoid.{u2} α _inst_2 _inst_3)))) (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_2)) M N)) (Matrix.mul.{u2, u1, u1, u1} n n n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_2)) (Star.star.{max u1 u2} (Matrix.{u1, u1, u2} n n α) (Matrix.instStarMatrix.{u2, u1} n α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_2))) (StarRing.toStarAddMonoid.{u2} α _inst_2 _inst_3)))) N) (Star.star.{max u2 u1} (Matrix.{u1, u1, u2} n n α) (Matrix.instStarMatrix.{u2, u1} n α (InvolutiveStar.toStar.{u2} α (StarAddMonoid.toInvolutiveStar.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_2))) (StarRing.toStarAddMonoid.{u2} α _inst_2 _inst_3)))) M))
Case conversion may be inaccurate. Consider using '#align matrix.star_mul Matrix.star_mulₓ'. -/
/-- A version of `star_mul` for `⬝` instead of `*`. -/
theorem star_mul [Fintype n] [NonUnitalSemiring α] [StarRing α] (M N : Matrix n n α) :
    star (M ⬝ N) = star N ⬝ star M :=
  conjTranspose_mul _ _
#align matrix.star_mul Matrix.star_mul

end Star

#print Matrix.submatrix /-
/-- Given maps `(r_reindex : l → m)` and  `(c_reindex : o → n)` reindexing the rows and columns of
a matrix `M : matrix m n α`, the matrix `M.submatrix r_reindex c_reindex : matrix l o α` is defined
by `(M.submatrix r_reindex c_reindex) i j = M (r_reindex i) (c_reindex j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved. -/
def submatrix (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) : Matrix l o α :=
  of fun i j => A (r_reindex i) (c_reindex j)
#align matrix.submatrix Matrix.submatrix
-/

/- warning: matrix.submatrix_apply -> Matrix.submatrix_apply is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} (A : Matrix.{u3, u4, u1} m n α) (r_reindex : l -> m) (c_reindex : o -> n) (i : l) (j : o), Eq.{succ u1} α (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α A r_reindex c_reindex i j) (A (r_reindex i) (c_reindex j))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u5}} (A : Matrix.{u4, u3, u5} m n α) (r_reindex : l -> m) (c_reindex : o -> n) (i : l) (j : o), Eq.{succ u5} α (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α A r_reindex c_reindex i j) (A (r_reindex i) (c_reindex j))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_apply Matrix.submatrix_applyₓ'. -/
@[simp]
theorem submatrix_apply (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) (i j) :
    A.submatrix r_reindex c_reindex i j = A (r_reindex i) (c_reindex j) :=
  rfl
#align matrix.submatrix_apply Matrix.submatrix_apply

/- warning: matrix.submatrix_id_id -> Matrix.submatrix_id_id is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} (A : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.submatrix.{u1, u2, u2, u3, u3} m m n n α A (id.{succ u2} m) (id.{succ u3} n)) A
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.submatrix.{u3, u2, u2, u1, u1} m m n n α A (id.{succ u2} m) (id.{succ u1} n)) A
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_id_id Matrix.submatrix_id_idₓ'. -/
@[simp]
theorem submatrix_id_id (A : Matrix m n α) : A.submatrix id id = A :=
  ext fun _ _ => rfl
#align matrix.submatrix_id_id Matrix.submatrix_id_id

/- warning: matrix.submatrix_submatrix -> Matrix.submatrix_submatrix is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} {l₂ : Type.{u6}} {o₂ : Type.{u7}} (A : Matrix.{u3, u4, u1} m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o), Eq.{succ (max u6 u7 u1)} (Matrix.{u6, u7, u1} l₂ o₂ α) (Matrix.submatrix.{u1, u6, u2, u5, u7} l₂ l o o₂ α (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α A r₁ c₁) r₂ c₂) (Matrix.submatrix.{u1, u6, u3, u4, u7} l₂ m n o₂ α A (Function.comp.{succ u6, succ u2, succ u3} l₂ l m r₁ r₂) (Function.comp.{succ u7, succ u5, succ u4} o₂ o n c₁ c₂))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u7}} {l₂ : Type.{u6}} {o₂ : Type.{u5}} (A : Matrix.{u4, u3, u7} m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o), Eq.{max (max (succ u7) (succ u6)) (succ u5)} (Matrix.{u6, u5, u7} l₂ o₂ α) (Matrix.submatrix.{u7, u6, u2, u1, u5} l₂ l o o₂ α (Matrix.submatrix.{u7, u2, u4, u3, u1} l m n o α A r₁ c₁) r₂ c₂) (Matrix.submatrix.{u7, u6, u4, u3, u5} l₂ m n o₂ α A (Function.comp.{succ u6, succ u2, succ u4} l₂ l m r₁ r₂) (Function.comp.{succ u5, succ u1, succ u3} o₂ o n c₁ c₂))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_submatrix Matrix.submatrix_submatrixₓ'. -/
@[simp]
theorem submatrix_submatrix {l₂ o₂ : Type _} (A : Matrix m n α) (r₁ : l → m) (c₁ : o → n)
    (r₂ : l₂ → l) (c₂ : o₂ → o) :
    (A.submatrix r₁ c₁).submatrix r₂ c₂ = A.submatrix (r₁ ∘ r₂) (c₁ ∘ c₂) :=
  ext fun _ _ => rfl
#align matrix.submatrix_submatrix Matrix.submatrix_submatrix

/- warning: matrix.transpose_submatrix -> Matrix.transpose_submatrix is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} (A : Matrix.{u3, u4, u1} m n α) (r_reindex : l -> m) (c_reindex : o -> n), Eq.{succ (max u5 u2 u1)} (Matrix.{u5, u2, u1} o l α) (Matrix.transpose.{u1, u2, u5} l o α (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α A r_reindex c_reindex)) (Matrix.submatrix.{u1, u5, u4, u3, u2} o n m l α (Matrix.transpose.{u1, u3, u4} m n α A) c_reindex r_reindex)
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u5}} (A : Matrix.{u4, u3, u5} m n α) (r_reindex : l -> m) (c_reindex : o -> n), Eq.{max (max (succ u5) (succ u2)) (succ u1)} (Matrix.{u1, u2, u5} o l α) (Matrix.transpose.{u5, u2, u1} l o α (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α A r_reindex c_reindex)) (Matrix.submatrix.{u5, u1, u3, u4, u2} o n m l α (Matrix.transpose.{u5, u4, u3} m n α A) c_reindex r_reindex)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_submatrix Matrix.transpose_submatrixₓ'. -/
@[simp]
theorem transpose_submatrix (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
    (A.submatrix r_reindex c_reindex)ᵀ = Aᵀ.submatrix c_reindex r_reindex :=
  ext fun _ _ => rfl
#align matrix.transpose_submatrix Matrix.transpose_submatrix

/- warning: matrix.conj_transpose_submatrix -> Matrix.conjTranspose_submatrix is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Star.{u1} α] (A : Matrix.{u3, u4, u1} m n α) (r_reindex : l -> m) (c_reindex : o -> n), Eq.{succ (max u5 u2 u1)} (Matrix.{u5, u2, u1} o l α) (Matrix.conjTranspose.{u1, u2, u5} l o α _inst_1 (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α A r_reindex c_reindex)) (Matrix.submatrix.{u1, u5, u4, u3, u2} o n m l α (Matrix.conjTranspose.{u1, u3, u4} m n α _inst_1 A) c_reindex r_reindex)
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Star.{u5} α] (A : Matrix.{u4, u3, u5} m n α) (r_reindex : l -> m) (c_reindex : o -> n), Eq.{max (max (succ u5) (succ u2)) (succ u1)} (Matrix.{u1, u2, u5} o l α) (Matrix.conjTranspose.{u5, u2, u1} l o α _inst_1 (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α A r_reindex c_reindex)) (Matrix.submatrix.{u5, u1, u3, u4, u2} o n m l α (Matrix.conjTranspose.{u5, u4, u3} m n α _inst_1 A) c_reindex r_reindex)
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_submatrix Matrix.conjTranspose_submatrixₓ'. -/
@[simp]
theorem conjTranspose_submatrix [Star α] (A : Matrix m n α) (r_reindex : l → m)
    (c_reindex : o → n) : (A.submatrix r_reindex c_reindex)ᴴ = Aᴴ.submatrix c_reindex r_reindex :=
  ext fun _ _ => rfl
#align matrix.conj_transpose_submatrix Matrix.conjTranspose_submatrix

/- warning: matrix.submatrix_add -> Matrix.submatrix_add is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Add.{u1} α] (A : Matrix.{u3, u4, u1} m n α) (B : Matrix.{u3, u4, u1} m n α), Eq.{max (max (succ u2) (succ u3)) (max (succ u5) (succ u4)) (succ (max u2 u5 u1))} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α (HAdd.hAdd.{max u3 u4 u1, max u3 u4 u1, max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u1} m n α) (instHAdd.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.hasAdd.{u1, u3, u4} m n α _inst_1)) A B)) (HAdd.hAdd.{max (max u2 u3) (max u5 u4) u2 u5 u1, max (max u2 u3) (max u5 u4) u2 u5 u1, max (max u2 u3) (max u5 u4) u2 u5 u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (instHAdd.{max (max u2 u3) (max u5 u4) u2 u5 u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Pi.instAdd.{max u2 u3, max (max u5 u4) u2 u5 u1} (l -> m) (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (fun (i : l -> m) => Pi.instAdd.{max u5 u4, max u2 u5 u1} (o -> n) (fun (c_reindex : o -> n) => Matrix.{u2, u5, u1} l o α) (fun (i : o -> n) => Matrix.hasAdd.{u1, u2, u5} l o α _inst_1)))) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α A) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α B))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Add.{u5} α] (A : Matrix.{u4, u3, u5} m n α) (B : Matrix.{u4, u3, u5} m n α), Eq.{max (max (max (max (succ u5) (succ u2)) (succ u4)) (succ u3)) (succ u1)} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α (HAdd.hAdd.{max (max u5 u4) u3, max (max u5 u4) u3, max (max u5 u4) u3} (Matrix.{u4, u3, u5} m n α) (Matrix.{u4, u3, u5} m n α) (Matrix.{u4, u3, u5} m n α) (instHAdd.{max (max u5 u4) u3} (Matrix.{u4, u3, u5} m n α) (Matrix.add.{u5, u4, u3} m n α _inst_1)) A B)) (HAdd.hAdd.{max (max (max (max u5 u4) u3) u1) u2, max (max (max (max u5 u4) u3) u1) u2, max (max (max (max u5 u2) u4) u3) u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (instHAdd.{max (max (max (max u5 u4) u3) u1) u2} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (Pi.instAdd.{max u2 u4, max (max (max u5 u2) u3) u1} (l -> m) (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (fun (i : l -> m) => Pi.instAdd.{max u3 u1, max (max u5 u2) u1} (o -> n) (fun (c_reindex : o -> n) => Matrix.{u2, u1, u5} l o α) (fun (i : o -> n) => Matrix.add.{u5, u2, u1} l o α _inst_1)))) (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α A) (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α B))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_add Matrix.submatrix_addₓ'. -/
theorem submatrix_add [Add α] (A B : Matrix m n α) :
    ((A + B).submatrix : (l → m) → (o → n) → Matrix l o α) = A.submatrix + B.submatrix :=
  rfl
#align matrix.submatrix_add Matrix.submatrix_add

/- warning: matrix.submatrix_neg -> Matrix.submatrix_neg is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Neg.{u1} α] (A : Matrix.{u3, u4, u1} m n α), Eq.{max (max (succ u2) (succ u3)) (max (succ u5) (succ u4)) (succ (max u2 u5 u1))} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α (Neg.neg.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.hasNeg.{u1, u3, u4} m n α _inst_1) A)) (Neg.neg.{max (max u2 u3) (max u5 u4) u2 u5 u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Pi.instNeg.{max u2 u3, max (max u5 u4) u2 u5 u1} (l -> m) (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (fun (i : l -> m) => Pi.instNeg.{max u5 u4, max u2 u5 u1} (o -> n) (fun (c_reindex : o -> n) => Matrix.{u2, u5, u1} l o α) (fun (i : o -> n) => Matrix.hasNeg.{u1, u2, u5} l o α _inst_1))) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α A))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Neg.{u5} α] (A : Matrix.{u4, u3, u5} m n α), Eq.{max (max (max (max (succ u5) (succ u2)) (succ u4)) (succ u3)) (succ u1)} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α (Neg.neg.{max (max u5 u4) u3} (Matrix.{u4, u3, u5} m n α) (Matrix.neg.{u5, u4, u3} m n α _inst_1) A)) (Neg.neg.{max (max (max (max u5 u4) u3) u1) u2} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (Pi.instNeg.{max u4 u2, max (max (max u5 u3) u1) u2} (l -> m) (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (fun (i : l -> m) => Pi.instNeg.{max u3 u1, max (max u5 u1) u2} (o -> n) (fun (c_reindex : o -> n) => Matrix.{u2, u1, u5} l o α) (fun (i : o -> n) => Matrix.neg.{u5, u2, u1} l o α _inst_1))) (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α A))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_neg Matrix.submatrix_negₓ'. -/
theorem submatrix_neg [Neg α] (A : Matrix m n α) :
    ((-A).submatrix : (l → m) → (o → n) → Matrix l o α) = -A.submatrix :=
  rfl
#align matrix.submatrix_neg Matrix.submatrix_neg

/- warning: matrix.submatrix_sub -> Matrix.submatrix_sub is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Sub.{u1} α] (A : Matrix.{u3, u4, u1} m n α) (B : Matrix.{u3, u4, u1} m n α), Eq.{max (max (succ u2) (succ u3)) (max (succ u5) (succ u4)) (succ (max u2 u5 u1))} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α (HSub.hSub.{max u3 u4 u1, max u3 u4 u1, max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u1} m n α) (Matrix.{u3, u4, u1} m n α) (instHSub.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.hasSub.{u1, u3, u4} m n α _inst_1)) A B)) (HSub.hSub.{max (max u2 u3) (max u5 u4) u2 u5 u1, max (max u2 u3) (max u5 u4) u2 u5 u1, max (max u2 u3) (max u5 u4) u2 u5 u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (instHSub.{max (max u2 u3) (max u5 u4) u2 u5 u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Pi.instSub.{max u2 u3, max (max u5 u4) u2 u5 u1} (l -> m) (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (fun (i : l -> m) => Pi.instSub.{max u5 u4, max u2 u5 u1} (o -> n) (fun (c_reindex : o -> n) => Matrix.{u2, u5, u1} l o α) (fun (i : o -> n) => Matrix.hasSub.{u1, u2, u5} l o α _inst_1)))) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α A) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α B))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Sub.{u5} α] (A : Matrix.{u4, u3, u5} m n α) (B : Matrix.{u4, u3, u5} m n α), Eq.{max (max (max (max (succ u5) (succ u2)) (succ u4)) (succ u3)) (succ u1)} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α (HSub.hSub.{max (max u5 u4) u3, max (max u5 u4) u3, max (max u5 u4) u3} (Matrix.{u4, u3, u5} m n α) (Matrix.{u4, u3, u5} m n α) (Matrix.{u4, u3, u5} m n α) (instHSub.{max (max u5 u4) u3} (Matrix.{u4, u3, u5} m n α) (Matrix.sub.{u5, u4, u3} m n α _inst_1)) A B)) (HSub.hSub.{max (max (max (max u5 u4) u3) u1) u2, max (max (max (max u5 u4) u3) u1) u2, max (max (max (max u5 u2) u4) u3) u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (instHSub.{max (max (max (max u5 u4) u3) u1) u2} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (Pi.instSub.{max u2 u4, max (max (max u5 u2) u3) u1} (l -> m) (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u2, u1, u5} l o α)) (fun (i : l -> m) => Pi.instSub.{max u3 u1, max (max u5 u2) u1} (o -> n) (fun (c_reindex : o -> n) => Matrix.{u2, u1, u5} l o α) (fun (i : o -> n) => Matrix.sub.{u5, u2, u1} l o α _inst_1)))) (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α A) (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α B))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_sub Matrix.submatrix_subₓ'. -/
theorem submatrix_sub [Sub α] (A B : Matrix m n α) :
    ((A - B).submatrix : (l → m) → (o → n) → Matrix l o α) = A.submatrix - B.submatrix :=
  rfl
#align matrix.submatrix_sub Matrix.submatrix_sub

/- warning: matrix.submatrix_zero -> Matrix.submatrix_zero is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α], Eq.{max (max (succ u2) (succ u3)) (max (succ u5) (succ u4)) (succ (max u2 u5 u1))} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α (OfNat.ofNat.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) 0 (OfNat.mk.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) 0 (Zero.zero.{max u3 u4 u1} (Matrix.{u3, u4, u1} m n α) (Matrix.hasZero.{u1, u3, u4} m n α _inst_1))))) (OfNat.ofNat.{max (max u2 u3) (max u5 u4) u2 u5 u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) 0 (OfNat.mk.{max (max u2 u3) (max u5 u4) u2 u5 u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) 0 (Zero.zero.{max (max u2 u3) (max u5 u4) u2 u5 u1} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Pi.instZero.{max u2 u3, max (max u5 u4) u2 u5 u1} (l -> m) (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (fun (i : l -> m) => Pi.instZero.{max u5 u4, max u2 u5 u1} (o -> n) (fun (c_reindex : o -> n) => Matrix.{u2, u5, u1} l o α) (fun (i : o -> n) => Matrix.hasZero.{u1, u2, u5} l o α _inst_1))))))
but is expected to have type
  forall {l : Type.{u4}} {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Zero.{u5} α], Eq.{max (max (max (max (succ u5) (succ u4)) (succ u3)) (succ u2)) (succ u1)} ((l -> m) -> (o -> n) -> (Matrix.{u4, u1, u5} l o α)) (Matrix.submatrix.{u5, u4, u3, u2, u1} l m n o α (OfNat.ofNat.{max (max u5 u3) u2} (Matrix.{u3, u2, u5} m n α) 0 (Zero.toOfNat0.{max (max u5 u3) u2} (Matrix.{u3, u2, u5} m n α) (Matrix.zero.{u5, u3, u2} m n α _inst_1)))) (OfNat.ofNat.{max (max (max (max u5 u4) u3) u2) u1} ((l -> m) -> (o -> n) -> (Matrix.{u4, u1, u5} l o α)) 0 (Zero.toOfNat0.{max (max (max (max u5 u4) u3) u2) u1} ((l -> m) -> (o -> n) -> (Matrix.{u4, u1, u5} l o α)) (Pi.instZero.{max u4 u3, max (max (max u5 u4) u2) u1} (l -> m) (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u4, u1, u5} l o α)) (fun (i : l -> m) => Pi.instZero.{max u2 u1, max (max u5 u4) u1} (o -> n) (fun (c_reindex : o -> n) => Matrix.{u4, u1, u5} l o α) (fun (i : o -> n) => Matrix.zero.{u5, u4, u1} l o α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_zero Matrix.submatrix_zeroₓ'. -/
@[simp]
theorem submatrix_zero [Zero α] :
    ((0 : Matrix m n α).submatrix : (l → m) → (o → n) → Matrix l o α) = 0 :=
  rfl
#align matrix.submatrix_zero Matrix.submatrix_zero

/- warning: matrix.submatrix_smul -> Matrix.submatrix_smul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} {R : Type.{u6}} [_inst_1 : SMul.{u6, u1} R α] (r : R) (A : Matrix.{u3, u4, u1} m n α), Eq.{max (max (succ u2) (succ u3)) (max (succ u5) (succ u4)) (succ (max u2 u5 u1))} ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α (SMul.smul.{u6, max u3 u4 u1} R (Matrix.{u3, u4, u1} m n α) (Matrix.hasSmul.{u1, u3, u4, u6} m n R α _inst_1) r A)) (SMul.smul.{u6, max (max u2 u3) (max u5 u4) u2 u5 u1} R ((l -> m) -> (o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Function.hasSMul.{max u2 u3, u6, max (max u5 u4) u2 u5 u1} (l -> m) R ((o -> n) -> (Matrix.{u2, u5, u1} l o α)) (Function.hasSMul.{max u5 u4, u6, max u2 u5 u1} (o -> n) R (Matrix.{u2, u5, u1} l o α) (Matrix.hasSmul.{u1, u2, u5, u6} l o R α _inst_1))) r (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α A))
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u6}} {R : Type.{u5}} [_inst_1 : SMul.{u5, u6} R α] (r : R) (A : Matrix.{u4, u3, u6} m n α), Eq.{max (max (max (max (succ u6) (succ u2)) (succ u4)) (succ u3)) (succ u1)} ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u6} l o α)) (Matrix.submatrix.{u6, u2, u4, u3, u1} l m n o α (HSMul.hSMul.{u5, max (max u6 u4) u3, max (max u6 u4) u3} R (Matrix.{u4, u3, u6} m n α) (Matrix.{u4, u3, u6} m n α) (instHSMul.{u5, max (max u6 u4) u3} R (Matrix.{u4, u3, u6} m n α) (Matrix.smul.{u6, u4, u3, u5} m n R α _inst_1)) r A)) (HSMul.hSMul.{u5, max (max (max (max u6 u4) u3) u1) u2, max (max (max (max u6 u4) u3) u1) u2} R ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u6} l o α)) ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u6} l o α)) (instHSMul.{u5, max (max (max (max u6 u4) u3) u1) u2} R ((l -> m) -> (o -> n) -> (Matrix.{u2, u1, u6} l o α)) (Pi.instSMul.{max u4 u2, max (max (max u6 u3) u1) u2, u5} (l -> m) R (fun (r_reindex : l -> m) => (o -> n) -> (Matrix.{u2, u1, u6} l o α)) (fun (i : l -> m) => Pi.instSMul.{max u3 u1, max (max u6 u1) u2, u5} (o -> n) R (fun (c_reindex : o -> n) => Matrix.{u2, u1, u6} l o α) (fun (i : o -> n) => Matrix.smul.{u6, u2, u1, u5} l o R α _inst_1)))) r (Matrix.submatrix.{u6, u2, u4, u3, u1} l m n o α A))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_smul Matrix.submatrix_smulₓ'. -/
theorem submatrix_smul {R : Type _} [SMul R α] (r : R) (A : Matrix m n α) :
    ((r • A : Matrix m n α).submatrix : (l → m) → (o → n) → Matrix l o α) = r • A.submatrix :=
  rfl
#align matrix.submatrix_smul Matrix.submatrix_smul

/- warning: matrix.submatrix_map -> Matrix.submatrix_map is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u5}} {o : Type.{u6}} {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (e₁ : l -> m) (e₂ : o -> n) (A : Matrix.{u4, u5, u1} m n α), Eq.{succ (max u3 u6 u2)} (Matrix.{u3, u6, u2} l o β) (Matrix.submatrix.{u2, u3, u4, u5, u6} l m n o β (Matrix.map.{u1, u2, u4, u5} m n α β A f) e₁ e₂) (Matrix.map.{u1, u2, u3, u6} l o α β (Matrix.submatrix.{u1, u3, u4, u5, u6} l m n o α A e₁ e₂) f)
but is expected to have type
  forall {l : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {o : Type.{u1}} {α : Type.{u5}} {β : Type.{u6}} (f : α -> β) (e₁ : l -> m) (e₂ : o -> n) (A : Matrix.{u4, u3, u5} m n α), Eq.{max (max (succ u6) (succ u2)) (succ u1)} (Matrix.{u2, u1, u6} l o β) (Matrix.submatrix.{u6, u2, u4, u3, u1} l m n o β (Matrix.map.{u5, u6, u4, u3} m n α β A f) e₁ e₂) (Matrix.map.{u5, u6, u2, u1} l o α β (Matrix.submatrix.{u5, u2, u4, u3, u1} l m n o α A e₁ e₂) f)
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_map Matrix.submatrix_mapₓ'. -/
theorem submatrix_map (f : α → β) (e₁ : l → m) (e₂ : o → n) (A : Matrix m n α) :
    (A.map f).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map f :=
  rfl
#align matrix.submatrix_map Matrix.submatrix_map

/- warning: matrix.submatrix_diagonal -> Matrix.submatrix_diagonal is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} l] (d : m -> α) (e : l -> m), (Function.Injective.{succ u2, succ u3} l m e) -> (Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} l l α) (Matrix.submatrix.{u1, u2, u3, u3, u2} l m m l α (Matrix.diagonal.{u1, u3} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_1 d) e e) (Matrix.diagonal.{u1, u2} l α (fun (a : l) (b : l) => _inst_3 a b) _inst_1 (Function.comp.{succ u2, succ u3, succ u1} l m α d e)))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : DecidableEq.{succ u1} l] (d : m -> α) (e : l -> m), (Function.Injective.{succ u1, succ u2} l m e) -> (Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} l l α) (Matrix.submatrix.{u3, u1, u2, u2, u1} l m m l α (Matrix.diagonal.{u3, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_1 d) e e) (Matrix.diagonal.{u3, u1} l α (fun (a : l) (b : l) => _inst_3 a b) _inst_1 (Function.comp.{succ u1, succ u2, succ u3} l m α d e)))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_diagonal Matrix.submatrix_diagonalₓ'. -/
/-- Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexing map `e` is
  injective, then the resulting matrix is again diagonal. -/
theorem submatrix_diagonal [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l → m)
    (he : Function.Injective e) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  ext fun i j => by
    rw [submatrix_apply]
    by_cases h : i = j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (he.ne h)]
#align matrix.submatrix_diagonal Matrix.submatrix_diagonal

/- warning: matrix.submatrix_one -> Matrix.submatrix_one is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : DecidableEq.{succ u3} m] [_inst_4 : DecidableEq.{succ u2} l] (e : l -> m), (Function.Injective.{succ u2, succ u3} l m e) -> (Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} l l α) (Matrix.submatrix.{u1, u2, u3, u3, u2} l m m l α (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} m m α) 1 (OfNat.mk.{max u3 u1} (Matrix.{u3, u3, u1} m m α) 1 (One.one.{max u3 u1} (Matrix.{u3, u3, u1} m m α) (Matrix.hasOne.{u1, u3} m α (fun (a : m) (b : m) => _inst_3 a b) _inst_1 _inst_2)))) e e) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} l l α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} l l α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} l l α) (Matrix.hasOne.{u1, u2} l α (fun (a : l) (b : l) => _inst_4 a b) _inst_1 _inst_2)))))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_2 : One.{u3} α] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : DecidableEq.{succ u1} l] (e : l -> m), (Function.Injective.{succ u1, succ u2} l m e) -> (Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} l l α) (Matrix.submatrix.{u3, u1, u2, u2, u1} l m m l α (OfNat.ofNat.{max u3 u2} (Matrix.{u2, u2, u3} m m α) 1 (One.toOfNat1.{max u3 u2} (Matrix.{u2, u2, u3} m m α) (Matrix.one.{u3, u2} m α (fun (a : m) (b : m) => _inst_3 a b) _inst_1 _inst_2))) e e) (OfNat.ofNat.{max u3 u1} (Matrix.{u1, u1, u3} l l α) 1 (One.toOfNat1.{max u3 u1} (Matrix.{u1, u1, u3} l l α) (Matrix.one.{u3, u1} l α (fun (a : l) (b : l) => _inst_4 a b) _inst_1 _inst_2))))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_one Matrix.submatrix_oneₓ'. -/
theorem submatrix_one [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l → m)
    (he : Function.Injective e) : (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_diagonal _ e he
#align matrix.submatrix_one Matrix.submatrix_one

/- warning: matrix.submatrix_mul -> Matrix.submatrix_mul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Fintype.{u4} n] [_inst_2 : Fintype.{u5} o] [_inst_3 : Mul.{u1} α] [_inst_4 : AddCommMonoid.{u1} α] {p : Type.{u6}} {q : Type.{u7}} (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u4, u6, u1} n p α) (e₁ : l -> m) (e₂ : o -> n) (e₃ : q -> p), (Function.Bijective.{succ u5, succ u4} o n e₂) -> (Eq.{succ (max u2 u7 u1)} (Matrix.{u2, u7, u1} l q α) (Matrix.submatrix.{u1, u2, u3, u6, u7} l m p q α (Matrix.mul.{u1, u3, u4, u6} m n p α _inst_1 _inst_3 _inst_4 M N) e₁ e₃) (Matrix.mul.{u1, u2, u5, u7} l o q α _inst_2 _inst_3 _inst_4 (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α M e₁ e₂) (Matrix.submatrix.{u1, u5, u4, u6, u7} o n p q α N e₂ e₃)))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u6}} {o : Type.{u5}} {α : Type.{u7}} [_inst_1 : Fintype.{u6} n] [_inst_2 : Fintype.{u5} o] [_inst_3 : Mul.{u7} α] [_inst_4 : AddCommMonoid.{u7} α] {p : Type.{u4}} {q : Type.{u3}} (M : Matrix.{u2, u6, u7} m n α) (N : Matrix.{u6, u4, u7} n p α) (e₁ : l -> m) (e₂ : o -> n) (e₃ : q -> p), (Function.Bijective.{succ u5, succ u6} o n e₂) -> (Eq.{max (max (succ u7) (succ u1)) (succ u3)} (Matrix.{u1, u3, u7} l q α) (Matrix.submatrix.{u7, u1, u2, u4, u3} l m p q α (Matrix.mul.{u7, u2, u6, u4} m n p α _inst_1 _inst_3 _inst_4 M N) e₁ e₃) (Matrix.mul.{u7, u1, u5, u3} l o q α _inst_2 _inst_3 _inst_4 (Matrix.submatrix.{u7, u1, u2, u6, u5} l m n o α M e₁ e₂) (Matrix.submatrix.{u7, u5, u6, u4, u3} o n p q α N e₂ e₃)))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_mul Matrix.submatrix_mulₓ'. -/
theorem submatrix_mul [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p q : Type _}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o → n) (e₃ : q → p)
    (he₂ : Function.Bijective e₂) :
    (M ⬝ N).submatrix e₁ e₃ = M.submatrix e₁ e₂ ⬝ N.submatrix e₂ e₃ :=
  ext fun _ _ => (he₂.sum_comp _).symm
#align matrix.submatrix_mul Matrix.submatrix_mul

/- warning: matrix.diag_submatrix -> Matrix.diag_submatrix is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {α : Type.{u1}} (A : Matrix.{u3, u3, u1} m m α) (e : l -> m), Eq.{max (succ u2) (succ u1)} (l -> α) (Matrix.diag.{u1, u2} l α (Matrix.submatrix.{u1, u2, u3, u3, u2} l m m l α A e e)) (Function.comp.{succ u2, succ u3, succ u1} l m α (Matrix.diag.{u1, u3} m α A) e)
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} (A : Matrix.{u2, u2, u3} m m α) (e : l -> m), Eq.{max (succ u3) (succ u1)} (l -> α) (Matrix.diag.{u3, u1} l α (Matrix.submatrix.{u3, u1, u2, u2, u1} l m m l α A e e)) (Function.comp.{succ u1, succ u2, succ u3} l m α (Matrix.diag.{u3, u2} m α A) e)
Case conversion may be inaccurate. Consider using '#align matrix.diag_submatrix Matrix.diag_submatrixₓ'. -/
theorem diag_submatrix (A : Matrix m m α) (e : l → m) : diag (A.submatrix e e) = A.diag ∘ e :=
  rfl
#align matrix.diag_submatrix Matrix.diag_submatrix

/-! `simp` lemmas for `matrix.submatrix`s interaction with `matrix.diagonal`, `1`, and `matrix.mul`
for when the mappings are bundled. -/


/- warning: matrix.submatrix_diagonal_embedding -> Matrix.submatrix_diagonal_embedding is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} l] (d : m -> α) (e : Function.Embedding.{succ u2, succ u3} l m), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} l l α) (Matrix.submatrix.{u1, u2, u3, u3, u2} l m m l α (Matrix.diagonal.{u1, u3} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_1 d) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} l m) (fun (_x : Function.Embedding.{succ u2, succ u3} l m) => l -> m) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} l m) e) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} l m) (fun (_x : Function.Embedding.{succ u2, succ u3} l m) => l -> m) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} l m) e)) (Matrix.diagonal.{u1, u2} l α (fun (a : l) (b : l) => _inst_3 a b) _inst_1 (Function.comp.{succ u2, succ u3, succ u1} l m α d (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} l m) (fun (_x : Function.Embedding.{succ u2, succ u3} l m) => l -> m) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} l m) e)))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : DecidableEq.{succ u1} l] (d : m -> α) (e : Function.Embedding.{succ u1, succ u2} l m), Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} l l α) (Matrix.submatrix.{u3, u1, u2, u2, u1} l m m l α (Matrix.diagonal.{u3, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_1 d) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : l) => m) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l m (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} l m)) e) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : l) => m) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l m (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} l m)) e)) (Matrix.diagonal.{u3, u1} l α (fun (a : l) (b : l) => _inst_3 a b) _inst_1 (Function.comp.{succ u1, succ u2, succ u3} l m α d (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : l) => m) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l m (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} l m)) e)))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_diagonal_embedding Matrix.submatrix_diagonal_embeddingₓ'. -/
@[simp]
theorem submatrix_diagonal_embedding [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α)
    (e : l ↪ m) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.Injective
#align matrix.submatrix_diagonal_embedding Matrix.submatrix_diagonal_embedding

/- warning: matrix.submatrix_diagonal_equiv -> Matrix.submatrix_diagonal_equiv is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : DecidableEq.{succ u3} m] [_inst_3 : DecidableEq.{succ u2} l] (d : m -> α) (e : Equiv.{succ u2, succ u3} l m), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} l l α) (Matrix.submatrix.{u1, u2, u3, u3, u2} l m m l α (Matrix.diagonal.{u1, u3} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_1 d) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} l m) (fun (_x : Equiv.{succ u2, succ u3} l m) => l -> m) (Equiv.hasCoeToFun.{succ u2, succ u3} l m) e) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} l m) (fun (_x : Equiv.{succ u2, succ u3} l m) => l -> m) (Equiv.hasCoeToFun.{succ u2, succ u3} l m) e)) (Matrix.diagonal.{u1, u2} l α (fun (a : l) (b : l) => _inst_3 a b) _inst_1 (Function.comp.{succ u2, succ u3, succ u1} l m α d (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} l m) (fun (_x : Equiv.{succ u2, succ u3} l m) => l -> m) (Equiv.hasCoeToFun.{succ u2, succ u3} l m) e)))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_2 : DecidableEq.{succ u2} m] [_inst_3 : DecidableEq.{succ u1} l] (d : m -> α) (e : Equiv.{succ u1, succ u2} l m), Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} l l α) (Matrix.submatrix.{u3, u1, u2, u2, u1} l m m l α (Matrix.diagonal.{u3, u2} m α (fun (a : m) (b : m) => _inst_2 a b) _inst_1 d) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : l) => m) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} l m) e) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : l) => m) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} l m) e)) (Matrix.diagonal.{u3, u1} l α (fun (a : l) (b : l) => _inst_3 a b) _inst_1 (Function.comp.{succ u1, succ u2, succ u3} l m α d (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : l) => m) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} l m) e)))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_diagonal_equiv Matrix.submatrix_diagonal_equivₓ'. -/
@[simp]
theorem submatrix_diagonal_equiv [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l ≃ m) :
    (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.Injective
#align matrix.submatrix_diagonal_equiv Matrix.submatrix_diagonal_equiv

/- warning: matrix.submatrix_one_embedding -> Matrix.submatrix_one_embedding is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : DecidableEq.{succ u3} m] [_inst_4 : DecidableEq.{succ u2} l] (e : Function.Embedding.{succ u2, succ u3} l m), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} l l α) (Matrix.submatrix.{u1, u2, u3, u3, u2} l m m l α (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} m m α) 1 (OfNat.mk.{max u3 u1} (Matrix.{u3, u3, u1} m m α) 1 (One.one.{max u3 u1} (Matrix.{u3, u3, u1} m m α) (Matrix.hasOne.{u1, u3} m α (fun (a : m) (b : m) => _inst_3 a b) _inst_1 _inst_2)))) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} l m) (fun (_x : Function.Embedding.{succ u2, succ u3} l m) => l -> m) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} l m) e) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} l m) (fun (_x : Function.Embedding.{succ u2, succ u3} l m) => l -> m) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} l m) e)) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} l l α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} l l α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} l l α) (Matrix.hasOne.{u1, u2} l α (fun (a : l) (b : l) => _inst_4 a b) _inst_1 _inst_2))))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_2 : One.{u3} α] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : DecidableEq.{succ u1} l] (e : Function.Embedding.{succ u1, succ u2} l m), Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} l l α) (Matrix.submatrix.{u3, u1, u2, u2, u1} l m m l α (OfNat.ofNat.{max u3 u2} (Matrix.{u2, u2, u3} m m α) 1 (One.toOfNat1.{max u3 u2} (Matrix.{u2, u2, u3} m m α) (Matrix.one.{u3, u2} m α (fun (a : m) (b : m) => _inst_3 a b) _inst_1 _inst_2))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : l) => m) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l m (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} l m)) e) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : l) => m) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} l m) l m (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} l m)) e)) (OfNat.ofNat.{max u3 u1} (Matrix.{u1, u1, u3} l l α) 1 (One.toOfNat1.{max u3 u1} (Matrix.{u1, u1, u3} l l α) (Matrix.one.{u3, u1} l α (fun (a : l) (b : l) => _inst_4 a b) _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_one_embedding Matrix.submatrix_one_embeddingₓ'. -/
@[simp]
theorem submatrix_one_embedding [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.Injective
#align matrix.submatrix_one_embedding Matrix.submatrix_one_embedding

/- warning: matrix.submatrix_one_equiv -> Matrix.submatrix_one_equiv is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : DecidableEq.{succ u3} m] [_inst_4 : DecidableEq.{succ u2} l] (e : Equiv.{succ u2, succ u3} l m), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} l l α) (Matrix.submatrix.{u1, u2, u3, u3, u2} l m m l α (OfNat.ofNat.{max u3 u1} (Matrix.{u3, u3, u1} m m α) 1 (OfNat.mk.{max u3 u1} (Matrix.{u3, u3, u1} m m α) 1 (One.one.{max u3 u1} (Matrix.{u3, u3, u1} m m α) (Matrix.hasOne.{u1, u3} m α (fun (a : m) (b : m) => _inst_3 a b) _inst_1 _inst_2)))) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} l m) (fun (_x : Equiv.{succ u2, succ u3} l m) => l -> m) (Equiv.hasCoeToFun.{succ u2, succ u3} l m) e) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} l m) (fun (_x : Equiv.{succ u2, succ u3} l m) => l -> m) (Equiv.hasCoeToFun.{succ u2, succ u3} l m) e)) (OfNat.ofNat.{max u2 u1} (Matrix.{u2, u2, u1} l l α) 1 (OfNat.mk.{max u2 u1} (Matrix.{u2, u2, u1} l l α) 1 (One.one.{max u2 u1} (Matrix.{u2, u2, u1} l l α) (Matrix.hasOne.{u1, u2} l α (fun (a : l) (b : l) => _inst_4 a b) _inst_1 _inst_2))))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {α : Type.{u3}} [_inst_1 : Zero.{u3} α] [_inst_2 : One.{u3} α] [_inst_3 : DecidableEq.{succ u2} m] [_inst_4 : DecidableEq.{succ u1} l] (e : Equiv.{succ u1, succ u2} l m), Eq.{max (succ u3) (succ u1)} (Matrix.{u1, u1, u3} l l α) (Matrix.submatrix.{u3, u1, u2, u2, u1} l m m l α (OfNat.ofNat.{max u3 u2} (Matrix.{u2, u2, u3} m m α) 1 (One.toOfNat1.{max u3 u2} (Matrix.{u2, u2, u3} m m α) (Matrix.one.{u3, u2} m α (fun (a : m) (b : m) => _inst_3 a b) _inst_1 _inst_2))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : l) => m) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} l m) e) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : l) => m) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} l m) e)) (OfNat.ofNat.{max u3 u1} (Matrix.{u1, u1, u3} l l α) 1 (One.toOfNat1.{max u3 u1} (Matrix.{u1, u1, u3} l l α) (Matrix.one.{u3, u1} l α (fun (a : l) (b : l) => _inst_4 a b) _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_one_equiv Matrix.submatrix_one_equivₓ'. -/
@[simp]
theorem submatrix_one_equiv [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.Injective
#align matrix.submatrix_one_equiv Matrix.submatrix_one_equiv

/- warning: matrix.submatrix_mul_equiv -> Matrix.submatrix_mul_equiv is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Fintype.{u4} n] [_inst_2 : Fintype.{u5} o] [_inst_3 : AddCommMonoid.{u1} α] [_inst_4 : Mul.{u1} α] {p : Type.{u6}} {q : Type.{u7}} (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u4, u6, u1} n p α) (e₁ : l -> m) (e₂ : Equiv.{succ u5, succ u4} o n) (e₃ : q -> p), Eq.{succ (max u2 u7 u1)} (Matrix.{u2, u7, u1} l q α) (Matrix.mul.{u1, u2, u5, u7} l o q α _inst_2 _inst_4 _inst_3 (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α M e₁ (coeFn.{max 1 (max (succ u5) (succ u4)) (succ u4) (succ u5), max (succ u5) (succ u4)} (Equiv.{succ u5, succ u4} o n) (fun (_x : Equiv.{succ u5, succ u4} o n) => o -> n) (Equiv.hasCoeToFun.{succ u5, succ u4} o n) e₂)) (Matrix.submatrix.{u1, u5, u4, u6, u7} o n p q α N (coeFn.{max 1 (max (succ u5) (succ u4)) (succ u4) (succ u5), max (succ u5) (succ u4)} (Equiv.{succ u5, succ u4} o n) (fun (_x : Equiv.{succ u5, succ u4} o n) => o -> n) (Equiv.hasCoeToFun.{succ u5, succ u4} o n) e₂) e₃)) (Matrix.submatrix.{u1, u2, u3, u6, u7} l m p q α (Matrix.mul.{u1, u3, u4, u6} m n p α _inst_1 _inst_4 _inst_3 M N) e₁ e₃)
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u6}} {o : Type.{u5}} {α : Type.{u7}} [_inst_1 : Fintype.{u6} n] [_inst_2 : Fintype.{u5} o] [_inst_3 : AddCommMonoid.{u7} α] [_inst_4 : Mul.{u7} α] {p : Type.{u4}} {q : Type.{u3}} (M : Matrix.{u2, u6, u7} m n α) (N : Matrix.{u6, u4, u7} n p α) (e₁ : l -> m) (e₂ : Equiv.{succ u5, succ u6} o n) (e₃ : q -> p), Eq.{max (max (succ u7) (succ u1)) (succ u3)} (Matrix.{u1, u3, u7} l q α) (Matrix.mul.{u7, u1, u5, u3} l o q α _inst_2 _inst_4 _inst_3 (Matrix.submatrix.{u7, u1, u2, u6, u5} l m n o α M e₁ (FunLike.coe.{max (succ u6) (succ u5), succ u5, succ u6} (Equiv.{succ u5, succ u6} o n) o (fun (_x : o) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : o) => n) _x) (Equiv.instFunLikeEquiv.{succ u5, succ u6} o n) e₂)) (Matrix.submatrix.{u7, u5, u6, u4, u3} o n p q α N (FunLike.coe.{max (succ u6) (succ u5), succ u5, succ u6} (Equiv.{succ u5, succ u6} o n) o (fun (_x : o) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : o) => n) _x) (Equiv.instFunLikeEquiv.{succ u5, succ u6} o n) e₂) e₃)) (Matrix.submatrix.{u7, u1, u2, u4, u3} l m p q α (Matrix.mul.{u7, u2, u6, u4} m n p α _inst_1 _inst_4 _inst_3 M N) e₁ e₃)
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_mul_equiv Matrix.submatrix_mul_equivₓ'. -/
@[simp]
theorem submatrix_mul_equiv [Fintype n] [Fintype o] [AddCommMonoid α] [Mul α] {p q : Type _}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p) :
    M.submatrix e₁ e₂ ⬝ N.submatrix e₂ e₃ = (M ⬝ N).submatrix e₁ e₃ :=
  (submatrix_mul M N e₁ e₂ e₃ e₂.Bijective).symm
#align matrix.submatrix_mul_equiv Matrix.submatrix_mul_equiv

/- warning: matrix.mul_submatrix_one -> Matrix.mul_submatrix_one is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Fintype.{u4} n] [_inst_2 : Fintype.{u5} o] [_inst_3 : NonAssocSemiring.{u1} α] [_inst_4 : DecidableEq.{succ u5} o] (e₁ : Equiv.{succ u4, succ u5} n o) (e₂ : l -> o) (M : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} m l α) (Matrix.mul.{u1, u3, u4, u2} m n l α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) M (Matrix.submatrix.{u1, u4, u5, u5, u2} n o o l α (OfNat.ofNat.{max u5 u1} (Matrix.{u5, u5, u1} o o α) 1 (OfNat.mk.{max u5 u1} (Matrix.{u5, u5, u1} o o α) 1 (One.one.{max u5 u1} (Matrix.{u5, u5, u1} o o α) (Matrix.hasOne.{u1, u5} o α (fun (a : o) (b : o) => _inst_4 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_3))))))) (coeFn.{max 1 (max (succ u4) (succ u5)) (succ u5) (succ u4), max (succ u4) (succ u5)} (Equiv.{succ u4, succ u5} n o) (fun (_x : Equiv.{succ u4, succ u5} n o) => n -> o) (Equiv.hasCoeToFun.{succ u4, succ u5} n o) e₁) e₂)) (Matrix.submatrix.{u1, u3, u3, u4, u2} m m n l α M (id.{succ u3} m) (Function.comp.{succ u2, succ u5, succ u4} l o n (coeFn.{max 1 (max (succ u5) (succ u4)) (succ u4) (succ u5), max (succ u5) (succ u4)} (Equiv.{succ u5, succ u4} o n) (fun (_x : Equiv.{succ u5, succ u4} o n) => o -> n) (Equiv.hasCoeToFun.{succ u5, succ u4} o n) (Equiv.symm.{succ u4, succ u5} n o e₁)) e₂))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u2}} {n : Type.{u4}} {o : Type.{u3}} {α : Type.{u5}} [_inst_1 : Fintype.{u4} n] [_inst_2 : Fintype.{u3} o] [_inst_3 : NonAssocSemiring.{u5} α] [_inst_4 : DecidableEq.{succ u3} o] (e₁ : Equiv.{succ u4, succ u3} n o) (e₂ : l -> o) (M : Matrix.{u2, u4, u5} m n α), Eq.{max (max (succ u5) (succ u1)) (succ u2)} (Matrix.{u2, u1, u5} m l α) (Matrix.mul.{u5, u2, u4, u1} m n l α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_3)) M (Matrix.submatrix.{u5, u4, u3, u3, u1} n o o l α (OfNat.ofNat.{max u5 u3} (Matrix.{u3, u3, u5} o o α) 1 (One.toOfNat1.{max u5 u3} (Matrix.{u3, u3, u5} o o α) (Matrix.one.{u5, u3} o α (fun (a : o) (b : o) => _inst_4 a b) (MulZeroOneClass.toZero.{u5} α (NonAssocSemiring.toMulZeroOneClass.{u5} α _inst_3)) (NonAssocSemiring.toOne.{u5} α _inst_3)))) (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Equiv.{succ u4, succ u3} n o) n (fun (_x : n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : n) => o) _x) (Equiv.instFunLikeEquiv.{succ u4, succ u3} n o) e₁) e₂)) (Matrix.submatrix.{u5, u2, u2, u4, u1} m m n l α M (id.{succ u2} m) (Function.comp.{succ u1, succ u3, succ u4} l o n (FunLike.coe.{max (succ u4) (succ u3), succ u3, succ u4} (Equiv.{succ u3, succ u4} o n) o (fun (_x : o) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : o) => n) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u4} o n) (Equiv.symm.{succ u4, succ u3} n o e₁)) e₂))
Case conversion may be inaccurate. Consider using '#align matrix.mul_submatrix_one Matrix.mul_submatrix_oneₓ'. -/
theorem mul_submatrix_one [Fintype n] [Fintype o] [NonAssocSemiring α] [DecidableEq o] (e₁ : n ≃ o)
    (e₂ : l → o) (M : Matrix m n α) :
    M ⬝ (1 : Matrix o o α).submatrix e₁ e₂ = submatrix M id (e₁.symm ∘ e₂) :=
  by
  let A := M.submatrix id e₁.symm
  have : M = A.submatrix id e₁ := by
    simp only [submatrix_submatrix, Function.comp.right_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this, submatrix_mul_equiv]
  simp only [Matrix.mul_one, submatrix_submatrix, Function.comp.right_id, submatrix_id_id,
    Equiv.symm_comp_self]
#align matrix.mul_submatrix_one Matrix.mul_submatrix_one

/- warning: matrix.one_submatrix_mul -> Matrix.one_submatrix_mul is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} m] [_inst_2 : Fintype.{u5} o] [_inst_3 : NonAssocSemiring.{u1} α] [_inst_4 : DecidableEq.{succ u5} o] (e₁ : l -> o) (e₂ : Equiv.{succ u3, succ u5} m o) (M : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u2 u4 u1)} (Matrix.{u2, u4, u1} l n α) (Matrix.mul.{u1, u2, u3, u4} l m n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3)) (Matrix.submatrix.{u1, u2, u5, u5, u3} l o o m α (OfNat.ofNat.{max u5 u1} (Matrix.{u5, u5, u1} o o α) 1 (OfNat.mk.{max u5 u1} (Matrix.{u5, u5, u1} o o α) 1 (One.one.{max u5 u1} (Matrix.{u5, u5, u1} o o α) (Matrix.hasOne.{u1, u5} o α (fun (a : o) (b : o) => _inst_4 a b) (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_3))) (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_3))))))) e₁ (coeFn.{max 1 (max (succ u3) (succ u5)) (succ u5) (succ u3), max (succ u3) (succ u5)} (Equiv.{succ u3, succ u5} m o) (fun (_x : Equiv.{succ u3, succ u5} m o) => m -> o) (Equiv.hasCoeToFun.{succ u3, succ u5} m o) e₂)) M) (Matrix.submatrix.{u1, u2, u3, u4, u4} l m n n α M (Function.comp.{succ u2, succ u5, succ u3} l o m (coeFn.{max 1 (max (succ u5) (succ u3)) (succ u3) (succ u5), max (succ u5) (succ u3)} (Equiv.{succ u5, succ u3} o m) (fun (_x : Equiv.{succ u5, succ u3} o m) => o -> m) (Equiv.hasCoeToFun.{succ u5, succ u3} o m) (Equiv.symm.{succ u3, succ u5} m o e₂)) e₁) (id.{succ u4} n))
but is expected to have type
  forall {l : Type.{u1}} {m : Type.{u4}} {n : Type.{u2}} {o : Type.{u3}} {α : Type.{u5}} [_inst_1 : Fintype.{u4} m] [_inst_2 : Fintype.{u3} o] [_inst_3 : NonAssocSemiring.{u5} α] [_inst_4 : DecidableEq.{succ u3} o] (e₁ : l -> o) (e₂ : Equiv.{succ u4, succ u3} m o) (M : Matrix.{u4, u2, u5} m n α), Eq.{max (max (succ u5) (succ u1)) (succ u2)} (Matrix.{u1, u2, u5} l n α) (Matrix.mul.{u5, u1, u4, u2} l m n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} α _inst_3)) (Matrix.submatrix.{u5, u1, u3, u3, u4} l o o m α (OfNat.ofNat.{max u5 u3} (Matrix.{u3, u3, u5} o o α) 1 (One.toOfNat1.{max u5 u3} (Matrix.{u3, u3, u5} o o α) (Matrix.one.{u5, u3} o α (fun (a : o) (b : o) => _inst_4 a b) (MulZeroOneClass.toZero.{u5} α (NonAssocSemiring.toMulZeroOneClass.{u5} α _inst_3)) (NonAssocSemiring.toOne.{u5} α _inst_3)))) e₁ (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Equiv.{succ u4, succ u3} m o) m (fun (_x : m) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m) => o) _x) (Equiv.instFunLikeEquiv.{succ u4, succ u3} m o) e₂)) M) (Matrix.submatrix.{u5, u1, u4, u2, u2} l m n n α M (Function.comp.{succ u1, succ u3, succ u4} l o m (FunLike.coe.{max (succ u4) (succ u3), succ u3, succ u4} (Equiv.{succ u3, succ u4} o m) o (fun (_x : o) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : o) => m) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u4} o m) (Equiv.symm.{succ u4, succ u3} m o e₂)) e₁) (id.{succ u2} n))
Case conversion may be inaccurate. Consider using '#align matrix.one_submatrix_mul Matrix.one_submatrix_mulₓ'. -/
theorem one_submatrix_mul [Fintype m] [Fintype o] [NonAssocSemiring α] [DecidableEq o] (e₁ : l → o)
    (e₂ : m ≃ o) (M : Matrix m n α) :
    ((1 : Matrix o o α).submatrix e₁ e₂).mul M = submatrix M (e₂.symm ∘ e₁) id :=
  by
  let A := M.submatrix e₂.symm id
  have : M = A.submatrix e₂ id := by
    simp only [submatrix_submatrix, Function.comp.right_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this, submatrix_mul_equiv]
  simp only [Matrix.one_mul, submatrix_submatrix, Function.comp.right_id, submatrix_id_id,
    Equiv.symm_comp_self]
#align matrix.one_submatrix_mul Matrix.one_submatrix_mul

#print Matrix.reindex /-
/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : Matrix m n α ≃ Matrix l o α
    where
  toFun M := M.submatrix eₘ.symm eₙ.symm
  invFun M := M.submatrix eₘ eₙ
  left_inv M := by simp
  right_inv M := by simp
#align matrix.reindex Matrix.reindex
-/

/- warning: matrix.reindex_apply -> Matrix.reindex_apply is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} (eₘ : Equiv.{succ u3, succ u2} m l) (eₙ : Equiv.{succ u4, succ u5} n o) (M : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u2 u5 u1)} (Matrix.{u2, u5, u1} l o α) (coeFn.{max 1 (max (succ (max u3 u4 u1)) (succ (max u2 u5 u1))) (succ (max u2 u5 u1)) (succ (max u3 u4 u1)), max (succ (max u3 u4 u1)) (succ (max u2 u5 u1))} (Equiv.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) (fun (_x : Equiv.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) => (Matrix.{u3, u4, u1} m n α) -> (Matrix.{u2, u5, u1} l o α)) (Equiv.hasCoeToFun.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) (Matrix.reindex.{u1, u2, u3, u4, u5} l m n o α eₘ eₙ) M) (Matrix.submatrix.{u1, u2, u3, u4, u5} l m n o α M (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} l m) (fun (_x : Equiv.{succ u2, succ u3} l m) => l -> m) (Equiv.hasCoeToFun.{succ u2, succ u3} l m) (Equiv.symm.{succ u3, succ u2} m l eₘ)) (coeFn.{max 1 (max (succ u5) (succ u4)) (succ u4) (succ u5), max (succ u5) (succ u4)} (Equiv.{succ u5, succ u4} o n) (fun (_x : Equiv.{succ u5, succ u4} o n) => o -> n) (Equiv.hasCoeToFun.{succ u5, succ u4} o n) (Equiv.symm.{succ u4, succ u5} n o eₙ)))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u5}} (eₘ : Equiv.{succ u4, succ u3} m l) (eₙ : Equiv.{succ u2, succ u1} n o) (M : Matrix.{u4, u2, u5} m n α), Eq.{max (max (succ u5) (succ u3)) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u4, u2, u5} m n α) => Matrix.{u3, u1, u5} l o α) M) (FunLike.coe.{max (max (max (max (succ u3) (succ u4)) (succ u2)) (succ u1)) (succ u5), max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Equiv.{max (max (succ u5) (succ u2)) (succ u4), max (max (succ u5) (succ u1)) (succ u3)} (Matrix.{u4, u2, u5} m n α) (Matrix.{u3, u1, u5} l o α)) (Matrix.{u4, u2, u5} m n α) (fun (_x : Matrix.{u4, u2, u5} m n α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u4, u2, u5} m n α) => Matrix.{u3, u1, u5} l o α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Matrix.{u4, u2, u5} m n α) (Matrix.{u3, u1, u5} l o α)) (Matrix.reindex.{u5, u3, u4, u2, u1} l m n o α eₘ eₙ) M) (Matrix.submatrix.{u5, u3, u4, u2, u1} l m n o α M (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (Equiv.{succ u3, succ u4} l m) l (fun (_x : l) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : l) => m) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u4} l m) (Equiv.symm.{succ u4, succ u3} m l eₘ)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} o n) o (fun (_x : o) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : o) => n) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} o n) (Equiv.symm.{succ u2, succ u1} n o eₙ)))
Case conversion may be inaccurate. Consider using '#align matrix.reindex_apply Matrix.reindex_applyₓ'. -/
@[simp]
theorem reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm :=
  rfl
#align matrix.reindex_apply Matrix.reindex_apply

/- warning: matrix.reindex_refl_refl -> Matrix.reindex_refl_refl is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} (A : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (coeFn.{succ (max u2 u3 u1), succ (max u2 u3 u1)} (Equiv.{succ (max u2 u3 u1), succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α)) (fun (_x : Equiv.{succ (max u2 u3 u1), succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α)) => (Matrix.{u2, u3, u1} m n α) -> (Matrix.{u2, u3, u1} m n α)) (Equiv.hasCoeToFun.{succ (max u2 u3 u1), succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.{u2, u3, u1} m n α)) (Matrix.reindex.{u1, u2, u2, u3, u3} m m n n α (Equiv.refl.{succ u2} m) (Equiv.refl.{succ u3} n)) A) A
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} (A : Matrix.{u2, u1, u3} m n α), Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u2, u1, u3} m n α) => Matrix.{u2, u1, u3} m n α) A) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u3) (succ u1)) (succ u2), max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α)) (Matrix.{u2, u1, u3} m n α) (fun (_x : Matrix.{u2, u1, u3} m n α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u2, u1, u3} m n α) => Matrix.{u2, u1, u3} m n α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Matrix.{u2, u1, u3} m n α) (Matrix.{u2, u1, u3} m n α)) (Matrix.reindex.{u3, u2, u2, u1, u1} m m n n α (Equiv.refl.{succ u2} m) (Equiv.refl.{succ u1} n)) A) A
Case conversion may be inaccurate. Consider using '#align matrix.reindex_refl_refl Matrix.reindex_refl_reflₓ'. -/
@[simp]
theorem reindex_refl_refl (A : Matrix m n α) : reindex (Equiv.refl _) (Equiv.refl _) A = A :=
  A.submatrix_id_id
#align matrix.reindex_refl_refl Matrix.reindex_refl_refl

/- warning: matrix.reindex_symm -> Matrix.reindex_symm is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} (eₘ : Equiv.{succ u3, succ u2} m l) (eₙ : Equiv.{succ u4, succ u5} n o), Eq.{max 1 (max (succ (max u2 u5 u1)) (succ (max u3 u4 u1))) (succ (max u3 u4 u1)) (succ (max u2 u5 u1))} (Equiv.{succ (max u2 u5 u1), succ (max u3 u4 u1)} (Matrix.{u2, u5, u1} l o α) (Matrix.{u3, u4, u1} m n α)) (Equiv.symm.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α) (Matrix.reindex.{u1, u2, u3, u4, u5} l m n o α eₘ eₙ)) (Matrix.reindex.{u1, u3, u2, u5, u4} m l o n α (Equiv.symm.{succ u3, succ u2} m l eₘ) (Equiv.symm.{succ u4, succ u5} n o eₙ))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u5}} (eₘ : Equiv.{succ u4, succ u3} m l) (eₙ : Equiv.{succ u2, succ u1} n o), Eq.{max (max (max (max (succ u5) (succ u3)) (succ u4)) (succ u2)) (succ u1)} (Equiv.{max (max (succ u3) (succ u1)) (succ u5), max (max (succ u4) (succ u2)) (succ u5)} (Matrix.{u3, u1, u5} l o α) (Matrix.{u4, u2, u5} m n α)) (Equiv.symm.{max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Matrix.{u4, u2, u5} m n α) (Matrix.{u3, u1, u5} l o α) (Matrix.reindex.{u5, u3, u4, u2, u1} l m n o α eₘ eₙ)) (Matrix.reindex.{u5, u4, u3, u1, u2} m l o n α (Equiv.symm.{succ u4, succ u3} m l eₘ) (Equiv.symm.{succ u2, succ u1} n o eₙ))
Case conversion may be inaccurate. Consider using '#align matrix.reindex_symm Matrix.reindex_symmₓ'. -/
@[simp]
theorem reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : Matrix l o α ≃ _) :=
  rfl
#align matrix.reindex_symm Matrix.reindex_symm

/- warning: matrix.reindex_trans -> Matrix.reindex_trans is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} {l₂ : Type.{u6}} {o₂ : Type.{u7}} (eₘ : Equiv.{succ u3, succ u2} m l) (eₙ : Equiv.{succ u4, succ u5} n o) (eₘ₂ : Equiv.{succ u2, succ u6} l l₂) (eₙ₂ : Equiv.{succ u5, succ u7} o o₂), Eq.{max 1 (max (succ (max u3 u4 u1)) (succ (max u6 u7 u1))) (succ (max u6 u7 u1)) (succ (max u3 u4 u1))} (Equiv.{succ (max u3 u4 u1), succ (max u6 u7 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u6, u7, u1} l₂ o₂ α)) (Equiv.trans.{succ (max u3 u4 u1), succ (max u2 u5 u1), succ (max u6 u7 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α) (Matrix.{u6, u7, u1} l₂ o₂ α) (Matrix.reindex.{u1, u2, u3, u4, u5} l m n o α eₘ eₙ) (Matrix.reindex.{u1, u6, u2, u5, u7} l₂ l o o₂ α eₘ₂ eₙ₂)) (Matrix.reindex.{u1, u6, u3, u4, u7} l₂ m n o₂ α (Equiv.trans.{succ u3, succ u2, succ u6} m l l₂ eₘ eₘ₂) (Equiv.trans.{succ u4, succ u5, succ u7} n o o₂ eₙ eₙ₂))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u7}} {l₂ : Type.{u6}} {o₂ : Type.{u5}} (eₘ : Equiv.{succ u4, succ u3} m l) (eₙ : Equiv.{succ u2, succ u1} n o) (eₘ₂ : Equiv.{succ u3, succ u6} l l₂) (eₙ₂ : Equiv.{succ u1, succ u5} o o₂), Eq.{max (max (max (max (succ u7) (succ u4)) (succ u2)) (succ u6)) (succ u5)} (Equiv.{max (max (succ u4) (succ u2)) (succ u7), max (max (succ u5) (succ u6)) (succ u7)} (Matrix.{u4, u2, u7} m n α) (Matrix.{u6, u5, u7} l₂ o₂ α)) (Equiv.trans.{max (max (succ u4) (succ u2)) (succ u7), max (max (succ u3) (succ u1)) (succ u7), max (max (succ u5) (succ u6)) (succ u7)} (Matrix.{u4, u2, u7} m n α) (Matrix.{u3, u1, u7} l o α) (Matrix.{u6, u5, u7} l₂ o₂ α) (Matrix.reindex.{u7, u3, u4, u2, u1} l m n o α eₘ eₙ) (Matrix.reindex.{u7, u6, u3, u1, u5} l₂ l o o₂ α eₘ₂ eₙ₂)) (Matrix.reindex.{u7, u6, u4, u2, u5} l₂ m n o₂ α (Equiv.trans.{succ u4, succ u3, succ u6} m l l₂ eₘ eₘ₂) (Equiv.trans.{succ u2, succ u1, succ u5} n o o₂ eₙ eₙ₂))
Case conversion may be inaccurate. Consider using '#align matrix.reindex_trans Matrix.reindex_transₓ'. -/
@[simp]
theorem reindex_trans {l₂ o₂ : Type _} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
    (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) =
      (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) :=
  Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm : _)
#align matrix.reindex_trans Matrix.reindex_trans

/- warning: matrix.transpose_reindex -> Matrix.transpose_reindex is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} (eₘ : Equiv.{succ u3, succ u2} m l) (eₙ : Equiv.{succ u4, succ u5} n o) (M : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u5 u2 u1)} (Matrix.{u5, u2, u1} o l α) (Matrix.transpose.{u1, u2, u5} l o α (coeFn.{max 1 (max (succ (max u3 u4 u1)) (succ (max u2 u5 u1))) (succ (max u2 u5 u1)) (succ (max u3 u4 u1)), max (succ (max u3 u4 u1)) (succ (max u2 u5 u1))} (Equiv.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) (fun (_x : Equiv.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) => (Matrix.{u3, u4, u1} m n α) -> (Matrix.{u2, u5, u1} l o α)) (Equiv.hasCoeToFun.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) (Matrix.reindex.{u1, u2, u3, u4, u5} l m n o α eₘ eₙ) M)) (coeFn.{max 1 (max (succ (max u4 u3 u1)) (succ (max u5 u2 u1))) (succ (max u5 u2 u1)) (succ (max u4 u3 u1)), max (succ (max u4 u3 u1)) (succ (max u5 u2 u1))} (Equiv.{succ (max u4 u3 u1), succ (max u5 u2 u1)} (Matrix.{u4, u3, u1} n m α) (Matrix.{u5, u2, u1} o l α)) (fun (_x : Equiv.{succ (max u4 u3 u1), succ (max u5 u2 u1)} (Matrix.{u4, u3, u1} n m α) (Matrix.{u5, u2, u1} o l α)) => (Matrix.{u4, u3, u1} n m α) -> (Matrix.{u5, u2, u1} o l α)) (Equiv.hasCoeToFun.{succ (max u4 u3 u1), succ (max u5 u2 u1)} (Matrix.{u4, u3, u1} n m α) (Matrix.{u5, u2, u1} o l α)) (Matrix.reindex.{u1, u5, u4, u3, u2} o n m l α eₙ eₘ) (Matrix.transpose.{u1, u3, u4} m n α M))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u5}} (eₘ : Equiv.{succ u4, succ u3} m l) (eₙ : Equiv.{succ u2, succ u1} n o) (M : Matrix.{u4, u2, u5} m n α), Eq.{max (max (succ u5) (succ u3)) (succ u1)} (Matrix.{u1, u3, u5} o l α) (Matrix.transpose.{u5, u3, u1} l o α (FunLike.coe.{max (max (max (max (succ u3) (succ u4)) (succ u2)) (succ u1)) (succ u5), max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Equiv.{max (max (succ u5) (succ u2)) (succ u4), max (max (succ u5) (succ u1)) (succ u3)} (Matrix.{u4, u2, u5} m n α) (Matrix.{u3, u1, u5} l o α)) (Matrix.{u4, u2, u5} m n α) (fun (_x : Matrix.{u4, u2, u5} m n α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u4, u2, u5} m n α) => Matrix.{u3, u1, u5} l o α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Matrix.{u4, u2, u5} m n α) (Matrix.{u3, u1, u5} l o α)) (Matrix.reindex.{u5, u3, u4, u2, u1} l m n o α eₘ eₙ) M)) (FunLike.coe.{max (max (max (max (succ u3) (succ u4)) (succ u2)) (succ u1)) (succ u5), max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Equiv.{max (max (succ u5) (succ u4)) (succ u2), max (max (succ u5) (succ u3)) (succ u1)} (Matrix.{u2, u4, u5} n m α) (Matrix.{u1, u3, u5} o l α)) (Matrix.{u2, u4, u5} n m α) (fun (_x : Matrix.{u2, u4, u5} n m α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u2, u4, u5} n m α) => Matrix.{u1, u3, u5} o l α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Matrix.{u2, u4, u5} n m α) (Matrix.{u1, u3, u5} o l α)) (Matrix.reindex.{u5, u1, u2, u4, u3} o n m l α eₙ eₘ) (Matrix.transpose.{u5, u4, u2} m n α M))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_reindex Matrix.transpose_reindexₓ'. -/
theorem transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ :=
  rfl
#align matrix.transpose_reindex Matrix.transpose_reindex

/- warning: matrix.conj_transpose_reindex -> Matrix.conjTranspose_reindex is a dubious translation:
lean 3 declaration is
  forall {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} [_inst_1 : Star.{u1} α] (eₘ : Equiv.{succ u3, succ u2} m l) (eₙ : Equiv.{succ u4, succ u5} n o) (M : Matrix.{u3, u4, u1} m n α), Eq.{succ (max u5 u2 u1)} (Matrix.{u5, u2, u1} o l α) (Matrix.conjTranspose.{u1, u2, u5} l o α _inst_1 (coeFn.{max 1 (max (succ (max u3 u4 u1)) (succ (max u2 u5 u1))) (succ (max u2 u5 u1)) (succ (max u3 u4 u1)), max (succ (max u3 u4 u1)) (succ (max u2 u5 u1))} (Equiv.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) (fun (_x : Equiv.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) => (Matrix.{u3, u4, u1} m n α) -> (Matrix.{u2, u5, u1} l o α)) (Equiv.hasCoeToFun.{succ (max u3 u4 u1), succ (max u2 u5 u1)} (Matrix.{u3, u4, u1} m n α) (Matrix.{u2, u5, u1} l o α)) (Matrix.reindex.{u1, u2, u3, u4, u5} l m n o α eₘ eₙ) M)) (coeFn.{max 1 (max (succ (max u4 u3 u1)) (succ (max u5 u2 u1))) (succ (max u5 u2 u1)) (succ (max u4 u3 u1)), max (succ (max u4 u3 u1)) (succ (max u5 u2 u1))} (Equiv.{succ (max u4 u3 u1), succ (max u5 u2 u1)} (Matrix.{u4, u3, u1} n m α) (Matrix.{u5, u2, u1} o l α)) (fun (_x : Equiv.{succ (max u4 u3 u1), succ (max u5 u2 u1)} (Matrix.{u4, u3, u1} n m α) (Matrix.{u5, u2, u1} o l α)) => (Matrix.{u4, u3, u1} n m α) -> (Matrix.{u5, u2, u1} o l α)) (Equiv.hasCoeToFun.{succ (max u4 u3 u1), succ (max u5 u2 u1)} (Matrix.{u4, u3, u1} n m α) (Matrix.{u5, u2, u1} o l α)) (Matrix.reindex.{u1, u5, u4, u3, u2} o n m l α eₙ eₘ) (Matrix.conjTranspose.{u1, u3, u4} m n α _inst_1 M))
but is expected to have type
  forall {l : Type.{u3}} {m : Type.{u4}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u5}} [_inst_1 : Star.{u5} α] (eₘ : Equiv.{succ u4, succ u3} m l) (eₙ : Equiv.{succ u2, succ u1} n o) (M : Matrix.{u4, u2, u5} m n α), Eq.{max (max (succ u5) (succ u3)) (succ u1)} (Matrix.{u1, u3, u5} o l α) (Matrix.conjTranspose.{u5, u3, u1} l o α _inst_1 (FunLike.coe.{max (max (max (max (succ u3) (succ u4)) (succ u2)) (succ u1)) (succ u5), max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Equiv.{max (max (succ u5) (succ u2)) (succ u4), max (max (succ u5) (succ u1)) (succ u3)} (Matrix.{u4, u2, u5} m n α) (Matrix.{u3, u1, u5} l o α)) (Matrix.{u4, u2, u5} m n α) (fun (_x : Matrix.{u4, u2, u5} m n α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u4, u2, u5} m n α) => Matrix.{u3, u1, u5} l o α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Matrix.{u4, u2, u5} m n α) (Matrix.{u3, u1, u5} l o α)) (Matrix.reindex.{u5, u3, u4, u2, u1} l m n o α eₘ eₙ) M)) (FunLike.coe.{max (max (max (max (succ u3) (succ u4)) (succ u2)) (succ u1)) (succ u5), max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Equiv.{max (max (succ u5) (succ u4)) (succ u2), max (max (succ u5) (succ u3)) (succ u1)} (Matrix.{u2, u4, u5} n m α) (Matrix.{u1, u3, u5} o l α)) (Matrix.{u2, u4, u5} n m α) (fun (_x : Matrix.{u2, u4, u5} n m α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Matrix.{u2, u4, u5} n m α) => Matrix.{u1, u3, u5} o l α) _x) (Equiv.instFunLikeEquiv.{max (max (succ u4) (succ u2)) (succ u5), max (max (succ u3) (succ u1)) (succ u5)} (Matrix.{u2, u4, u5} n m α) (Matrix.{u1, u3, u5} o l α)) (Matrix.reindex.{u5, u1, u2, u4, u3} o n m l α eₙ eₘ) (Matrix.conjTranspose.{u5, u4, u2} m n α _inst_1 M))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_reindex Matrix.conjTranspose_reindexₓ'. -/
theorem conjTranspose_reindex [Star α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ :=
  rfl
#align matrix.conj_transpose_reindex Matrix.conjTranspose_reindex

/- warning: matrix.submatrix_mul_transpose_submatrix -> Matrix.submatrix_mul_transpose_submatrix is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u3} n] [_inst_3 : AddCommMonoid.{u1} α] [_inst_4 : Mul.{u1} α] (e : Equiv.{succ u2, succ u3} m n) (M : Matrix.{u2, u3, u1} m n α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} m m α) (Matrix.mul.{u1, u2, u2, u2} m m m α _inst_1 _inst_4 _inst_3 (Matrix.submatrix.{u1, u2, u2, u3, u2} m m n m α M (id.{succ u2} m) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} m n) (fun (_x : Equiv.{succ u2, succ u3} m n) => m -> n) (Equiv.hasCoeToFun.{succ u2, succ u3} m n) e)) (Matrix.submatrix.{u1, u2, u3, u2, u2} m n m m α (Matrix.transpose.{u1, u2, u3} m n α M) (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} m n) (fun (_x : Equiv.{succ u2, succ u3} m n) => m -> n) (Equiv.hasCoeToFun.{succ u2, succ u3} m n) e) (id.{succ u2} m))) (Matrix.mul.{u1, u2, u3, u2} m n m α _inst_2 _inst_4 _inst_3 M (Matrix.transpose.{u1, u2, u3} m n α M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : Fintype.{u1} n] [_inst_3 : AddCommMonoid.{u3} α] [_inst_4 : Mul.{u3} α] (e : Equiv.{succ u2, succ u1} m n) (M : Matrix.{u2, u1, u3} m n α), Eq.{max (succ u3) (succ u2)} (Matrix.{u2, u2, u3} m m α) (Matrix.mul.{u3, u2, u2, u2} m m m α _inst_1 _inst_4 _inst_3 (Matrix.submatrix.{u3, u2, u2, u1, u2} m m n m α M (id.{succ u2} m) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} m n) m (fun (_x : m) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m) => n) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} m n) e)) (Matrix.submatrix.{u3, u2, u1, u2, u2} m n m m α (Matrix.transpose.{u3, u2, u1} m n α M) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} m n) m (fun (_x : m) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : m) => n) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} m n) e) (id.{succ u2} m))) (Matrix.mul.{u3, u2, u1, u2} m n m α _inst_2 _inst_4 _inst_3 M (Matrix.transpose.{u3, u2, u1} m n α M))
Case conversion may be inaccurate. Consider using '#align matrix.submatrix_mul_transpose_submatrix Matrix.submatrix_mul_transpose_submatrixₓ'. -/
@[simp]
theorem submatrix_mul_transpose_submatrix [Fintype m] [Fintype n] [AddCommMonoid α] [Mul α]
    (e : m ≃ n) (M : Matrix m n α) : M.submatrix id e ⬝ Mᵀ.submatrix e id = M ⬝ Mᵀ := by
  rw [submatrix_mul_equiv, submatrix_id_id]
#align matrix.submatrix_mul_transpose_submatrix Matrix.submatrix_mul_transpose_submatrix

#print Matrix.subLeft /-
/-- The left `n × l` part of a `n × (l+r)` matrix. -/
@[reducible]
def subLeft {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin l) α :=
  submatrix A id (Fin.castAdd r)
#align matrix.sub_left Matrix.subLeft
-/

#print Matrix.subRight /-
/-- The right `n × r` part of a `n × (l+r)` matrix. -/
@[reducible]
def subRight {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin r) α :=
  submatrix A id (Fin.natAdd l)
#align matrix.sub_right Matrix.subRight
-/

#print Matrix.subUp /-
/-- The top `u × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def subUp {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin u) (Fin n) α :=
  submatrix A (Fin.castAdd d) id
#align matrix.sub_up Matrix.subUp
-/

#print Matrix.subDown /-
/-- The bottom `d × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def subDown {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin d) (Fin n) α :=
  submatrix A (Fin.natAdd u) id
#align matrix.sub_down Matrix.subDown
-/

#print Matrix.subUpRight /-
/-- The top-right `u × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subUpRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin r) α :=
  subUp (subRight A)
#align matrix.sub_up_right Matrix.subUpRight
-/

#print Matrix.subDownRight /-
/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subDownRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin r) α :=
  subDown (subRight A)
#align matrix.sub_down_right Matrix.subDownRight
-/

#print Matrix.subUpLeft /-
/-- The top-left `u × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subUpLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin l) α :=
  subUp (subLeft A)
#align matrix.sub_up_left Matrix.subUpLeft
-/

#print Matrix.subDownLeft /-
/-- The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subDownLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin l) α :=
  subDown (subLeft A)
#align matrix.sub_down_left Matrix.subDownLeft
-/

section RowCol

/-!
### `row_col` section

Simplification lemmas for `matrix.row` and `matrix.col`.
-/


open Matrix

/- warning: matrix.col_add -> Matrix.col_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Add.{u1} α] (v : m -> α) (w : m -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, 0, u1} m Unit α) (Matrix.col.{u1, u2} m α (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_1))) v w)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u2, 0, u1} m Unit α) (Matrix.{u2, 0, u1} m Unit α) (Matrix.{u2, 0, u1} m Unit α) (instHAdd.{max u2 u1} (Matrix.{u2, 0, u1} m Unit α) (Matrix.hasAdd.{u1, u2, 0} m Unit α _inst_1)) (Matrix.col.{u1, u2} m α v) (Matrix.col.{u1, u2} m α w))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Add.{u2} α] (v : m -> α) (w : m -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, 0, u2} m Unit α) (Matrix.col.{u2, u1} m α (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_1))) v w)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{u1, 0, u2} m Unit α) (Matrix.{u1, 0, u2} m Unit α) (Matrix.{u1, 0, u2} m Unit α) (instHAdd.{max u2 u1} (Matrix.{u1, 0, u2} m Unit α) (Matrix.add.{u2, u1, 0} m Unit α _inst_1)) (Matrix.col.{u2, u1} m α v) (Matrix.col.{u2, u1} m α w))
Case conversion may be inaccurate. Consider using '#align matrix.col_add Matrix.col_addₓ'. -/
@[simp]
theorem col_add [Add α] (v w : m → α) : col (v + w) = col v + col w :=
  by
  ext
  rfl
#align matrix.col_add Matrix.col_add

/- warning: matrix.col_smul -> Matrix.col_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : SMul.{u3, u1} R α] (x : R) (v : m -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, 0, u1} m Unit α) (Matrix.col.{u1, u2} m α (SMul.smul.{u3, max u2 u1} R (m -> α) (Function.hasSMul.{u2, u3, u1} m R α _inst_1) x v)) (SMul.smul.{u3, max u2 u1} R (Matrix.{u2, 0, u1} m Unit α) (Matrix.hasSmul.{u1, u2, 0, u3} m Unit R α _inst_1) x (Matrix.col.{u1, u2} m α v))
but is expected to have type
  forall {m : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} [_inst_1 : SMul.{u2, u3} R α] (x : R) (v : m -> α), Eq.{max (succ u3) (succ u1)} (Matrix.{u1, 0, u3} m Unit α) (Matrix.col.{u3, u1} m α (HSMul.hSMul.{u2, max u3 u1, max u3 u1} R (m -> α) (m -> α) (instHSMul.{u2, max u3 u1} R (m -> α) (Pi.instSMul.{u1, u3, u2} m R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.26602 : m) => α) (fun (i : m) => _inst_1))) x v)) (HSMul.hSMul.{u2, max u1 u3, max u3 u1} R (Matrix.{u1, 0, u3} m Unit α) (Matrix.{u1, 0, u3} m Unit α) (instHSMul.{u2, max u3 u1} R (Matrix.{u1, 0, u3} m Unit α) (Matrix.smul.{u3, u1, 0, u2} m Unit R α _inst_1)) x (Matrix.col.{u3, u1} m α v))
Case conversion may be inaccurate. Consider using '#align matrix.col_smul Matrix.col_smulₓ'. -/
@[simp]
theorem col_smul [SMul R α] (x : R) (v : m → α) : col (x • v) = x • col v :=
  by
  ext
  rfl
#align matrix.col_smul Matrix.col_smul

/- warning: matrix.row_add -> Matrix.row_add is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Add.{u1} α] (v : m -> α) (w : m -> α), Eq.{succ (max u2 u1)} (Matrix.{0, u2, u1} Unit m α) (Matrix.row.{u1, u2} m α (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_1))) v w)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{0, u2, u1} Unit m α) (Matrix.{0, u2, u1} Unit m α) (Matrix.{0, u2, u1} Unit m α) (instHAdd.{max u2 u1} (Matrix.{0, u2, u1} Unit m α) (Matrix.hasAdd.{u1, 0, u2} Unit m α _inst_1)) (Matrix.row.{u1, u2} m α v) (Matrix.row.{u1, u2} m α w))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Add.{u2} α] (v : m -> α) (w : m -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{0, u1, u2} Unit m α) (Matrix.row.{u2, u1} m α (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (m -> α) (m -> α) (m -> α) (instHAdd.{max u2 u1} (m -> α) (Pi.instAdd.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_1))) v w)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Matrix.{0, u1, u2} Unit m α) (Matrix.{0, u1, u2} Unit m α) (Matrix.{0, u1, u2} Unit m α) (instHAdd.{max u2 u1} (Matrix.{0, u1, u2} Unit m α) (Matrix.add.{u2, 0, u1} Unit m α _inst_1)) (Matrix.row.{u2, u1} m α v) (Matrix.row.{u2, u1} m α w))
Case conversion may be inaccurate. Consider using '#align matrix.row_add Matrix.row_addₓ'. -/
@[simp]
theorem row_add [Add α] (v w : m → α) : row (v + w) = row v + row w :=
  by
  ext
  rfl
#align matrix.row_add Matrix.row_add

/- warning: matrix.row_smul -> Matrix.row_smul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {R : Type.{u3}} {α : Type.{u1}} [_inst_1 : SMul.{u3, u1} R α] (x : R) (v : m -> α), Eq.{succ (max u2 u1)} (Matrix.{0, u2, u1} Unit m α) (Matrix.row.{u1, u2} m α (SMul.smul.{u3, max u2 u1} R (m -> α) (Function.hasSMul.{u2, u3, u1} m R α _inst_1) x v)) (SMul.smul.{u3, max u2 u1} R (Matrix.{0, u2, u1} Unit m α) (Matrix.hasSmul.{u1, 0, u2, u3} Unit m R α _inst_1) x (Matrix.row.{u1, u2} m α v))
but is expected to have type
  forall {m : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} [_inst_1 : SMul.{u2, u3} R α] (x : R) (v : m -> α), Eq.{max (succ u3) (succ u1)} (Matrix.{0, u1, u3} Unit m α) (Matrix.row.{u3, u1} m α (HSMul.hSMul.{u2, max u3 u1, max u3 u1} R (m -> α) (m -> α) (instHSMul.{u2, max u3 u1} R (m -> α) (Pi.instSMul.{u1, u3, u2} m R (fun (a._@.Mathlib.Data.Matrix.Basic._hyg.26709 : m) => α) (fun (i : m) => _inst_1))) x v)) (HSMul.hSMul.{u2, max u1 u3, max u3 u1} R (Matrix.{0, u1, u3} Unit m α) (Matrix.{0, u1, u3} Unit m α) (instHSMul.{u2, max u3 u1} R (Matrix.{0, u1, u3} Unit m α) (Matrix.smul.{u3, 0, u1, u2} Unit m R α _inst_1)) x (Matrix.row.{u3, u1} m α v))
Case conversion may be inaccurate. Consider using '#align matrix.row_smul Matrix.row_smulₓ'. -/
@[simp]
theorem row_smul [SMul R α] (x : R) (v : m → α) : row (x • v) = x • row v :=
  by
  ext
  rfl
#align matrix.row_smul Matrix.row_smul

/- warning: matrix.transpose_col -> Matrix.transpose_col is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} (v : m -> α), Eq.{succ (max u2 u1)} (Matrix.{0, u2, u1} Unit m α) (Matrix.transpose.{u1, u2, 0} m Unit α (Matrix.col.{u1, u2} m α v)) (Matrix.row.{u1, u2} m α v)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} (v : m -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{0, u1, u2} Unit m α) (Matrix.transpose.{u2, u1, 0} m Unit α (Matrix.col.{u2, u1} m α v)) (Matrix.row.{u2, u1} m α v)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_col Matrix.transpose_colₓ'. -/
@[simp]
theorem transpose_col (v : m → α) : (Matrix.col v)ᵀ = Matrix.row v :=
  by
  ext
  rfl
#align matrix.transpose_col Matrix.transpose_col

/- warning: matrix.transpose_row -> Matrix.transpose_row is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} (v : m -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, 0, u1} m Unit α) (Matrix.transpose.{u1, 0, u2} Unit m α (Matrix.row.{u1, u2} m α v)) (Matrix.col.{u1, u2} m α v)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} (v : m -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, 0, u2} m Unit α) (Matrix.transpose.{u2, 0, u1} Unit m α (Matrix.row.{u2, u1} m α v)) (Matrix.col.{u2, u1} m α v)
Case conversion may be inaccurate. Consider using '#align matrix.transpose_row Matrix.transpose_rowₓ'. -/
@[simp]
theorem transpose_row (v : m → α) : (Matrix.row v)ᵀ = Matrix.col v :=
  by
  ext
  rfl
#align matrix.transpose_row Matrix.transpose_row

/- warning: matrix.conj_transpose_col -> Matrix.conjTranspose_col is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Star.{u1} α] (v : m -> α), Eq.{succ (max u2 u1)} (Matrix.{0, u2, u1} Unit m α) (Matrix.conjTranspose.{u1, u2, 0} m Unit α _inst_1 (Matrix.col.{u1, u2} m α v)) (Matrix.row.{u1, u2} m α (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_1)) v))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Star.{u2} α] (v : m -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{0, u1, u2} Unit m α) (Matrix.conjTranspose.{u2, u1, 0} m Unit α _inst_1 (Matrix.col.{u2, u1} m α v)) (Matrix.row.{u2, u1} m α (Star.star.{max u1 u2} (m -> α) (Pi.instStarForAll.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_1)) v))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_col Matrix.conjTranspose_colₓ'. -/
@[simp]
theorem conjTranspose_col [Star α] (v : m → α) : (col v)ᴴ = row (star v) :=
  by
  ext
  rfl
#align matrix.conj_transpose_col Matrix.conjTranspose_col

/- warning: matrix.conj_transpose_row -> Matrix.conjTranspose_row is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Star.{u1} α] (v : m -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, 0, u1} m Unit α) (Matrix.conjTranspose.{u1, 0, u2} Unit m α _inst_1 (Matrix.row.{u1, u2} m α v)) (Matrix.col.{u1, u2} m α (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_1)) v))
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Star.{u2} α] (v : m -> α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, 0, u2} m Unit α) (Matrix.conjTranspose.{u2, 0, u1} Unit m α _inst_1 (Matrix.row.{u2, u1} m α v)) (Matrix.col.{u2, u1} m α (Star.star.{max u1 u2} (m -> α) (Pi.instStarForAll.{u1, u2} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_1)) v))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_row Matrix.conjTranspose_rowₓ'. -/
@[simp]
theorem conjTranspose_row [Star α] (v : m → α) : (row v)ᴴ = col (star v) :=
  by
  ext
  rfl
#align matrix.conj_transpose_row Matrix.conjTranspose_row

/- warning: matrix.row_vec_mul -> Matrix.row_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] (M : Matrix.{u2, u3, u1} m n α) (v : m -> α), Eq.{succ (max u3 u1)} (Matrix.{0, u3, u1} Unit n α) (Matrix.row.{u1, u3} n α (Matrix.vecMul.{u1, u2, u3} m n α _inst_2 _inst_1 v M)) (Matrix.mul.{u1, 0, u2, u3} Unit m n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Matrix.row.{u1, u2} m α v) M)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : NonUnitalNonAssocSemiring.{u3} α] (M : Matrix.{u2, u1, u3} m n α) (v : m -> α), Eq.{max (succ u3) (succ u1)} (Matrix.{0, u1, u3} Unit n α) (Matrix.row.{u3, u1} n α (Matrix.vecMul.{u3, u2, u1} m n α _inst_2 _inst_1 v M)) (Matrix.mul.{u3, 0, u2, u1} Unit m n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_2) (Matrix.row.{u3, u2} m α v) M)
Case conversion may be inaccurate. Consider using '#align matrix.row_vec_mul Matrix.row_vecMulₓ'. -/
theorem row_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : m → α) :
    Matrix.row (Matrix.vecMul v M) = Matrix.row v ⬝ M :=
  by
  ext
  rfl
#align matrix.row_vec_mul Matrix.row_vecMul

/- warning: matrix.col_vec_mul -> Matrix.col_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] (M : Matrix.{u2, u3, u1} m n α) (v : m -> α), Eq.{succ (max u3 u1)} (Matrix.{u3, 0, u1} n Unit α) (Matrix.col.{u1, u3} n α (Matrix.vecMul.{u1, u2, u3} m n α _inst_2 _inst_1 v M)) (Matrix.transpose.{u1, 0, u3} Unit n α (Matrix.mul.{u1, 0, u2, u3} Unit m n α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Matrix.row.{u1, u2} m α v) M))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} m] [_inst_2 : NonUnitalNonAssocSemiring.{u3} α] (M : Matrix.{u2, u1, u3} m n α) (v : m -> α), Eq.{max (succ u3) (succ u1)} (Matrix.{u1, 0, u3} n Unit α) (Matrix.col.{u3, u1} n α (Matrix.vecMul.{u3, u2, u1} m n α _inst_2 _inst_1 v M)) (Matrix.transpose.{u3, 0, u1} Unit n α (Matrix.mul.{u3, 0, u2, u1} Unit m n α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_2) (Matrix.row.{u3, u2} m α v) M))
Case conversion may be inaccurate. Consider using '#align matrix.col_vec_mul Matrix.col_vecMulₓ'. -/
theorem col_vecMul [Fintype m] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : m → α) :
    Matrix.col (Matrix.vecMul v M) = (Matrix.row v ⬝ M)ᵀ :=
  by
  ext
  rfl
#align matrix.col_vec_mul Matrix.col_vecMul

/- warning: matrix.col_mul_vec -> Matrix.col_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} n] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] (M : Matrix.{u2, u3, u1} m n α) (v : n -> α), Eq.{succ (max u2 u1)} (Matrix.{u2, 0, u1} m Unit α) (Matrix.col.{u1, u2} m α (Matrix.mulVec.{u1, u2, u3} m n α _inst_2 _inst_1 M v)) (Matrix.mul.{u1, u2, u3, 0} m n Unit α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) M (Matrix.col.{u1, u3} n α v))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} n] [_inst_2 : NonUnitalNonAssocSemiring.{u3} α] (M : Matrix.{u1, u2, u3} m n α) (v : n -> α), Eq.{max (succ u3) (succ u1)} (Matrix.{u1, 0, u3} m Unit α) (Matrix.col.{u3, u1} m α (Matrix.mulVec.{u3, u1, u2} m n α _inst_2 _inst_1 M v)) (Matrix.mul.{u3, u1, u2, 0} m n Unit α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_2) M (Matrix.col.{u3, u2} n α v))
Case conversion may be inaccurate. Consider using '#align matrix.col_mul_vec Matrix.col_mulVecₓ'. -/
theorem col_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : n → α) :
    Matrix.col (Matrix.mulVec M v) = M ⬝ Matrix.col v :=
  by
  ext
  rfl
#align matrix.col_mul_vec Matrix.col_mulVec

/- warning: matrix.row_mul_vec -> Matrix.row_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : Fintype.{u3} n] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] (M : Matrix.{u2, u3, u1} m n α) (v : n -> α), Eq.{succ (max u2 u1)} (Matrix.{0, u2, u1} Unit m α) (Matrix.row.{u1, u2} m α (Matrix.mulVec.{u1, u2, u3} m n α _inst_2 _inst_1 M v)) (Matrix.transpose.{u1, u2, 0} m Unit α (Matrix.mul.{u1, u2, u3, 0} m n Unit α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) M (Matrix.col.{u1, u3} n α v)))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : Fintype.{u2} n] [_inst_2 : NonUnitalNonAssocSemiring.{u3} α] (M : Matrix.{u1, u2, u3} m n α) (v : n -> α), Eq.{max (succ u3) (succ u1)} (Matrix.{0, u1, u3} Unit m α) (Matrix.row.{u3, u1} m α (Matrix.mulVec.{u3, u1, u2} m n α _inst_2 _inst_1 M v)) (Matrix.transpose.{u3, u1, 0} m Unit α (Matrix.mul.{u3, u1, u2, 0} m n Unit α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_2) M (Matrix.col.{u3, u2} n α v)))
Case conversion may be inaccurate. Consider using '#align matrix.row_mul_vec Matrix.row_mulVecₓ'. -/
theorem row_mulVec [Fintype n] [NonUnitalNonAssocSemiring α] (M : Matrix m n α) (v : n → α) :
    Matrix.row (Matrix.mulVec M v) = (M ⬝ Matrix.col v)ᵀ :=
  by
  ext
  rfl
#align matrix.row_mul_vec Matrix.row_mulVec

/- warning: matrix.row_mul_col_apply -> Matrix.row_mul_col_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {α : Type.{u1}} [_inst_1 : Fintype.{u2} m] [_inst_2 : Mul.{u1} α] [_inst_3 : AddCommMonoid.{u1} α] (v : m -> α) (w : m -> α) (i : Unit) (j : Unit), Eq.{succ u1} α (Matrix.mul.{u1, 0, u2, 0} Unit m Unit α _inst_1 _inst_2 _inst_3 (Matrix.row.{u1, u2} m α v) (Matrix.col.{u1, u2} m α w) i j) (Matrix.dotProduct.{u1, u2} m α _inst_1 _inst_2 _inst_3 v w)
but is expected to have type
  forall {m : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u1} m] [_inst_2 : Mul.{u2} α] [_inst_3 : AddCommMonoid.{u2} α] (v : m -> α) (w : m -> α) (i : Unit) (j : Unit), Eq.{succ u2} α (Matrix.mul.{u2, 0, u1, 0} Unit m Unit α _inst_1 _inst_2 _inst_3 (Matrix.row.{u2, u1} m α v) (Matrix.col.{u2, u1} m α w) i j) (Matrix.dotProduct.{u2, u1} m α _inst_1 _inst_2 _inst_3 v w)
Case conversion may be inaccurate. Consider using '#align matrix.row_mul_col_apply Matrix.row_mul_col_applyₓ'. -/
@[simp]
theorem row_mul_col_apply [Fintype m] [Mul α] [AddCommMonoid α] (v w : m → α) (i j) :
    (row v ⬝ col w) i j = v ⬝ᵥ w :=
  rfl
#align matrix.row_mul_col_apply Matrix.row_mul_col_apply

end RowCol

section Update

#print Matrix.updateRow /-
/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def updateRow [DecidableEq m] (M : Matrix m n α) (i : m) (b : n → α) : Matrix m n α :=
  Function.update M i b
#align matrix.update_row Matrix.updateRow
-/

#print Matrix.updateColumn /-
/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def updateColumn [DecidableEq n] (M : Matrix m n α) (j : n) (b : m → α) : Matrix m n α := fun i =>
  Function.update (M i) j (b i)
#align matrix.update_column Matrix.updateColumn
-/

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

/- warning: matrix.update_row_self -> Matrix.updateRow_self is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m], Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.updateRow.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b i) b
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {M : Matrix.{u2, u1, u3} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m], Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.updateRow.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b i) b
Case conversion may be inaccurate. Consider using '#align matrix.update_row_self Matrix.updateRow_selfₓ'. -/
@[simp]
theorem updateRow_self [DecidableEq m] : updateRow M i b i = b :=
  Function.update_same i b M
#align matrix.update_row_self Matrix.updateRow_self

/- warning: matrix.update_column_self -> Matrix.updateColumn_self is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {i : m} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u3} n], Eq.{succ u1} α (Matrix.updateColumn.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c i j) (c i)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} {M : Matrix.{u1, u2, u3} m n α} {i : m} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u2} n], Eq.{succ u3} α (Matrix.updateColumn.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c i j) (c i)
Case conversion may be inaccurate. Consider using '#align matrix.update_column_self Matrix.updateColumn_selfₓ'. -/
@[simp]
theorem updateColumn_self [DecidableEq n] : updateColumn M j c i j = c i :=
  Function.update_same j (c i) (M i)
#align matrix.update_column_self Matrix.updateColumn_self

/- warning: matrix.update_row_ne -> Matrix.updateRow_ne is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m] {i' : m}, (Ne.{succ u2} m i' i) -> (Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.updateRow.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b i') (M i'))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {M : Matrix.{u2, u1, u3} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m] {i' : m}, (Ne.{succ u2} m i' i) -> (Eq.{max (succ u3) (succ u1)} (n -> α) (Matrix.updateRow.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b i') (M i'))
Case conversion may be inaccurate. Consider using '#align matrix.update_row_ne Matrix.updateRow_neₓ'. -/
@[simp]
theorem updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' ≠ i) : updateRow M i b i' = M i' :=
  Function.update_noteq i_ne b M
#align matrix.update_row_ne Matrix.updateRow_ne

/- warning: matrix.update_column_ne -> Matrix.updateColumn_ne is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {i : m} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u3} n] {j' : n}, (Ne.{succ u3} n j' j) -> (Eq.{succ u1} α (Matrix.updateColumn.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c i j') (M i j'))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} {M : Matrix.{u1, u2, u3} m n α} {i : m} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u2} n] {j' : n}, (Ne.{succ u2} n j' j) -> (Eq.{succ u3} α (Matrix.updateColumn.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c i j') (M i j'))
Case conversion may be inaccurate. Consider using '#align matrix.update_column_ne Matrix.updateColumn_neₓ'. -/
@[simp]
theorem updateColumn_ne [DecidableEq n] {j' : n} (j_ne : j' ≠ j) :
    updateColumn M j c i j' = M i j' :=
  Function.update_noteq j_ne (c i) (M i)
#align matrix.update_column_ne Matrix.updateColumn_ne

/- warning: matrix.update_row_apply -> Matrix.updateRow_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {i : m} {j : n} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m] {i' : m}, Eq.{succ u1} α (Matrix.updateRow.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b i' j) (ite.{succ u1} α (Eq.{succ u2} m i' i) (_inst_1 i' i) (b j) (M i' j))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {M : Matrix.{u2, u1, u3} m n α} {i : m} {j : n} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m] {i' : m}, Eq.{succ u3} α (Matrix.updateRow.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b i' j) (ite.{succ u3} α (Eq.{succ u2} m i' i) (_inst_1 i' i) (b j) (M i' j))
Case conversion may be inaccurate. Consider using '#align matrix.update_row_apply Matrix.updateRow_applyₓ'. -/
theorem updateRow_apply [DecidableEq m] {i' : m} :
    updateRow M i b i' j = if i' = i then b j else M i' j :=
  by
  by_cases i' = i
  · rw [h, update_row_self, if_pos rfl]
  · rwa [update_row_ne h, if_neg h]
#align matrix.update_row_apply Matrix.updateRow_apply

/- warning: matrix.update_column_apply -> Matrix.updateColumn_apply is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {i : m} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u3} n] {j' : n}, Eq.{succ u1} α (Matrix.updateColumn.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c i j') (ite.{succ u1} α (Eq.{succ u3} n j' j) (_inst_1 j' j) (c i) (M i j'))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} {M : Matrix.{u1, u2, u3} m n α} {i : m} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u2} n] {j' : n}, Eq.{succ u3} α (Matrix.updateColumn.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c i j') (ite.{succ u3} α (Eq.{succ u2} n j' j) (_inst_1 j' j) (c i) (M i j'))
Case conversion may be inaccurate. Consider using '#align matrix.update_column_apply Matrix.updateColumn_applyₓ'. -/
theorem updateColumn_apply [DecidableEq n] {j' : n} :
    updateColumn M j c i j' = if j' = j then c i else M i j' :=
  by
  by_cases j' = j
  · rw [h, update_column_self, if_pos rfl]
  · rwa [update_column_ne h, if_neg h]
#align matrix.update_column_apply Matrix.updateColumn_apply

/- warning: matrix.update_column_subsingleton -> Matrix.updateColumn_subsingleton is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : Subsingleton.{succ u2} n] (A : Matrix.{u1, u2, u3} m n R) (i : n) (b : m -> R), Eq.{succ (max u1 u2 u3)} (Matrix.{u1, u2, u3} m n R) (Matrix.updateColumn.{u3, u1, u2} m n R (fun (a : n) (b : n) => decidableEq_of_subsingleton.{succ u2} n _inst_1 a b) A i b) (Matrix.submatrix.{u3, u1, u1, 0, u2} m m Unit n R (Matrix.col.{u3, u1} m R b) (id.{succ u1} m) (Function.const.{1, succ u2} Unit n Unit.unit))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u1}} [_inst_1 : Subsingleton.{succ u3} n] (A : Matrix.{u2, u3, u1} m n R) (i : n) (b : m -> R), Eq.{max (max (succ u2) (succ u3)) (succ u1)} (Matrix.{u2, u3, u1} m n R) (Matrix.updateColumn.{u1, u2, u3} m n R (fun (a : n) (b : n) => decidableEq_of_subsingleton.{succ u3} n _inst_1 a b) A i b) (Matrix.submatrix.{u1, u2, u2, 0, u3} m m Unit n R (Matrix.col.{u1, u2} m R b) (id.{succ u2} m) (Function.const.{1, succ u3} Unit n Unit.unit))
Case conversion may be inaccurate. Consider using '#align matrix.update_column_subsingleton Matrix.updateColumn_subsingletonₓ'. -/
@[simp]
theorem updateColumn_subsingleton [Subsingleton n] (A : Matrix m n R) (i : n) (b : m → R) :
    A.updateColumn i b = (col b).submatrix id (Function.const n ()) :=
  by
  ext (x y)
  simp [update_column_apply, Subsingleton.elim i y]
#align matrix.update_column_subsingleton Matrix.updateColumn_subsingleton

/- warning: matrix.update_row_subsingleton -> Matrix.updateRow_subsingleton is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : Subsingleton.{succ u1} m] (A : Matrix.{u1, u2, u3} m n R) (i : m) (b : n -> R), Eq.{succ (max u1 u2 u3)} (Matrix.{u1, u2, u3} m n R) (Matrix.updateRow.{u3, u1, u2} m n R (fun (a : m) (b : m) => decidableEq_of_subsingleton.{succ u1} m _inst_1 a b) A i b) (Matrix.submatrix.{u3, u1, 0, u2, u2} m Unit n n R (Matrix.row.{u3, u2} n R b) (Function.const.{1, succ u1} Unit m Unit.unit) (id.{succ u2} n))
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u1}} [_inst_1 : Subsingleton.{succ u3} m] (A : Matrix.{u3, u2, u1} m n R) (i : m) (b : n -> R), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u3, u2, u1} m n R) (Matrix.updateRow.{u1, u3, u2} m n R (fun (a : m) (b : m) => decidableEq_of_subsingleton.{succ u3} m _inst_1 a b) A i b) (Matrix.submatrix.{u1, u3, 0, u2, u2} m Unit n n R (Matrix.row.{u1, u2} n R b) (Function.const.{1, succ u3} Unit m Unit.unit) (id.{succ u2} n))
Case conversion may be inaccurate. Consider using '#align matrix.update_row_subsingleton Matrix.updateRow_subsingletonₓ'. -/
@[simp]
theorem updateRow_subsingleton [Subsingleton m] (A : Matrix m n R) (i : m) (b : n → R) :
    A.updateRow i b = (row b).submatrix (Function.const m ()) id :=
  by
  ext (x y)
  simp [update_column_apply, Subsingleton.elim i x]
#align matrix.update_row_subsingleton Matrix.updateRow_subsingleton

/- warning: matrix.map_update_row -> Matrix.map_updateRow is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {M : Matrix.{u3, u4, u1} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u3} m] (f : α -> β), Eq.{succ (max u3 u4 u2)} (Matrix.{u3, u4, u2} m n β) (Matrix.map.{u1, u2, u3, u4} m n α β (Matrix.updateRow.{u1, u3, u4} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b) f) (Matrix.updateRow.{u2, u3, u4} m n β (fun (a : m) (b : m) => _inst_1 a b) (Matrix.map.{u1, u2, u3, u4} m n α β M f) i (Function.comp.{succ u4, succ u1, succ u2} n α β f b))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {β : Type.{u4}} {M : Matrix.{u2, u1, u3} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m] (f : α -> β), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (Matrix.{u2, u1, u4} m n β) (Matrix.map.{u3, u4, u2, u1} m n α β (Matrix.updateRow.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b) f) (Matrix.updateRow.{u4, u2, u1} m n β (fun (a : m) (b : m) => _inst_1 a b) (Matrix.map.{u3, u4, u2, u1} m n α β M f) i (Function.comp.{succ u1, succ u3, succ u4} n α β f b))
Case conversion may be inaccurate. Consider using '#align matrix.map_update_row Matrix.map_updateRowₓ'. -/
theorem map_updateRow [DecidableEq m] (f : α → β) :
    map (updateRow M i b) f = updateRow (M.map f) i (f ∘ b) :=
  by
  ext (i' j')
  rw [update_row_apply, map_apply, map_apply, update_row_apply]
  exact apply_ite f _ _ _
#align matrix.map_update_row Matrix.map_updateRow

/- warning: matrix.map_update_column -> Matrix.map_updateColumn is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {M : Matrix.{u3, u4, u1} m n α} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u4} n] (f : α -> β), Eq.{succ (max u3 u4 u2)} (Matrix.{u3, u4, u2} m n β) (Matrix.map.{u1, u2, u3, u4} m n α β (Matrix.updateColumn.{u1, u3, u4} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c) f) (Matrix.updateColumn.{u2, u3, u4} m n β (fun (a : n) (b : n) => _inst_1 a b) (Matrix.map.{u1, u2, u3, u4} m n α β M f) j (Function.comp.{succ u3, succ u1, succ u2} m α β f c))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} {M : Matrix.{u1, u2, u3} m n α} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u2} n] (f : α -> β), Eq.{max (max (succ u4) (succ u1)) (succ u2)} (Matrix.{u1, u2, u4} m n β) (Matrix.map.{u3, u4, u1, u2} m n α β (Matrix.updateColumn.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c) f) (Matrix.updateColumn.{u4, u1, u2} m n β (fun (a : n) (b : n) => _inst_1 a b) (Matrix.map.{u3, u4, u1, u2} m n α β M f) j (Function.comp.{succ u1, succ u3, succ u4} m α β f c))
Case conversion may be inaccurate. Consider using '#align matrix.map_update_column Matrix.map_updateColumnₓ'. -/
theorem map_updateColumn [DecidableEq n] (f : α → β) :
    map (updateColumn M j c) f = updateColumn (M.map f) j (f ∘ c) :=
  by
  ext (i' j')
  rw [update_column_apply, map_apply, map_apply, update_column_apply]
  exact apply_ite f _ _ _
#align matrix.map_update_column Matrix.map_updateColumn

/- warning: matrix.update_row_transpose -> Matrix.updateRow_transpose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u3} n], Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.updateRow.{u1, u3, u2} n m α (fun (a : n) (b : n) => _inst_1 a b) (Matrix.transpose.{u1, u2, u3} m n α M) j c) (Matrix.transpose.{u1, u2, u3} m n α (Matrix.updateColumn.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} {M : Matrix.{u1, u2, u3} m n α} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u2} n], Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} n m α) (Matrix.updateRow.{u3, u2, u1} n m α (fun (a : n) (b : n) => _inst_1 a b) (Matrix.transpose.{u3, u1, u2} m n α M) j c) (Matrix.transpose.{u3, u1, u2} m n α (Matrix.updateColumn.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c))
Case conversion may be inaccurate. Consider using '#align matrix.update_row_transpose Matrix.updateRow_transposeₓ'. -/
theorem updateRow_transpose [DecidableEq n] : updateRow Mᵀ j c = (updateColumn M j c)ᵀ :=
  by
  ext (i' j)
  rw [transpose_apply, update_row_apply, update_column_apply]
  rfl
#align matrix.update_row_transpose Matrix.updateRow_transpose

/- warning: matrix.update_column_transpose -> Matrix.updateColumn_transpose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m], Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.updateColumn.{u1, u3, u2} n m α (fun (a : m) (b : m) => _inst_1 a b) (Matrix.transpose.{u1, u2, u3} m n α M) i b) (Matrix.transpose.{u1, u2, u3} m n α (Matrix.updateRow.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {M : Matrix.{u2, u1, u3} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.updateColumn.{u3, u1, u2} n m α (fun (a : m) (b : m) => _inst_1 a b) (Matrix.transpose.{u3, u2, u1} m n α M) i b) (Matrix.transpose.{u3, u2, u1} m n α (Matrix.updateRow.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b))
Case conversion may be inaccurate. Consider using '#align matrix.update_column_transpose Matrix.updateColumn_transposeₓ'. -/
theorem updateColumn_transpose [DecidableEq m] : updateColumn Mᵀ i b = (updateRow M i b)ᵀ :=
  by
  ext (i' j)
  rw [transpose_apply, update_row_apply, update_column_apply]
  rfl
#align matrix.update_column_transpose Matrix.updateColumn_transpose

/- warning: matrix.update_row_conj_transpose -> Matrix.updateRow_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u3} n] [_inst_2 : Star.{u1} α], Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.updateRow.{u1, u3, u2} n m α (fun (a : n) (b : n) => _inst_1 a b) (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_2 M) j (Star.star.{max u2 u1} (m -> α) (Pi.hasStar.{u2, u1} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_2)) c)) (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_2 (Matrix.updateColumn.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c))
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} {M : Matrix.{u1, u2, u3} m n α} {j : n} {c : m -> α} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Star.{u3} α], Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u2, u1, u3} n m α) (Matrix.updateRow.{u3, u2, u1} n m α (fun (a : n) (b : n) => _inst_1 a b) (Matrix.conjTranspose.{u3, u1, u2} m n α _inst_2 M) j (Star.star.{max u3 u1} (m -> α) (Pi.instStarForAll.{u1, u3} m (fun (ᾰ : m) => α) (fun (i : m) => _inst_2)) c)) (Matrix.conjTranspose.{u3, u1, u2} m n α _inst_2 (Matrix.updateColumn.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) M j c))
Case conversion may be inaccurate. Consider using '#align matrix.update_row_conj_transpose Matrix.updateRow_conjTransposeₓ'. -/
theorem updateRow_conjTranspose [DecidableEq n] [Star α] :
    updateRow Mᴴ j (star c) = (updateColumn M j c)ᴴ :=
  by
  rw [conj_transpose, conj_transpose, transpose_map, transpose_map, update_row_transpose,
    map_update_column]
  rfl
#align matrix.update_row_conj_transpose Matrix.updateRow_conjTranspose

/- warning: matrix.update_column_conj_transpose -> Matrix.updateColumn_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} {M : Matrix.{u2, u3, u1} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m] [_inst_2 : Star.{u1} α], Eq.{succ (max u3 u2 u1)} (Matrix.{u3, u2, u1} n m α) (Matrix.updateColumn.{u1, u3, u2} n m α (fun (a : m) (b : m) => _inst_1 a b) (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_2 M) i (Star.star.{max u3 u1} (n -> α) (Pi.hasStar.{u3, u1} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_2)) b)) (Matrix.conjTranspose.{u1, u2, u3} m n α _inst_2 (Matrix.updateRow.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b))
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} {M : Matrix.{u2, u1, u3} m n α} {i : m} {b : n -> α} [_inst_1 : DecidableEq.{succ u2} m] [_inst_2 : Star.{u3} α], Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u1, u2, u3} n m α) (Matrix.updateColumn.{u3, u1, u2} n m α (fun (a : m) (b : m) => _inst_1 a b) (Matrix.conjTranspose.{u3, u2, u1} m n α _inst_2 M) i (Star.star.{max u3 u1} (n -> α) (Pi.instStarForAll.{u1, u3} n (fun (ᾰ : n) => α) (fun (i : n) => _inst_2)) b)) (Matrix.conjTranspose.{u3, u2, u1} m n α _inst_2 (Matrix.updateRow.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_1 a b) M i b))
Case conversion may be inaccurate. Consider using '#align matrix.update_column_conj_transpose Matrix.updateColumn_conjTransposeₓ'. -/
theorem updateColumn_conjTranspose [DecidableEq m] [Star α] :
    updateColumn Mᴴ i (star b) = (updateRow M i b)ᴴ :=
  by
  rw [conj_transpose, conj_transpose, transpose_map, transpose_map, update_column_transpose,
    map_update_row]
  rfl
#align matrix.update_column_conj_transpose Matrix.updateColumn_conjTranspose

/- warning: matrix.update_row_eq_self -> Matrix.updateRow_eq_self is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} m] (A : Matrix.{u2, u3, u1} m n α) (i : m), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.updateRow.{u1, u2, u3} m n α (fun (a : m) (b : m) => _inst_1 a b) A i (A i)) A
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} m] (A : Matrix.{u2, u1, u3} m n α) (i : m), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Matrix.{u2, u1, u3} m n α) (Matrix.updateRow.{u3, u2, u1} m n α (fun (a : m) (b : m) => _inst_1 a b) A i (A i)) A
Case conversion may be inaccurate. Consider using '#align matrix.update_row_eq_self Matrix.updateRow_eq_selfₓ'. -/
@[simp]
theorem updateRow_eq_self [DecidableEq m] (A : Matrix m n α) (i : m) : A.updateRow i (A i) = A :=
  Function.update_eq_self i A
#align matrix.update_row_eq_self Matrix.updateRow_eq_self

/- warning: matrix.update_column_eq_self -> Matrix.updateColumn_eq_self is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u2}} {n : Type.{u3}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} n] (A : Matrix.{u2, u3, u1} m n α) (i : n), Eq.{succ (max u2 u3 u1)} (Matrix.{u2, u3, u1} m n α) (Matrix.updateColumn.{u1, u2, u3} m n α (fun (a : n) (b : n) => _inst_1 a b) A i (fun (j : m) => A j i)) A
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {α : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} n] (A : Matrix.{u1, u2, u3} m n α) (i : n), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Matrix.{u1, u2, u3} m n α) (Matrix.updateColumn.{u3, u1, u2} m n α (fun (a : n) (b : n) => _inst_1 a b) A i (fun (j : m) => A j i)) A
Case conversion may be inaccurate. Consider using '#align matrix.update_column_eq_self Matrix.updateColumn_eq_selfₓ'. -/
@[simp]
theorem updateColumn_eq_self [DecidableEq n] (A : Matrix m n α) (i : n) :
    (A.updateColumn i fun j => A j i) = A :=
  funext fun j => Function.update_eq_self i (A j)
#align matrix.update_column_eq_self Matrix.updateColumn_eq_self

/- warning: matrix.diagonal_update_column_single -> Matrix.diagonal_updateColumn_single is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] (v : n -> α) (i : n) (x : α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.updateColumn.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 v) i (Pi.single.{u2, u1} n (fun (ᾰ : n) => α) (fun (a : n) (b : n) => _inst_1 a b) (fun (i : n) => _inst_2) i x)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (Function.update.{succ u2, succ u1} n (fun (ᾰ : n) => α) (fun (a : n) (b : n) => _inst_1 a b) v i x))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] (v : n -> α) (i : n) (x : α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.updateColumn.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 v) i (Pi.single.{u1, u2} n (fun (ᾰ : n) => α) (fun (a : n) (b : n) => _inst_1 a b) (fun (i : n) => _inst_2) i x)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (Function.update.{succ u1, succ u2} n (fun (ᾰ : n) => α) (fun (a : n) (b : n) => _inst_1 a b) v i x))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_update_column_single Matrix.diagonal_updateColumn_singleₓ'. -/
theorem diagonal_updateColumn_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateColumn i (Pi.single i x) = diagonal (Function.update v i x) :=
  by
  ext (j k)
  obtain rfl | hjk := eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hji := eq_or_ne j i
    · rw [update_column_self, Pi.single_eq_same, Function.update_same]
    · rw [update_column_ne hji, diagonal_apply_eq, Function.update_noteq hji]
  · rw [diagonal_apply_ne _ hjk]
    obtain rfl | hki := eq_or_ne k i
    · rw [update_column_self, Pi.single_eq_of_ne hjk]
    · rw [update_column_ne hki, diagonal_apply_ne _ hjk]
#align matrix.diagonal_update_column_single Matrix.diagonal_updateColumn_single

/- warning: matrix.diagonal_update_row_single -> Matrix.diagonal_updateRow_single is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Zero.{u1} α] (v : n -> α) (i : n) (x : α), Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} n n α) (Matrix.updateRow.{u1, u2, u2} n n α (fun (a : n) (b : n) => _inst_1 a b) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 v) i (Pi.single.{u2, u1} n (fun (ᾰ : n) => α) (fun (a : n) (b : n) => _inst_1 a b) (fun (i : n) => _inst_2) i x)) (Matrix.diagonal.{u1, u2} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (Function.update.{succ u2, succ u1} n (fun (ᾰ : n) => α) (fun (a : n) (b : n) => _inst_1 a b) v i x))
but is expected to have type
  forall {n : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Zero.{u2} α] (v : n -> α) (i : n) (x : α), Eq.{max (succ u2) (succ u1)} (Matrix.{u1, u1, u2} n n α) (Matrix.updateRow.{u2, u1, u1} n n α (fun (a : n) (b : n) => _inst_1 a b) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 v) i (Pi.single.{u1, u2} n (fun (ᾰ : n) => α) (fun (a : n) (b : n) => _inst_1 a b) (fun (i : n) => _inst_2) i x)) (Matrix.diagonal.{u2, u1} n α (fun (a : n) (b : n) => _inst_1 a b) _inst_2 (Function.update.{succ u1, succ u2} n (fun (ᾰ : n) => α) (fun (a : n) (b : n) => _inst_1 a b) v i x))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_update_row_single Matrix.diagonal_updateRow_singleₓ'. -/
theorem diagonal_updateRow_single [DecidableEq n] [Zero α] (v : n → α) (i : n) (x : α) :
    (diagonal v).updateRow i (Pi.single i x) = diagonal (Function.update v i x) := by
  rw [← diagonal_transpose, update_row_transpose, diagonal_update_column_single, diagonal_transpose]
#align matrix.diagonal_update_row_single Matrix.diagonal_updateRow_single

end Update

end Matrix

namespace RingHom

variable [Fintype n] [NonAssocSemiring α] [NonAssocSemiring β]

/- warning: ring_hom.map_matrix_mul -> RingHom.map_matrix_mul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u3}} {n : Type.{u4}} {o : Type.{u5}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u4} n] [_inst_2 : NonAssocSemiring.{u1} α] [_inst_3 : NonAssocSemiring.{u2} β] (M : Matrix.{u3, u4, u1} m n α) (N : Matrix.{u4, u5, u1} n o α) (i : m) (j : o) (f : RingHom.{u1, u2} α β _inst_2 _inst_3), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β _inst_2 _inst_3) (fun (_x : RingHom.{u1, u2} α β _inst_2 _inst_3) => α -> β) (RingHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3) f (Matrix.mul.{u1, u3, u4, u5} m n o α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_2)) M N i j)) (Matrix.mul.{u2, u3, u4, u5} m n o β _inst_1 (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β _inst_3)) (Matrix.map.{u1, u2, u3, u4} m n α β M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β _inst_2 _inst_3) (fun (_x : RingHom.{u1, u2} α β _inst_2 _inst_3) => α -> β) (RingHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3) f)) (Matrix.map.{u1, u2, u4, u5} n o α β N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β _inst_2 _inst_3) (fun (_x : RingHom.{u1, u2} α β _inst_2 _inst_3) => α -> β) (RingHom.hasCoeToFun.{u1, u2} α β _inst_2 _inst_3) f)) i j)
but is expected to have type
  forall {m : Type.{u3}} {n : Type.{u2}} {o : Type.{u1}} {α : Type.{u4}} {β : Type.{u5}} [_inst_1 : Fintype.{u2} n] [_inst_2 : NonAssocSemiring.{u4} α] [_inst_3 : NonAssocSemiring.{u5} β] (M : Matrix.{u3, u2, u4} m n α) (N : Matrix.{u2, u1, u4} n o α) (i : m) (j : o) (f : RingHom.{u4, u5} α β _inst_2 _inst_3), Eq.{succ u5} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) M N i j)) (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) (NonUnitalNonAssocSemiring.toMul.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3) (RingHomClass.toNonUnitalRingHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β _inst_2 _inst_3 (RingHom.instRingHomClassRingHom.{u4, u5} α β _inst_2 _inst_3)))) f (Matrix.mul.{u4, u3, u2, u1} m n o α _inst_1 (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) M N i j)) (Matrix.mul.{u5, u3, u2, u1} m n o β _inst_1 (NonUnitalNonAssocSemiring.toMul.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (Matrix.map.{u4, u5, u3, u2} m n α β M (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) (NonUnitalNonAssocSemiring.toMul.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3) (RingHomClass.toNonUnitalRingHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β _inst_2 _inst_3 (RingHom.instRingHomClassRingHom.{u4, u5} α β _inst_2 _inst_3)))) f)) (Matrix.map.{u4, u5, u2, u1} n o α β N (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β (NonUnitalNonAssocSemiring.toMul.{u4} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2)) (NonUnitalNonAssocSemiring.toMul.{u5} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} α _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u5} β _inst_3) (RingHomClass.toNonUnitalRingHomClass.{max u4 u5, u4, u5} (RingHom.{u4, u5} α β _inst_2 _inst_3) α β _inst_2 _inst_3 (RingHom.instRingHomClassRingHom.{u4, u5} α β _inst_2 _inst_3)))) f)) i j)
Case conversion may be inaccurate. Consider using '#align ring_hom.map_matrix_mul RingHom.map_matrix_mulₓ'. -/
theorem map_matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α →+* β) :
    f (Matrix.mul M N i j) = Matrix.mul (M.map f) (N.map f) i j := by
  simp [Matrix.mul_apply, RingHom.map_sum]
#align ring_hom.map_matrix_mul RingHom.map_matrix_mul

/- warning: ring_hom.map_dot_product -> RingHom.map_dotProduct is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : Fintype.{u1} n] [_inst_4 : NonAssocSemiring.{u2} R] [_inst_5 : NonAssocSemiring.{u3} S] (f : RingHom.{u2, u3} R S _inst_4 _inst_5) (v : n -> R) (w : n -> R), Eq.{succ u3} S (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} R S _inst_4 _inst_5) (fun (_x : RingHom.{u2, u3} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u2, u3} R S _inst_4 _inst_5) f (Matrix.dotProduct.{u2, u1} n R _inst_1 (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_4))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_4)) v w)) (Matrix.dotProduct.{u3, u1} n S _inst_1 (Distrib.toHasMul.{u3} S (NonUnitalNonAssocSemiring.toDistrib.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5)) (Function.comp.{succ u1, succ u2, succ u3} n R S (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} R S _inst_4 _inst_5) (fun (_x : RingHom.{u2, u3} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u2, u3} R S _inst_4 _inst_5) f) v) (Function.comp.{succ u1, succ u2, succ u3} n R S (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} R S _inst_4 _inst_5) (fun (_x : RingHom.{u2, u3} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u2, u3} R S _inst_4 _inst_5) f) w))
but is expected to have type
  forall {n : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : Fintype.{u1} n] [_inst_4 : NonAssocSemiring.{u3} R] [_inst_5 : NonAssocSemiring.{u2} S] (f : RingHom.{u3, u2} R S _inst_4 _inst_5) (v : n -> R) (w : n -> R), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) (Matrix.dotProduct.{u3, u1} n R _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) v w)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u3, u2} R S _inst_4 _inst_5)))) f (Matrix.dotProduct.{u3, u1} n R _inst_1 (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) v w)) (Matrix.dotProduct.{u2, u1} n S _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_5)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_5)) (Function.comp.{succ u1, succ u3, succ u2} n R S (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u3, u2} R S _inst_4 _inst_5)))) f) v) (Function.comp.{succ u1, succ u3, succ u2} n R S (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u3 u2, u3, u2} (RingHom.{u3, u2} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u3, u2} R S _inst_4 _inst_5)))) f) w))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_dot_product RingHom.map_dotProductₓ'. -/
theorem map_dotProduct [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (v w : n → R) :
    f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w := by simp only [Matrix.dotProduct, f.map_sum, f.map_mul]
#align ring_hom.map_dot_product RingHom.map_dotProduct

/- warning: ring_hom.map_vec_mul -> RingHom.map_vecMul is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} {S : Type.{u4}} [_inst_1 : Fintype.{u2} n] [_inst_4 : NonAssocSemiring.{u3} R] [_inst_5 : NonAssocSemiring.{u4} S] (f : RingHom.{u3, u4} R S _inst_4 _inst_5) (M : Matrix.{u2, u1, u3} n m R) (v : n -> R) (i : m), Eq.{succ u4} S (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (RingHom.{u3, u4} R S _inst_4 _inst_5) (fun (_x : RingHom.{u3, u4} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u3, u4} R S _inst_4 _inst_5) f (Matrix.vecMul.{u3, u2, u1} n m R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4) _inst_1 v M i)) (Matrix.vecMul.{u4, u2, u1} n m S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} S _inst_5) _inst_1 (Function.comp.{succ u2, succ u3, succ u4} n R S (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (RingHom.{u3, u4} R S _inst_4 _inst_5) (fun (_x : RingHom.{u3, u4} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u3, u4} R S _inst_4 _inst_5) f) v) (Matrix.map.{u3, u4, u2, u1} n m R S M (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (RingHom.{u3, u4} R S _inst_4 _inst_5) (fun (_x : RingHom.{u3, u4} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u3, u4} R S _inst_4 _inst_5) f)) i)
but is expected to have type
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u4}} {S : Type.{u3}} [_inst_1 : Fintype.{u2} n] [_inst_4 : NonAssocSemiring.{u4} R] [_inst_5 : NonAssocSemiring.{u3} S] (f : RingHom.{u4, u3} R S _inst_4 _inst_5) (M : Matrix.{u2, u1, u4} n m R) (v : n -> R) (i : m), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) (Matrix.vecMul.{u4, u2, u1} n m R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) _inst_1 v M i)) (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u4} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u4, u3} R S _inst_4 _inst_5)))) f (Matrix.vecMul.{u4, u2, u1} n m R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) _inst_1 v M i)) (Matrix.vecMul.{u3, u2, u1} n m S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5) _inst_1 (Function.comp.{succ u2, succ u4, succ u3} n R S (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u4} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u4, u3} R S _inst_4 _inst_5)))) f) v) (Matrix.map.{u4, u3, u2, u1} n m R S M (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u4} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u4, u3} R S _inst_4 _inst_5)))) f)) i)
Case conversion may be inaccurate. Consider using '#align ring_hom.map_vec_mul RingHom.map_vecMulₓ'. -/
theorem map_vecMul [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix n m R)
    (v : n → R) (i : m) : f (M.vecMul v i) = (M.map f).vecMul (f ∘ v) i := by
  simp only [Matrix.vecMul, Matrix.map_apply, RingHom.map_dotProduct]
#align ring_hom.map_vec_mul RingHom.map_vecMul

/- warning: ring_hom.map_mul_vec -> RingHom.map_mulVec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} {S : Type.{u4}} [_inst_1 : Fintype.{u2} n] [_inst_4 : NonAssocSemiring.{u3} R] [_inst_5 : NonAssocSemiring.{u4} S] (f : RingHom.{u3, u4} R S _inst_4 _inst_5) (M : Matrix.{u1, u2, u3} m n R) (v : n -> R) (i : m), Eq.{succ u4} S (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (RingHom.{u3, u4} R S _inst_4 _inst_5) (fun (_x : RingHom.{u3, u4} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u3, u4} R S _inst_4 _inst_5) f (Matrix.mulVec.{u3, u1, u2} m n R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_4) _inst_1 M v i)) (Matrix.mulVec.{u4, u1, u2} m n S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} S _inst_5) _inst_1 (Matrix.map.{u3, u4, u1, u2} m n R S M (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (RingHom.{u3, u4} R S _inst_4 _inst_5) (fun (_x : RingHom.{u3, u4} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u3, u4} R S _inst_4 _inst_5) f)) (Function.comp.{succ u2, succ u3, succ u4} n R S (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (RingHom.{u3, u4} R S _inst_4 _inst_5) (fun (_x : RingHom.{u3, u4} R S _inst_4 _inst_5) => R -> S) (RingHom.hasCoeToFun.{u3, u4} R S _inst_4 _inst_5) f) v) i)
but is expected to have type
  forall {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u4}} {S : Type.{u3}} [_inst_1 : Fintype.{u1} n] [_inst_4 : NonAssocSemiring.{u4} R] [_inst_5 : NonAssocSemiring.{u3} S] (f : RingHom.{u4, u3} R S _inst_4 _inst_5) (M : Matrix.{u2, u1, u4} m n R) (v : n -> R) (i : m), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) (Matrix.mulVec.{u4, u2, u1} m n R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) _inst_1 M v i)) (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u4} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u4, u3} R S _inst_4 _inst_5)))) f (Matrix.mulVec.{u4, u2, u1} m n R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) _inst_1 M v i)) (Matrix.mulVec.{u3, u2, u1} m n S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5) _inst_1 (Matrix.map.{u4, u3, u2, u1} m n R S M (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u4} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u4, u3} R S _inst_4 _inst_5)))) f)) (Function.comp.{succ u1, succ u4, succ u3} n R S (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonUnitalNonAssocSemiring.toMul.{u4} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4)) (NonUnitalNonAssocSemiring.toMul.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5)) (NonUnitalRingHomClass.toMulHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R _inst_4) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S _inst_5) (RingHomClass.toNonUnitalRingHomClass.{max u4 u3, u4, u3} (RingHom.{u4, u3} R S _inst_4 _inst_5) R S _inst_4 _inst_5 (RingHom.instRingHomClassRingHom.{u4, u3} R S _inst_4 _inst_5)))) f) v) i)
Case conversion may be inaccurate. Consider using '#align ring_hom.map_mul_vec RingHom.map_mulVecₓ'. -/
theorem map_mulVec [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (M : Matrix m n R)
    (v : n → R) (i : m) : f (M.mulVec v i) = (M.map f).mulVec (f ∘ v) i := by
  simp only [Matrix.mulVec, Matrix.map_apply, RingHom.map_dotProduct]
#align ring_hom.map_mul_vec RingHom.map_mulVec

end RingHom

