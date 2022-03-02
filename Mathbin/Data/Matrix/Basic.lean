/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.BigOperators.Pi
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.Module.Pi
import Mathbin.Algebra.Star.Pi
import Mathbin.Data.Equiv.Ring
import Mathbin.Data.Fintype.Card

/-!
# Matrices

This file defines basic properties of matrices.

## Notation

The locale `matrix` gives the following notation:

* `⬝ᵥ` for `matrix.dot_product`
* `⬝` for `matrix.mul`
* `ᵀ` for `matrix.transpose`
* `ᴴ` for `matrix.conj_transpose`

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/


universe u u' v w

open_locale BigOperators

/-- `matrix m n` is the type of matrices whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m → n → α

variable {l m n o : Type _} {m' : o → Type _} {n' : o → Type _}

variable {R : Type _} {S : Type _} {α : Type v} {β : Type w} {γ : Type _}

namespace Matrix

section Ext

variable {M N : Matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by
    simp [h]⟩

@[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp

end Ext

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
def map (M : Matrix m n α) (f : α → β) : Matrix m n β := fun i j => f (M i j)

@[simp]
theorem map_apply {M : Matrix m n α} {f : α → β} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl

@[simp]
theorem map_id (M : Matrix m n α) : M.map id = M := by
  ext
  rfl

@[simp]
theorem map_map {M : Matrix m n α} {β γ : Type _} {f : α → β} {g : β → γ} : (M.map f).map g = M.map (g ∘ f) := by
  ext
  rfl

/-- The transpose of a matrix. -/
def transposeₓ (M : Matrix m n α) : Matrix n m α
  | x, y => M y x

-- mathport name: «expr ᵀ»
localized [Matrix] postfix:1024 "ᵀ" => Matrix.transposeₓ

/-- The conjugate transpose of a matrix defined in term of `star`. -/
def conjTranspose [HasStar α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star

-- mathport name: «expr ᴴ»
localized [Matrix] postfix:1024 "ᴴ" => Matrix.conjTranspose

/-- `matrix.col u` is the column matrix whose entries are given by `u`. -/
def colₓ (w : m → α) : Matrix m Unit α
  | x, y => w x

/-- `matrix.row u` is the row matrix whose entries are given by `u`. -/
def rowₓ (v : n → α) : Matrix Unit n α
  | x, y => v y

instance [Inhabited α] : Inhabited (Matrix m n α) :=
  Pi.inhabited _

instance [Add α] : Add (Matrix m n α) :=
  Pi.hasAdd

instance [AddSemigroupₓ α] : AddSemigroupₓ (Matrix m n α) :=
  Pi.addSemigroup

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ (Matrix m n α) :=
  Pi.addCommSemigroup

instance [Zero α] : Zero (Matrix m n α) :=
  Pi.hasZero

instance [AddZeroClass α] : AddZeroClass (Matrix m n α) :=
  Pi.addZeroClass

instance [AddMonoidₓ α] : AddMonoidₓ (Matrix m n α) :=
  Pi.addMonoid

instance [AddCommMonoidₓ α] : AddCommMonoidₓ (Matrix m n α) :=
  Pi.addCommMonoid

instance [Neg α] : Neg (Matrix m n α) :=
  Pi.hasNeg

instance [Sub α] : Sub (Matrix m n α) :=
  Pi.hasSub

instance [AddGroupₓ α] : AddGroupₓ (Matrix m n α) :=
  Pi.addGroup

instance [AddCommGroupₓ α] : AddCommGroupₓ (Matrix m n α) :=
  Pi.addCommGroup

instance [Unique α] : Unique (Matrix m n α) :=
  Pi.unique

instance [Subsingleton α] : Subsingleton (Matrix m n α) :=
  Pi.subsingleton

instance [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n α) :=
  Function.nontrivial

instance [HasScalar R α] : HasScalar R (Matrix m n α) :=
  Pi.hasScalar

instance [HasScalar R α] [HasScalar S α] [SmulCommClass R S α] : SmulCommClass R S (Matrix m n α) :=
  Pi.smul_comm_class

instance [HasScalar R S] [HasScalar R α] [HasScalar S α] [IsScalarTower R S α] : IsScalarTower R S (Matrix m n α) :=
  Pi.is_scalar_tower

instance [HasScalar R α] [HasScalar Rᵐᵒᵖ α] [IsCentralScalar R α] : IsCentralScalar R (Matrix m n α) :=
  Pi.is_central_scalar

instance [Monoidₓ R] [MulAction R α] : MulAction R (Matrix m n α) :=
  Pi.mulAction _

instance [Monoidₓ R] [AddMonoidₓ α] [DistribMulAction R α] : DistribMulAction R (Matrix m n α) :=
  Pi.distribMulAction _

instance [Semiringₓ R] [AddCommMonoidₓ α] [Module R α] : Module R (Matrix m n α) :=
  Pi.module _ _ _

@[simp]
theorem map_zero [Zero α] [Zero β] (f : α → β) (h : f 0 = 0) : (0 : Matrix m n α).map f = 0 := by
  ext
  simp [h]

theorem map_add [Add α] [Add β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂) (M N : Matrix m n α) :
    (M + N).map f = M.map f + N.map f :=
  ext fun _ _ => hf _ _

theorem map_sub [Sub α] [Sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂) (M N : Matrix m n α) :
    (M - N).map f = M.map f - N.map f :=
  ext fun _ _ => hf _ _

theorem map_smul [HasScalar R α] [HasScalar R β] (f : α → β) (r : R) (hf : ∀ a, f (r • a) = r • f a)
    (M : Matrix m n α) : (r • M).map f = r • M.map f :=
  ext fun _ _ => hf _

theorem _root_.is_smul_regular.matrix [HasScalar R S] {k : R} (hk : IsSmulRegular S k) :
    IsSmulRegular (Matrix m n S) k :=
  IsSmulRegular.pi fun _ => IsSmulRegular.pi fun _ => hk

theorem _root_.is_left_regular.matrix [Mul α] {k : α} (hk : IsLeftRegular k) : IsSmulRegular (Matrix m n α) k :=
  hk.IsSmulRegular.Matrix

-- TODO[gh-6025]: make this an instance once safe to do so
theorem subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim i⟩

-- TODO[gh-6025]: make this an instance once safe to do so
theorem subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext
    exact isEmptyElim j⟩

end Matrix

open_locale Matrix

namespace Matrix

section Diagonal

variable [DecidableEq n]

/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`.

Note that bundled versions exist as:
* `matrix.diagonal_add_monoid_hom`
* `matrix.diagonal_linear_map`
* `matrix.diagonal_ring_hom`
* `matrix.diagonal_alg_hom`
-/
def diagonalₓ [Zero α] (d : n → α) : Matrix n n α
  | i, j => if i = j then d i else 0

@[simp]
theorem diagonal_apply_eq [Zero α] {d : n → α} (i : n) : (diagonalₓ d) i i = d i := by
  simp [diagonal]

@[simp]
theorem diagonal_apply_ne [Zero α] {d : n → α} {i j : n} (h : i ≠ j) : (diagonalₓ d) i j = 0 := by
  simp [diagonal, h]

theorem diagonal_apply_ne' [Zero α] {d : n → α} {i j : n} (h : j ≠ i) : (diagonalₓ d) i j = 0 :=
  diagonal_apply_ne h.symm

theorem diagonal_injective [Zero α] : Function.Injective (diagonalₓ : (n → α) → Matrix n n α) := fun d₁ d₂ h =>
  funext fun i => by
    simpa using matrix.ext_iff.mpr h i i

@[simp]
theorem diagonal_zero [Zero α] : (diagonalₓ fun _ => 0 : Matrix n n α) = 0 := by
  ext
  simp [diagonal]

@[simp]
theorem diagonal_transpose [Zero α] (v : n → α) : (diagonalₓ v)ᵀ = diagonalₓ v := by
  ext i j
  by_cases' h : i = j
  · simp [h, transpose]
    
  · simp [h, transpose, diagonal_apply_ne' h]
    

@[simp]
theorem diagonal_add [AddZeroClass α] (d₁ d₂ : n → α) : diagonalₓ d₁ + diagonalₓ d₂ = diagonalₓ fun i => d₁ i + d₂ i :=
  by
  ext i j <;> by_cases' h : i = j <;> simp [h]

@[simp]
theorem diagonal_smul [Monoidₓ R] [AddMonoidₓ α] [DistribMulAction R α] (r : R) (d : n → α) :
    diagonalₓ (r • d) = r • diagonalₓ d := by
  ext i j <;> by_cases' h : i = j <;> simp [h]

variable (n α)

/-- `matrix.diagonal` as an `add_monoid_hom`. -/
@[simps]
def diagonalAddMonoidHom [AddZeroClass α] : (n → α) →+ Matrix n n α where
  toFun := diagonalₓ
  map_zero' := diagonal_zero
  map_add' := fun x y => (diagonal_add x y).symm

variable (R)

/-- `matrix.diagonal` as a `linear_map`. -/
@[simps]
def diagonalLinearMap [Semiringₓ R] [AddCommMonoidₓ α] [Module R α] : (n → α) →ₗ[R] Matrix n n α :=
  { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }

variable {n α R}

@[simp]
theorem diagonal_map [Zero α] [Zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
    (diagonalₓ d).map f = diagonalₓ fun m => f (d m) := by
  ext
  simp only [diagonal, map_apply]
  split_ifs <;> simp [h]

@[simp]
theorem diagonal_conj_transpose [Semiringₓ α] [StarRing α] (v : n → α) : (diagonalₓ v)ᴴ = diagonalₓ (star v) := by
  rw [conj_transpose, diagonal_transpose, diagonal_map (star_zero _)]
  rfl

section One

variable [Zero α] [One α]

instance : One (Matrix n n α) :=
  ⟨diagonalₓ fun _ => 1⟩

@[simp]
theorem diagonal_one : (diagonalₓ fun _ => 1 : Matrix n n α) = 1 :=
  rfl

theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
  rfl

@[simp]
theorem one_apply_eq i : (1 : Matrix n n α) i i = 1 :=
  diagonal_apply_eq i

@[simp]
theorem one_apply_ne {i j} : i ≠ j → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne

theorem one_apply_ne' {i j} : j ≠ i → (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne'

@[simp]
theorem map_one [Zero β] [One β] (f : α → β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    (1 : Matrix n n α).map f = (1 : Matrix n n β) := by
  ext
  simp only [one_apply, map_apply]
  split_ifs <;> simp [h₀, h₁]

theorem one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single i 1 j := by
  simp only [one_apply, Pi.single_apply, eq_comm] <;> congr

-- deal with decidable_eq
end One

section Numeral

@[simp]
theorem bit0_apply [Add α] (M : Matrix m m α) (i : m) (j : m) : (bit0 M) i j = bit0 (M i j) :=
  rfl

variable [AddMonoidₓ α] [One α]

theorem bit1_apply (M : Matrix n n α) (i : n) (j : n) : (bit1 M) i j = if i = j then bit1 (M i j) else bit0 (M i j) :=
  by
  dsimp [bit1] <;> by_cases' h : i = j <;> simp [h]

@[simp]
theorem bit1_apply_eq (M : Matrix n n α) (i : n) : (bit1 M) i i = bit1 (M i i) := by
  simp [bit1_apply]

@[simp]
theorem bit1_apply_ne (M : Matrix n n α) {i j : n} (h : i ≠ j) : (bit1 M) i j = bit0 (M i j) := by
  simp [bit1_apply, h]

end Numeral

end Diagonal

section DotProduct

variable [Fintype m]

/-- `dot_product v w` is the sum of the entrywise products `v i * w i` -/
def dotProduct [Mul α] [AddCommMonoidₓ α] (v w : m → α) : α :=
  ∑ i, v i * w i

-- mathport name: «expr ⬝ᵥ »
/- The precedence of 72 comes immediately after ` • ` for `has_scalar.smul`,
   so that `r₁ • a ⬝ᵥ r₂ • b` is parsed as `(r₁ • a) ⬝ᵥ (r₂ • b)` here. -/
localized [Matrix] infixl:72 " ⬝ᵥ " => Matrix.dotProduct

theorem dot_product_assoc [Fintype n] [NonUnitalSemiringₓ α] (u : m → α) (w : n → α) (v : Matrix m n α) :
    (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i => v i ⬝ᵥ w := by
  simpa [dot_product, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm

theorem dot_product_comm [CommSemiringₓ α] (v w : m → α) : v ⬝ᵥ w = w ⬝ᵥ v := by
  simp_rw [dot_product, mul_comm]

@[simp]
theorem dot_product_punit [AddCommMonoidₓ α] [Mul α] (v w : PUnit → α) : v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩ := by
  simp [dot_product]

section NonUnitalNonAssocSemiringₓ

variable [NonUnitalNonAssocSemiringₓ α] (u v w : m → α)

@[simp]
theorem dot_product_zero : v ⬝ᵥ 0 = 0 := by
  simp [dot_product]

@[simp]
theorem dot_product_zero' : (v ⬝ᵥ fun _ => 0) = 0 :=
  dot_product_zero v

@[simp]
theorem zero_dot_product : 0 ⬝ᵥ v = 0 := by
  simp [dot_product]

@[simp]
theorem zero_dot_product' : (fun _ => (0 : α)) ⬝ᵥ v = 0 :=
  zero_dot_product v

@[simp]
theorem add_dot_product : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp [dot_product, add_mulₓ, Finset.sum_add_distrib]

@[simp]
theorem dot_product_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp [dot_product, mul_addₓ, Finset.sum_add_distrib]

end NonUnitalNonAssocSemiringₓ

section NonUnitalNonAssocSemiringDecidable

variable [DecidableEq m] [NonUnitalNonAssocSemiringₓ α] (u v w : m → α)

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (j «expr ≠ » i)
@[simp]
theorem diagonal_dot_product (i : m) : diagonalₓ v i ⬝ᵥ w = v i * w i := by
  have : ∀ j _ : j ≠ i, diagonalₓ v i j * w j = 0 := fun j hij => by
    simp [diagonal_apply_ne' hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (j «expr ≠ » i)
@[simp]
theorem dot_product_diagonal (i : m) : v ⬝ᵥ diagonalₓ w i = v i * w i := by
  have : ∀ j _ : j ≠ i, v j * diagonalₓ w i j = 0 := fun j hij => by
    simp [diagonal_apply_ne' hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (j «expr ≠ » i)
@[simp]
theorem dot_product_diagonal' (i : m) : (v ⬝ᵥ fun j => diagonalₓ w j i) = v i * w i := by
  have : ∀ j _ : j ≠ i, v j * diagonalₓ w j i = 0 := fun j hij => by
    simp [diagonal_apply_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (j «expr ≠ » i)
@[simp]
theorem single_dot_product (x : α) (i : m) : Pi.single i x ⬝ᵥ v = x * v i := by
  have : ∀ j _ : j ≠ i, Pi.single i x j * v j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (j «expr ≠ » i)
@[simp]
theorem dot_product_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x := by
  have : ∀ j _ : j ≠ i, v j * Pi.single i x j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

end NonUnitalNonAssocSemiringDecidable

section Ringₓ

variable [Ringₓ α] (u v w : m → α)

@[simp]
theorem neg_dot_product : -v ⬝ᵥ w = -(v ⬝ᵥ w) := by
  simp [dot_product]

@[simp]
theorem dot_product_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w) := by
  simp [dot_product]

@[simp]
theorem sub_dot_product : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w := by
  simp [sub_eq_add_neg]

@[simp]
theorem dot_product_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by
  simp [sub_eq_add_neg]

end Ringₓ

section DistribMulAction

variable [Monoidₓ R] [Mul α] [AddCommMonoidₓ α] [DistribMulAction R α]

@[simp]
theorem smul_dot_product [IsScalarTower R α α] (x : R) (v w : m → α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w) := by
  simp [dot_product, Finset.smul_sum, smul_mul_assoc]

@[simp]
theorem dot_product_smul [SmulCommClass R α α] (x : R) (v w : m → α) : v ⬝ᵥ x • w = x • (v ⬝ᵥ w) := by
  simp [dot_product, Finset.smul_sum, mul_smul_comm]

end DistribMulAction

section StarRing

variable [Semiringₓ α] [StarRing α] (v w : m → α)

theorem star_dot_product_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v) := by
  simp [dot_product]

theorem star_dot_product : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by
  simp [dot_product]

theorem dot_product_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v) := by
  simp [dot_product]

end StarRing

end DotProduct

open_locale Matrix

/-- `M ⬝ N` is the usual product of matrices `M` and `N`, i.e. we have that
`(M ⬝ N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `N`.
This is currently only defined when `m` is finite. -/
protected def mul [Fintype m] [Mul α] [AddCommMonoidₓ α] (M : Matrix l m α) (N : Matrix m n α) : Matrix l n α :=
  fun i k => (fun j => M i j) ⬝ᵥ fun j => N j k

-- mathport name: «expr ⬝ »
localized [Matrix] infixl:75 " ⬝ " => Matrix.mul

theorem mul_apply [Fintype m] [Mul α] [AddCommMonoidₓ α] {M : Matrix l m α} {N : Matrix m n α} {i k} :
    (M ⬝ N) i k = ∑ j, M i j * N j k :=
  rfl

instance [Fintype n] [Mul α] [AddCommMonoidₓ α] : Mul (Matrix n n α) :=
  ⟨Matrix.mul⟩

@[simp]
theorem mul_eq_mul [Fintype n] [Mul α] [AddCommMonoidₓ α] (M N : Matrix n n α) : M * N = M ⬝ N :=
  rfl

theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoidₓ α] {M : Matrix l m α} {N : Matrix m n α} {i k} :
    (M ⬝ N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k :=
  rfl

@[simp]
theorem diagonal_neg [DecidableEq n] [AddGroupₓ α] (d : n → α) : -diagonalₓ d = diagonalₓ fun i => -d i :=
  ((diagonalAddMonoidHom n α).map_neg d).symm

theorem sum_apply [AddCommMonoidₓ α] (i : m) (j : n) (s : Finset β) (g : β → Matrix m n α) :
    (∑ c in s, g c) i j = ∑ c in s, g c i j :=
  (congr_funₓ (s.sum_apply i g) j).trans (s.sum_apply j _)

section NonUnitalNonAssocSemiringₓ

variable [NonUnitalNonAssocSemiringₓ α]

@[simp]
protected theorem mul_zero [Fintype n] (M : Matrix m n α) : M ⬝ (0 : Matrix n o α) = 0 := by
  ext i j
  apply dot_product_zero

@[simp]
protected theorem zero_mul [Fintype m] (M : Matrix m n α) : (0 : Matrix l m α) ⬝ M = 0 := by
  ext i j
  apply zero_dot_product

protected theorem mul_add [Fintype n] (L : Matrix m n α) (M N : Matrix n o α) : L ⬝ (M + N) = L ⬝ M + L ⬝ N := by
  ext i j
  apply dot_product_add

protected theorem add_mul [Fintype m] (L M : Matrix l m α) (N : Matrix m n α) : (L + M) ⬝ N = L ⬝ N + M ⬝ N := by
  ext i j
  apply add_dot_product

instance [Fintype n] : NonUnitalNonAssocSemiringₓ (Matrix n n α) :=
  { Matrix.addCommMonoid with mul := (· * ·), add := (· + ·), zero := 0, mul_zero := Matrix.mul_zero,
    zero_mul := Matrix.zero_mul, left_distrib := Matrix.mul_add, right_distrib := Matrix.add_mul }

@[simp]
theorem diagonal_mul [Fintype m] [DecidableEq m] (d : m → α) (M : Matrix m n α) i j :
    (diagonalₓ d).mul M i j = d i * M i j :=
  diagonal_dot_product _ _ _

@[simp]
theorem mul_diagonal [Fintype n] [DecidableEq n] (d : n → α) (M : Matrix m n α) i j :
    (M ⬝ diagonalₓ d) i j = M i j * d j := by
  rw [← diagonal_transpose]
  apply dot_product_diagonal

@[simp]
theorem diagonal_mul_diagonal [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonalₓ d₁ ⬝ diagonalₓ d₂ = diagonalₓ fun i => d₁ i * d₂ i := by
  ext i j <;> by_cases' i = j <;> simp [h]

theorem diagonal_mul_diagonal' [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
    diagonalₓ d₁ * diagonalₓ d₂ = diagonalₓ fun i => d₁ i * d₂ i :=
  diagonal_mul_diagonal _ _

/-- Left multiplication by a matrix, as an `add_monoid_hom` from matrices to matrices. -/
@[simps]
def addMonoidHomMulLeft [Fintype m] (M : Matrix l m α) : Matrix m n α →+ Matrix l n α where
  toFun := fun x => M ⬝ x
  map_zero' := Matrix.mul_zero _
  map_add' := Matrix.mul_add _

/-- Right multiplication by a matrix, as an `add_monoid_hom` from matrices to matrices. -/
@[simps]
def addMonoidHomMulRight [Fintype m] (M : Matrix m n α) : Matrix l m α →+ Matrix l n α where
  toFun := fun x => x ⬝ M
  map_zero' := Matrix.zero_mul _
  map_add' := fun _ _ => Matrix.add_mul _ _ _

protected theorem sum_mul [Fintype m] (s : Finset β) (f : β → Matrix l m α) (M : Matrix m n α) :
    (∑ a in s, f a) ⬝ M = ∑ a in s, f a ⬝ M :=
  (addMonoidHomMulRight M : Matrix l m α →+ _).map_sum f s

protected theorem mul_sum [Fintype m] (s : Finset β) (f : β → Matrix m n α) (M : Matrix l m α) :
    (M ⬝ ∑ a in s, f a) = ∑ a in s, M ⬝ f a :=
  (addMonoidHomMulLeft M : Matrix m n α →+ _).map_sum f s

end NonUnitalNonAssocSemiringₓ

section NonAssocSemiringₓ

variable [NonAssocSemiringₓ α]

@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) : (1 : Matrix m m α) ⬝ M = M := by
  ext i j <;> rw [← diagonal_one, diagonal_mul, one_mulₓ]

@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) : M ⬝ (1 : Matrix n n α) = M := by
  ext i j <;> rw [← diagonal_one, mul_diagonal, mul_oneₓ]

instance [Fintype n] [DecidableEq n] : NonAssocSemiringₓ (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring with one := 1, one_mul := Matrix.one_mul, mul_one := Matrix.mul_one }

@[simp]
theorem map_mul [Fintype n] {L : Matrix m n α} {M : Matrix n o α} [NonAssocSemiringₓ β] {f : α →+* β} :
    (L ⬝ M).map f = L.map f ⬝ M.map f := by
  ext
  simp [mul_apply, RingHom.map_sum]

variable (α n)

/-- `matrix.diagonal` as a `ring_hom`. -/
@[simps]
def diagonalRingHom [Fintype n] [DecidableEq n] : (n → α) →+* Matrix n n α :=
  { diagonalAddMonoidHom n α with toFun := diagonalₓ, map_one' := diagonal_one,
    map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }

end NonAssocSemiringₓ

section NonUnitalSemiringₓ

variable [NonUnitalSemiringₓ α] [Fintype m] [Fintype n]

protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) : L ⬝ M ⬝ N = L ⬝ (M ⬝ N) := by
  ext
  apply dot_product_assoc

instance : NonUnitalSemiringₓ (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring with mul_assoc := Matrix.mul_assoc }

end NonUnitalSemiringₓ

section Semiringₓ

variable [Semiringₓ α]

instance [Fintype n] [DecidableEq n] : Semiringₓ (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.nonAssocSemiring with }

end Semiringₓ

section Ringₓ

variable [Ringₓ α] [Fintype n]

@[simp]
protected theorem neg_mul (M : Matrix m n α) (N : Matrix n o α) : -M ⬝ N = -(M ⬝ N) := by
  ext
  apply neg_dot_product

@[simp]
protected theorem mul_neg (M : Matrix m n α) (N : Matrix n o α) : M ⬝ -N = -(M ⬝ N) := by
  ext
  apply dot_product_neg

protected theorem sub_mul (M M' : Matrix m n α) (N : Matrix n o α) : (M - M') ⬝ N = M ⬝ N - M' ⬝ N := by
  rw [sub_eq_add_neg, Matrix.add_mul, Matrix.neg_mul, sub_eq_add_neg]

protected theorem mul_sub (M : Matrix m n α) (N N' : Matrix n o α) : M ⬝ (N - N') = M ⬝ N - M ⬝ N' := by
  rw [sub_eq_add_neg, Matrix.mul_add, Matrix.mul_neg, sub_eq_add_neg]

end Ringₓ

instance [Fintype n] [DecidableEq n] [Ringₓ α] : Ringₓ (Matrix n n α) :=
  { Matrix.semiring, Matrix.addCommGroup with }

section Semiringₓ

variable [Semiringₓ α]

theorem smul_eq_diagonal_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α) :
    a • M = (diagonalₓ fun _ => a) ⬝ M := by
  ext
  simp

@[simp]
theorem smul_mul [Fintype n] [Monoidₓ R] [DistribMulAction R α] [IsScalarTower R α α] (a : R) (M : Matrix m n α)
    (N : Matrix n l α) : (a • M) ⬝ N = a • M ⬝ N := by
  ext
  apply smul_dot_product

/-- This instance enables use with `smul_mul_assoc`. -/
instance semiring.is_scalar_tower [Fintype n] [Monoidₓ R] [DistribMulAction R α] [IsScalarTower R α α] :
    IsScalarTower R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => Matrix.smul_mul r m n⟩

@[simp]
theorem mul_smul [Fintype n] [Monoidₓ R] [DistribMulAction R α] [SmulCommClass R α α] (M : Matrix m n α) (a : R)
    (N : Matrix n l α) : M ⬝ (a • N) = a • M ⬝ N := by
  ext
  apply dot_product_smul

/-- This instance enables use with `mul_smul_comm`. -/
instance semiring.smul_comm_class [Fintype n] [Monoidₓ R] [DistribMulAction R α] [SmulCommClass R α α] :
    SmulCommClass R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩

@[simp]
theorem mul_mul_left [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (fun i j => a * M i j) ⬝ N = a • M ⬝ N :=
  smul_mul a M N

/-- The ring homomorphism `α →+* matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar (n : Type u) [DecidableEq n] [Fintype n] : α →+* Matrix n n α :=
  { (smulAddHom α _).flip (1 : Matrix n n α) with toFun := fun a => a • 1,
    map_one' := by
      simp ,
    map_mul' := by
      intros
      ext
      simp [mul_assoc] }

section Scalar

variable [DecidableEq n] [Fintype n]

@[simp]
theorem coe_scalar : (scalar n : α → Matrix n n α) = fun a => a • 1 :=
  rfl

theorem scalar_apply_eq (a : α) (i : n) : scalar n a i i = a := by
  simp only [coe_scalar, smul_eq_mul, mul_oneₓ, one_apply_eq, Pi.smul_apply]

theorem scalar_apply_ne (a : α) (i j : n) (h : i ≠ j) : scalar n a i j = 0 := by
  simp only [h, coe_scalar, one_apply_ne, Ne.def, not_false_iff, Pi.smul_apply, smul_zero]

theorem scalar_inj [Nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s := by
  constructor
  · intro h
    inhabit n
    rw [← scalar_apply_eq r (arbitrary n), ← scalar_apply_eq s (arbitrary n), h]
    
  · rintro rfl
    rfl
    

end Scalar

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ α] [Fintype n]

theorem smul_eq_mul_diagonal [DecidableEq n] (M : Matrix m n α) (a : α) : a • M = M ⬝ diagonalₓ fun _ => a := by
  ext
  simp [mul_comm]

@[simp]
theorem mul_mul_right (M : Matrix m n α) (N : Matrix n o α) (a : α) : (M ⬝ fun i j => a * N i j) = a • M ⬝ N :=
  mul_smul M a N

theorem scalar.commute [DecidableEq n] (r : α) (M : Matrix n n α) : Commute (scalar n r) M := by
  simp [Commute, SemiconjBy]

end CommSemiringₓ

section Algebra

variable [Fintype n] [DecidableEq n]

variable [CommSemiringₓ R] [Semiringₓ α] [Semiringₓ β] [Algebra R α] [Algebra R β]

instance : Algebra R (Matrix n n α) :=
  { (Matrix.scalar n).comp (algebraMap R α) with
    commutes' := fun r x => by
      ext
      simp [Matrix.scalar, Matrix.mul_apply, Matrix.one_apply, Algebra.commutes, smul_ite],
    smul_def' := fun r x => by
      ext
      simp [Matrix.scalar, Algebra.smul_def r] }

theorem algebra_map_matrix_apply {r : R} {i j : n} :
    algebraMap R (Matrix n n α) r i j = if i = j then algebraMap R α r else 0 := by
  dsimp [algebraMap, Algebra.toRingHom, Matrix.scalar]
  split_ifs with h <;> simp [h, Matrix.one_apply_ne]

theorem algebra_map_eq_diagonal (r : R) : algebraMap R (Matrix n n α) r = diagonalₓ (algebraMap R (n → α) r) :=
  Matrix.ext fun i j => algebra_map_matrix_apply

@[simp]
theorem algebra_map_eq_smul (r : R) : algebraMap R (Matrix n n R) r = r • (1 : Matrix n n R) :=
  rfl

theorem algebra_map_eq_diagonal_ring_hom : algebraMap R (Matrix n n α) = (diagonalRingHom n α).comp (algebraMap R _) :=
  RingHom.ext algebra_map_eq_diagonal

@[simp]
theorem map_algebra_map (r : R) (f : α → β) (hf : f 0 = 0) (hf₂ : f (algebraMap R α r) = algebraMap R β r) :
    (algebraMap R (Matrix n n α) r).map f = algebraMap R (Matrix n n β) r := by
  rw [algebra_map_eq_diagonal, algebra_map_eq_diagonal, diagonal_map hf]
  congr 1 with x
  simp only [hf₂, Pi.algebra_map_apply]

variable (R)

/-- `matrix.diagonal` as an `alg_hom`. -/
@[simps]
def diagonalAlgHom : (n → α) →ₐ[R] Matrix n n α :=
  { diagonalRingHom n α with toFun := diagonalₓ, commutes' := fun r => (algebra_map_eq_diagonal r).symm }

end Algebra

end Matrix

/-!
### Bundled versions of `matrix.map`
-/


namespace Equivₓ

/-- The `equiv` between spaces of matrices induced by an `equiv` between their
coefficients. This is `matrix.map` as an `equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ β) : Matrix m n α ≃ Matrix m n β where
  toFun := fun M => M.map f
  invFun := fun M => M.map f.symm
  left_inv := fun M => Matrix.ext fun _ _ => f.symm_apply_apply _
  right_inv := fun M => Matrix.ext fun _ _ => f.apply_symm_apply _

@[simp]
theorem map_matrix_refl : (Equivₓ.refl α).mapMatrix = Equivₓ.refl (Matrix m n α) :=
  rfl

@[simp]
theorem map_matrix_symm (f : α ≃ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ _) :=
  rfl

@[simp]
theorem map_matrix_trans (f : α ≃ β) (g : β ≃ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ _) :=
  rfl

end Equivₓ

namespace AddMonoidHom

variable [AddZeroClass α] [AddZeroClass β] [AddZeroClass γ]

/-- The `add_monoid_hom` between spaces of matrices induced by an `add_monoid_hom` between their
coefficients. This is `matrix.map` as an `add_monoid_hom`. -/
@[simps]
def mapMatrix (f : α →+ β) : Matrix m n α →+ Matrix m n β where
  toFun := fun M => M.map f
  map_zero' := Matrix.map_zero f f.map_zero
  map_add' := Matrix.map_add f f.map_add

@[simp]
theorem map_matrix_id : (AddMonoidHom.id α).mapMatrix = AddMonoidHom.id (Matrix m n α) :=
  rfl

@[simp]
theorem map_matrix_comp (f : β →+ γ) (g : α →+ β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →+ _) :=
  rfl

end AddMonoidHom

namespace AddEquiv

variable [Add α] [Add β] [Add γ]

/-- The `add_equiv` between spaces of matrices induced by an `add_equiv` between their
coefficients. This is `matrix.map` as an `add_equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃+ β) : Matrix m n α ≃+ Matrix m n β :=
  { f.toEquiv.mapMatrix with toFun := fun M => M.map f, invFun := fun M => M.map f.symm,
    map_add' := Matrix.map_add f f.map_add }

@[simp]
theorem map_matrix_refl : (AddEquiv.refl α).mapMatrix = AddEquiv.refl (Matrix m n α) :=
  rfl

@[simp]
theorem map_matrix_symm (f : α ≃+ β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃+ _) :=
  rfl

@[simp]
theorem map_matrix_trans (f : α ≃+ β) (g : β ≃+ γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃+ _) :=
  rfl

end AddEquiv

namespace LinearMap

variable [Semiringₓ R] [AddCommMonoidₓ α] [AddCommMonoidₓ β] [AddCommMonoidₓ γ]

variable [Module R α] [Module R β] [Module R γ]

/-- The `linear_map` between spaces of matrices induced by a `linear_map` between their
coefficients. This is `matrix.map` as a `linear_map`. -/
@[simps]
def mapMatrix (f : α →ₗ[R] β) : Matrix m n α →ₗ[R] Matrix m n β where
  toFun := fun M => M.map f
  map_add' := Matrix.map_add f f.map_add
  map_smul' := fun r => Matrix.map_smul f r (f.map_smul r)

@[simp]
theorem map_matrix_id : LinearMap.id.mapMatrix = (LinearMap.id : Matrix m n α →ₗ[R] _) :=
  rfl

@[simp]
theorem map_matrix_comp (f : β →ₗ[R] γ) (g : α →ₗ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m n α →ₗ[R] _) :=
  rfl

end LinearMap

namespace LinearEquiv

variable [Semiringₓ R] [AddCommMonoidₓ α] [AddCommMonoidₓ β] [AddCommMonoidₓ γ]

variable [Module R α] [Module R β] [Module R γ]

/-- The `linear_equiv` between spaces of matrices induced by an `linear_equiv` between their
coefficients. This is `matrix.map` as an `linear_equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ₗ[R] β) : Matrix m n α ≃ₗ[R] Matrix m n β :=
  { f.toEquiv.mapMatrix, f.toLinearMap.mapMatrix with toFun := fun M => M.map f, invFun := fun M => M.map f.symm }

@[simp]
theorem map_matrix_refl : (LinearEquiv.refl R α).mapMatrix = LinearEquiv.refl R (Matrix m n α) :=
  rfl

@[simp]
theorem map_matrix_symm (f : α ≃ₗ[R] β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m n β ≃ₗ[R] _) :=
  rfl

@[simp]
theorem map_matrix_trans (f : α ≃ₗ[R] β) (g : β ≃ₗ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m n α ≃ₗ[R] _) :=
  rfl

end LinearEquiv

namespace RingHom

variable [Fintype m] [DecidableEq m]

variable [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] [NonAssocSemiringₓ γ]

/-- The `ring_hom` between spaces of square matrices induced by a `ring_hom` between their
coefficients. This is `matrix.map` as a `ring_hom`. -/
@[simps]
def mapMatrix (f : α →+* β) : Matrix m m α →+* Matrix m m β :=
  { f.toAddMonoidHom.mapMatrix with toFun := fun M => M.map f,
    map_one' := by
      simp ,
    map_mul' := fun L M => Matrix.map_mul }

@[simp]
theorem map_matrix_id : (RingHom.id α).mapMatrix = RingHom.id (Matrix m m α) :=
  rfl

@[simp]
theorem map_matrix_comp (f : β →+* γ) (g : α →+* β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →+* _) :=
  rfl

end RingHom

namespace RingEquiv

variable [Fintype m] [DecidableEq m]

variable [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] [NonAssocSemiringₓ γ]

/-- The `ring_equiv` between spaces of square matrices induced by a `ring_equiv` between their
coefficients. This is `matrix.map` as a `ring_equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃+* β) : Matrix m m α ≃+* Matrix m m β :=
  { f.toRingHom.mapMatrix, f.toAddEquiv.mapMatrix with toFun := fun M => M.map f, invFun := fun M => M.map f.symm }

@[simp]
theorem map_matrix_refl : (RingEquiv.refl α).mapMatrix = RingEquiv.refl (Matrix m m α) :=
  rfl

@[simp]
theorem map_matrix_symm (f : α ≃+* β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃+* _) :=
  rfl

@[simp]
theorem map_matrix_trans (f : α ≃+* β) (g : β ≃+* γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃+* _) :=
  rfl

end RingEquiv

namespace AlgHom

variable [Fintype m] [DecidableEq m]

variable [CommSemiringₓ R] [Semiringₓ α] [Semiringₓ β] [Semiringₓ γ]

variable [Algebra R α] [Algebra R β] [Algebra R γ]

/-- The `alg_hom` between spaces of square matrices induced by a `alg_hom` between their
coefficients. This is `matrix.map` as a `alg_hom`. -/
@[simps]
def mapMatrix (f : α →ₐ[R] β) : Matrix m m α →ₐ[R] Matrix m m β :=
  { f.toRingHom.mapMatrix with toFun := fun M => M.map f,
    commutes' := fun r => Matrix.map_algebra_map r f f.map_zero (f.commutes r) }

@[simp]
theorem map_matrix_id : (AlgHom.id R α).mapMatrix = AlgHom.id R (Matrix m m α) :=
  rfl

@[simp]
theorem map_matrix_comp (f : β →ₐ[R] γ) (g : α →ₐ[R] β) :
    f.mapMatrix.comp g.mapMatrix = ((f.comp g).mapMatrix : Matrix m m α →ₐ[R] _) :=
  rfl

end AlgHom

namespace AlgEquiv

variable [Fintype m] [DecidableEq m]

variable [CommSemiringₓ R] [Semiringₓ α] [Semiringₓ β] [Semiringₓ γ]

variable [Algebra R α] [Algebra R β] [Algebra R γ]

/-- The `alg_equiv` between spaces of square matrices induced by a `alg_equiv` between their
coefficients. This is `matrix.map` as a `alg_equiv`. -/
@[simps apply]
def mapMatrix (f : α ≃ₐ[R] β) : Matrix m m α ≃ₐ[R] Matrix m m β :=
  { f.toAlgHom.mapMatrix, f.toRingEquiv.mapMatrix with toFun := fun M => M.map f, invFun := fun M => M.map f.symm }

@[simp]
theorem map_matrix_refl : AlgEquiv.refl.mapMatrix = (AlgEquiv.refl : Matrix m m α ≃ₐ[R] _) :=
  rfl

@[simp]
theorem map_matrix_symm (f : α ≃ₐ[R] β) : f.mapMatrix.symm = (f.symm.mapMatrix : Matrix m m β ≃ₐ[R] _) :=
  rfl

@[simp]
theorem map_matrix_trans (f : α ≃ₐ[R] β) (g : β ≃ₐ[R] γ) :
    f.mapMatrix.trans g.mapMatrix = ((f.trans g).mapMatrix : Matrix m m α ≃ₐ[R] _) :=
  rfl

end AlgEquiv

open_locale Matrix

namespace Matrix

/-- For two vectors `w` and `v`, `vec_mul_vec w v i j` is defined to be `w i * v j`.
    Put another way, `vec_mul_vec w v` is exactly `col w ⬝ row v`. -/
def vecMulVecₓ [Mul α] (w : m → α) (v : n → α) : Matrix m n α
  | x, y => w x * v y

section NonUnitalNonAssocSemiringₓ

variable [NonUnitalNonAssocSemiringₓ α]

/-- `mul_vec M v` is the matrix-vector product of `M` and `v`, where `v` is seen as a column matrix.
    Put another way, `mul_vec M v` is the vector whose entries
    are those of `M ⬝ col v` (see `col_mul_vec`). -/
def mulVecₓ [Fintype n] (M : Matrix m n α) (v : n → α) : m → α
  | i => (fun j => M i j) ⬝ᵥ v

/-- `vec_mul v M` is the vector-matrix product of `v` and `M`, where `v` is seen as a row matrix.
    Put another way, `vec_mul v M` is the vector whose entries
    are those of `row v ⬝ M` (see `row_vec_mul`). -/
def vecMulₓ [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
  | j => v ⬝ᵥ fun i => M i j

/-- Left multiplication by a matrix, as an `add_monoid_hom` from vectors to vectors. -/
@[simps]
def mulVecₓ.addMonoidHomLeft [Fintype n] (v : n → α) : Matrix m n α →+ m → α where
  toFun := fun M => mulVecₓ M v
  map_zero' := by
    ext <;> simp [mul_vec] <;> rfl
  map_add' := fun x y => by
    ext m
    apply add_dot_product

theorem mul_vec_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) : mulVecₓ (diagonalₓ v) w x = v x * w x :=
  diagonal_dot_product v w x

theorem vec_mul_diagonal [Fintype m] [DecidableEq m] (v w : m → α) (x : m) : vecMulₓ v (diagonalₓ w) x = v x * w x :=
  dot_product_diagonal' v w x

/-- Associate the dot product of `mul_vec` to the left. -/
theorem dot_product_mul_vec [Fintype n] [Fintype m] [NonUnitalSemiringₓ R] (v : m → R) (A : Matrix m n R) (w : n → R) :
    v ⬝ᵥ mulVecₓ A w = vecMulₓ v A ⬝ᵥ w := by
  simp only [dot_product, vec_mul, mul_vec, Finset.mul_sum, Finset.sum_mul, mul_assoc] <;> exact Finset.sum_comm

@[simp]
theorem mul_vec_zero [Fintype n] (A : Matrix m n α) : mulVecₓ A 0 = 0 := by
  ext
  simp [mul_vec]

@[simp]
theorem zero_vec_mul [Fintype m] (A : Matrix m n α) : vecMulₓ 0 A = 0 := by
  ext
  simp [vec_mul]

@[simp]
theorem zero_mul_vec [Fintype n] (v : n → α) : mulVecₓ (0 : Matrix m n α) v = 0 := by
  ext
  simp [mul_vec]

@[simp]
theorem vec_mul_zero [Fintype m] (v : m → α) : vecMulₓ v (0 : Matrix m n α) = 0 := by
  ext
  simp [vec_mul]

theorem vec_mul_vec_eq (w : m → α) (v : n → α) : vecMulVecₓ w v = colₓ w ⬝ rowₓ v := by
  ext i j
  simp [vec_mul_vec, mul_apply]
  rfl

theorem smul_mul_vec_assoc [Fintype n] [Monoidₓ R] [DistribMulAction R α] [IsScalarTower R α α] (a : R)
    (A : Matrix m n α) (b : n → α) : (a • A).mulVec b = a • A.mulVec b := by
  ext
  apply smul_dot_product

theorem mul_vec_add [Fintype n] (A : Matrix m n α) (x y : n → α) : A.mulVec (x + y) = A.mulVec x + A.mulVec y := by
  ext
  apply dot_product_add

theorem add_mul_vec [Fintype n] (A B : Matrix m n α) (x : n → α) : (A + B).mulVec x = A.mulVec x + B.mulVec x := by
  ext
  apply add_dot_product

theorem vec_mul_add [Fintype m] (A B : Matrix m n α) (x : m → α) : vecMulₓ x (A + B) = vecMulₓ x A + vecMulₓ x B := by
  ext
  apply dot_product_add

theorem add_vec_mul [Fintype m] (A : Matrix m n α) (x y : m → α) : vecMulₓ (x + y) A = vecMulₓ x A + vecMulₓ y A := by
  ext
  apply add_dot_product

theorem vec_mul_smul [Fintype n] [CommSemiringₓ R] [Semiringₓ S] [Algebra R S] (M : Matrix n m S) (b : R) (v : n → S) :
    M.vecMul (b • v) = b • M.vecMul v := by
  ext i
  simp only [vec_mul, dot_product, Finset.smul_sum, Pi.smul_apply, smul_mul_assoc]

theorem mul_vec_smul [Fintype n] [CommSemiringₓ R] [Semiringₓ S] [Algebra R S] (M : Matrix m n S) (b : R) (v : n → S) :
    M.mulVec (b • v) = b • M.mulVec v := by
  ext i
  simp only [mul_vec, dot_product, Finset.smul_sum, Pi.smul_apply, mul_smul_comm]

end NonUnitalNonAssocSemiringₓ

section NonUnitalSemiringₓ

variable [NonUnitalSemiringₓ α] [Fintype n]

@[simp]
theorem vec_mul_vec_mul [Fintype m] (v : m → α) (M : Matrix m n α) (N : Matrix n o α) :
    vecMulₓ (vecMulₓ v M) N = vecMulₓ v (M ⬝ N) := by
  ext
  apply dot_product_assoc

@[simp]
theorem mul_vec_mul_vec [Fintype o] (v : o → α) (M : Matrix m n α) (N : Matrix n o α) :
    mulVecₓ M (mulVecₓ N v) = mulVecₓ (M ⬝ N) v := by
  ext
  symm
  apply dot_product_assoc

end NonUnitalSemiringₓ

section NonAssocSemiringₓ

variable [Fintype m] [DecidableEq m] [NonAssocSemiringₓ α]

@[simp]
theorem one_mul_vec (v : m → α) : mulVecₓ 1 v = v := by
  ext
  rw [← diagonal_one, mul_vec_diagonal, one_mulₓ]

@[simp]
theorem vec_mul_one (v : m → α) : vecMulₓ v 1 = v := by
  ext
  rw [← diagonal_one, vec_mul_diagonal, mul_oneₓ]

end NonAssocSemiringₓ

section Ringₓ

variable [Ringₓ α]

theorem neg_vec_mul [Fintype m] (v : m → α) (A : Matrix m n α) : vecMulₓ (-v) A = -vecMulₓ v A := by
  ext
  apply neg_dot_product

theorem vec_mul_neg [Fintype m] (v : m → α) (A : Matrix m n α) : vecMulₓ v (-A) = -vecMulₓ v A := by
  ext
  apply dot_product_neg

theorem neg_mul_vec [Fintype n] (v : n → α) (A : Matrix m n α) : mulVecₓ (-A) v = -mulVecₓ A v := by
  ext
  apply neg_dot_product

theorem mul_vec_neg [Fintype n] (v : n → α) (A : Matrix m n α) : mulVecₓ A (-v) = -mulVecₓ A v := by
  ext
  apply dot_product_neg

end Ringₓ

section CommSemiringₓ

variable [CommSemiringₓ α]

theorem mul_vec_smul_assoc [Fintype n] (A : Matrix m n α) (b : n → α) (a : α) : A.mulVec (a • b) = a • A.mulVec b := by
  ext
  apply dot_product_smul

theorem mul_vec_transpose [Fintype m] (A : Matrix m n α) (x : m → α) : mulVecₓ Aᵀ x = vecMulₓ x A := by
  ext
  apply dot_product_comm

theorem vec_mul_transpose [Fintype n] (A : Matrix m n α) (x : n → α) : vecMulₓ x Aᵀ = mulVecₓ A x := by
  ext
  apply dot_product_comm

end CommSemiringₓ

section Transpose

open_locale Matrix

/-- Tell `simp` what the entries are in a transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp]
theorem transpose_apply (M : Matrix m n α) i j : M.transpose j i = M i j :=
  rfl

@[simp]
theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by
  ext <;> rfl

@[simp]
theorem transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0 := by
  ext i j <;> rfl

@[simp]
theorem transpose_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α)ᵀ = 1 := by
  ext i j
  unfold One.one transpose
  by_cases' i = j
  · simp only [h, diagonal_apply_eq]
    
  · simp only [diagonal_apply_ne h, diagonal_apply_ne fun p => h (symm p)]
    

@[simp]
theorem transpose_add [Add α] (M : Matrix m n α) (N : Matrix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ := by
  ext i j
  simp

@[simp]
theorem transpose_sub [Sub α] (M : Matrix m n α) (N : Matrix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ := by
  ext i j
  simp

@[simp]
theorem transpose_mul [CommSemiringₓ α] [Fintype n] (M : Matrix m n α) (N : Matrix n l α) : (M ⬝ N)ᵀ = Nᵀ ⬝ Mᵀ := by
  ext i j
  apply dot_product_comm

@[simp]
theorem transpose_smul {R : Type _} [HasScalar R α] (c : R) (M : Matrix m n α) : (c • M)ᵀ = c • Mᵀ := by
  ext i j
  rfl

@[simp]
theorem transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ = -Mᵀ := by
  ext i j <;> rfl

theorem transpose_map {f : α → β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ := by
  ext
  rfl

/-- `matrix.transpose` as an `add_equiv` -/
@[simps apply]
def transposeAddEquiv [Add α] : Matrix m n α ≃+ Matrix n m α where
  toFun := transposeₓ
  invFun := transposeₓ
  left_inv := transpose_transpose
  right_inv := transpose_transpose
  map_add' := transpose_add

@[simp]
theorem transpose_add_equiv_symm [Add α] :
    (transposeAddEquiv : Matrix m n α ≃+ Matrix n m α).symm = transpose_add_equiv :=
  rfl

theorem transpose_list_sum [AddMonoidₓ α] (l : List (Matrix m n α)) : l.Sumᵀ = (l.map transposeₓ).Sum :=
  (transposeAddEquiv : Matrix m n α ≃+ Matrix n m α).toAddMonoidHom.map_list_sum l

theorem transpose_multiset_sum [AddCommMonoidₓ α] (s : Multiset (Matrix m n α)) : s.Sumᵀ = (s.map transposeₓ).Sum :=
  (transposeAddEquiv : Matrix m n α ≃+ Matrix n m α).toAddMonoidHom.map_multiset_sum s

theorem transpose_sum [AddCommMonoidₓ α] {ι : Type _} (s : Finset ι) (M : ι → Matrix m n α) :
    (∑ i in s, M i)ᵀ = ∑ i in s, (M i)ᵀ :=
  (transposeAddEquiv : Matrix m n α ≃+ Matrix n m α).toAddMonoidHom.map_sum _ s

/-- `matrix.transpose` as a `ring_equiv` to the opposite ring -/
@[simps]
def transposeRingEquiv [CommSemiringₓ α] [Fintype m] : Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ :=
  { transposeAddEquiv.trans MulOpposite.opAddEquiv with toFun := fun M => MulOpposite.op Mᵀ, invFun := fun M => M.unopᵀ,
    map_mul' := fun M N => (congr_argₓ MulOpposite.op (transpose_mul M N)).trans (MulOpposite.op_mul _ _) }

theorem transpose_list_prod [CommSemiringₓ α] [Fintype m] [DecidableEq m] (l : List (Matrix m m α)) :
    l.Prodᵀ = (l.map transposeₓ).reverse.Prod :=
  (transposeRingEquiv : Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ).unop_map_list_prod l

end Transpose

section ConjTranspose

open_locale Matrix

/-- Tell `simp` what the entries are in a conjugate transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp]
theorem conj_transpose_apply [HasStar α] (M : Matrix m n α) i j : M.conjTranspose j i = star (M i j) :=
  rfl

@[simp]
theorem conj_transpose_conj_transpose [HasInvolutiveStar α] (M : Matrix m n α) : Mᴴᴴ = M := by
  ext <;> simp

@[simp]
theorem conj_transpose_zero [Semiringₓ α] [StarRing α] : (0 : Matrix m n α)ᴴ = 0 := by
  ext i j <;> simp

@[simp]
theorem conj_transpose_one [DecidableEq n] [Semiringₓ α] [StarRing α] : (1 : Matrix n n α)ᴴ = 1 := by
  simp [conj_transpose]

@[simp]
theorem conj_transpose_add [AddMonoidₓ α] [StarAddMonoid α] (M N : Matrix m n α) : (M + N)ᴴ = Mᴴ + Nᴴ := by
  ext i j <;> simp

@[simp]
theorem conj_transpose_sub [AddGroupₓ α] [StarAddMonoid α] (M N : Matrix m n α) : (M - N)ᴴ = Mᴴ - Nᴴ := by
  ext i j <;> simp

@[simp]
theorem conj_transpose_smul [CommMonoidₓ α] [StarSemigroup α] (c : α) (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ := by
  ext i j <;> simp [mul_comm]

@[simp]
theorem conj_transpose_mul [Fintype n] [Semiringₓ α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α) :
    (M ⬝ N)ᴴ = Nᴴ ⬝ Mᴴ := by
  ext i j <;> simp [mul_apply]

@[simp]
theorem conj_transpose_neg [Ringₓ α] [StarRing α] (M : Matrix m n α) : (-M)ᴴ = -Mᴴ := by
  ext i j <;> simp

/-- `matrix.conj_transpose` as an `add_equiv` -/
@[simps apply]
def conjTransposeAddEquiv [AddMonoidₓ α] [StarAddMonoid α] : Matrix m n α ≃+ Matrix n m α where
  toFun := conjTranspose
  invFun := conjTranspose
  left_inv := conj_transpose_conj_transpose
  right_inv := conj_transpose_conj_transpose
  map_add' := conj_transpose_add

@[simp]
theorem conj_transpose_add_equiv_symm [AddMonoidₓ α] [StarAddMonoid α] :
    (conjTransposeAddEquiv : Matrix m n α ≃+ Matrix n m α).symm = conj_transpose_add_equiv :=
  rfl

theorem conj_transpose_list_sum [AddMonoidₓ α] [StarAddMonoid α] (l : List (Matrix m n α)) :
    l.Sumᴴ = (l.map conjTranspose).Sum :=
  (conjTransposeAddEquiv : Matrix m n α ≃+ Matrix n m α).toAddMonoidHom.map_list_sum l

theorem conj_transpose_multiset_sum [AddCommMonoidₓ α] [StarAddMonoid α] (s : Multiset (Matrix m n α)) :
    s.Sumᴴ = (s.map conjTranspose).Sum :=
  (conjTransposeAddEquiv : Matrix m n α ≃+ Matrix n m α).toAddMonoidHom.map_multiset_sum s

theorem conj_transpose_sum [AddCommMonoidₓ α] [StarAddMonoid α] {ι : Type _} (s : Finset ι) (M : ι → Matrix m n α) :
    (∑ i in s, M i)ᴴ = ∑ i in s, (M i)ᴴ :=
  (conjTransposeAddEquiv : Matrix m n α ≃+ Matrix n m α).toAddMonoidHom.map_sum _ s

/-- `matrix.conj_transpose` as a `ring_equiv` to the opposite ring -/
@[simps]
def conjTransposeRingEquiv [CommSemiringₓ α] [StarRing α] [Fintype m] : Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ :=
  { conjTransposeAddEquiv.trans MulOpposite.opAddEquiv with toFun := fun M => MulOpposite.op Mᴴ,
    invFun := fun M => M.unopᴴ,
    map_mul' := fun M N => (congr_argₓ MulOpposite.op (conj_transpose_mul M N)).trans (MulOpposite.op_mul _ _) }

theorem conj_transpose_list_prod [CommSemiringₓ α] [StarRing α] [Fintype m] [DecidableEq m] (l : List (Matrix m m α)) :
    l.Prodᴴ = (l.map conjTranspose).reverse.Prod :=
  (conjTransposeRingEquiv : Matrix m m α ≃+* (Matrix m m α)ᵐᵒᵖ).unop_map_list_prod l

end ConjTranspose

section Star

/-- When `α` has a star operation, square matrices `matrix n n α` have a star
operation equal to `matrix.conj_transpose`. -/
instance [HasStar α] : HasStar (Matrix n n α) where
  star := conjTranspose

theorem star_eq_conj_transpose [HasStar α] (M : Matrix m m α) : star M = Mᴴ :=
  rfl

@[simp]
theorem star_apply [HasStar α] (M : Matrix n n α) i j : (star M) i j = star (M j i) :=
  rfl

instance [HasInvolutiveStar α] : HasInvolutiveStar (Matrix n n α) where
  star_involutive := conj_transpose_conj_transpose

/-- When `α` is a `*`-additive monoid, `matrix.has_star` is also a `*`-additive monoid. -/
instance [AddMonoidₓ α] [StarAddMonoid α] : StarAddMonoid (Matrix n n α) where
  star_add := conj_transpose_add

/-- When `α` is a `*`-(semi)ring, `matrix.has_star` is also a `*`-(semi)ring. -/
instance [Fintype n] [Semiringₓ α] [StarRing α] : StarRing (Matrix n n α) where
  star_add := conj_transpose_add
  star_mul := conj_transpose_mul

/-- A version of `star_mul` for `⬝` instead of `*`. -/
theorem star_mul [Fintype n] [Semiringₓ α] [StarRing α] (M N : Matrix n n α) : star (M ⬝ N) = star N ⬝ star M :=
  conj_transpose_mul _ _

end Star

/-- Given maps `(r_reindex : l → m)` and  `(c_reindex : o → n)` reindexing the rows and columns of
a matrix `M : matrix m n α`, the matrix `M.minor r_reindex c_reindex : matrix l o α` is defined
by `(M.minor r_reindex c_reindex) i j = M (r_reindex i) (c_reindex j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved. -/
def minor (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) : Matrix l o α := fun i j =>
  A (r_reindex i) (c_reindex j)

@[simp]
theorem minor_apply (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) i j :
    A.minor r_reindex c_reindex i j = A (r_reindex i) (c_reindex j) :=
  rfl

@[simp]
theorem minor_id_id (A : Matrix m n α) : A.minor id id = A :=
  ext fun _ _ => rfl

@[simp]
theorem minor_minor {l₂ o₂ : Type _} (A : Matrix m n α) (r₁ : l → m) (c₁ : o → n) (r₂ : l₂ → l) (c₂ : o₂ → o) :
    (A.minor r₁ c₁).minor r₂ c₂ = A.minor (r₁ ∘ r₂) (c₁ ∘ c₂) :=
  ext fun _ _ => rfl

@[simp]
theorem transpose_minor (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
    (A.minor r_reindex c_reindex)ᵀ = Aᵀ.minor c_reindex r_reindex :=
  ext fun _ _ => rfl

@[simp]
theorem conj_transpose_minor [HasStar α] (A : Matrix m n α) (r_reindex : l → m) (c_reindex : o → n) :
    (A.minor r_reindex c_reindex)ᴴ = Aᴴ.minor c_reindex r_reindex :=
  ext fun _ _ => rfl

theorem minor_add [Add α] (A B : Matrix m n α) :
    ((A + B).minor : (l → m) → (o → n) → Matrix l o α) = A.minor + B.minor :=
  rfl

theorem minor_neg [Neg α] (A : Matrix m n α) : ((-A).minor : (l → m) → (o → n) → Matrix l o α) = -A.minor :=
  rfl

theorem minor_sub [Sub α] (A B : Matrix m n α) :
    ((A - B).minor : (l → m) → (o → n) → Matrix l o α) = A.minor - B.minor :=
  rfl

@[simp]
theorem minor_zero [Zero α] : ((0 : Matrix m n α).minor : (l → m) → (o → n) → Matrix l o α) = 0 :=
  rfl

theorem minor_smul {R : Type _} [Semiringₓ R] [AddCommMonoidₓ α] [Module R α] (r : R) (A : Matrix m n α) :
    ((r • A : Matrix m n α).minor : (l → m) → (o → n) → Matrix l o α) = r • A.minor :=
  rfl

theorem minor_map (f : α → β) (e₁ : l → m) (e₂ : o → n) (A : Matrix m n α) :
    (A.map f).minor e₁ e₂ = (A.minor e₁ e₂).map f :=
  rfl

/-- Given a `(m × m)` diagonal matrix defined by a map `d : m → α`, if the reindexing map `e` is
  injective, then the resulting matrix is again diagonal. -/
theorem minor_diagonal [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l → m) (he : Function.Injective e) :
    (diagonalₓ d).minor e e = diagonalₓ (d ∘ e) :=
  ext fun i j => by
    rw [minor_apply]
    by_cases' h : i = j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq]
      
    · rw [diagonal_apply_ne h, diagonal_apply_ne (he.ne h)]
      

theorem minor_one [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l → m) (he : Function.Injective e) :
    (1 : Matrix m m α).minor e e = 1 :=
  minor_diagonal _ e he

theorem minor_mul [Fintype n] [Fintype o] [Semiringₓ α] {p q : Type _} (M : Matrix m n α) (N : Matrix n p α)
    (e₁ : l → m) (e₂ : o → n) (e₃ : q → p) (he₂ : Function.Bijective e₂) :
    (M ⬝ N).minor e₁ e₃ = M.minor e₁ e₂ ⬝ N.minor e₂ e₃ :=
  ext fun _ _ => (he₂.sum_comp _).symm

/-! `simp` lemmas for `matrix.minor`s interaction with `matrix.diagonal`, `1`, and `matrix.mul` for
when the mappings are bundled. -/


@[simp]
theorem minor_diagonal_embedding [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l ↪ m) :
    (diagonalₓ d).minor e e = diagonalₓ (d ∘ e) :=
  minor_diagonal d e e.Injective

@[simp]
theorem minor_diagonal_equiv [Zero α] [DecidableEq m] [DecidableEq l] (d : m → α) (e : l ≃ m) :
    (diagonalₓ d).minor e e = diagonalₓ (d ∘ e) :=
  minor_diagonal d e e.Injective

@[simp]
theorem minor_one_embedding [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m) :
    (1 : Matrix m m α).minor e e = 1 :=
  minor_one e e.Injective

@[simp]
theorem minor_one_equiv [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m) :
    (1 : Matrix m m α).minor e e = 1 :=
  minor_one e e.Injective

@[simp]
theorem minor_mul_equiv [Fintype n] [Fintype o] [Semiringₓ α] {p q : Type _} (M : Matrix m n α) (N : Matrix n p α)
    (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p) : M.minor e₁ e₂ ⬝ N.minor e₂ e₃ = (M ⬝ N).minor e₁ e₃ :=
  (minor_mul M N e₁ e₂ e₃ e₂.Bijective).symm

theorem mul_minor_one [Fintype n] [Fintype o] [Semiringₓ α] [DecidableEq o] (e₁ : n ≃ o) (e₂ : l → o)
    (M : Matrix m n α) : M ⬝ (1 : Matrix o o α).minor e₁ e₂ = minor M id (e₁.symm ∘ e₂) := by
  let A := M.minor id e₁.symm
  have : M = A.minor id e₁ := by
    simp only [minor_minor, Function.comp.right_id, minor_id_id, Equivₓ.symm_comp_self]
  rw [this, minor_mul_equiv]
  simp only [Matrix.mul_one, minor_minor, Function.comp.right_id, minor_id_id, Equivₓ.symm_comp_self]

theorem one_minor_mul [Fintype m] [Fintype o] [Semiringₓ α] [DecidableEq o] (e₁ : l → o) (e₂ : m ≃ o)
    (M : Matrix m n α) : ((1 : Matrix o o α).minor e₁ e₂).mul M = minor M (e₂.symm ∘ e₁) id := by
  let A := M.minor e₂.symm id
  have : M = A.minor e₂ id := by
    simp only [minor_minor, Function.comp.right_id, minor_id_id, Equivₓ.symm_comp_self]
  rw [this, minor_mul_equiv]
  simp only [Matrix.one_mul, minor_minor, Function.comp.right_id, minor_id_id, Equivₓ.symm_comp_self]

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : Matrix m n α ≃ Matrix l o α where
  toFun := fun M => M.minor eₘ.symm eₙ.symm
  invFun := fun M => M.minor eₘ eₙ
  left_inv := fun M => by
    simp
  right_inv := fun M => by
    simp

@[simp]
theorem reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) : reindex eₘ eₙ M = M.minor eₘ.symm eₙ.symm :=
  rfl

@[simp]
theorem reindex_refl_refl (A : Matrix m n α) : reindex (Equivₓ.refl _) (Equivₓ.refl _) A = A :=
  A.minor_id_id

@[simp]
theorem reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) : (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : Matrix l o α ≃ _) :=
  rfl

@[simp]
theorem reindex_trans {l₂ o₂ : Type _} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
    (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) = (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) :=
  Equivₓ.ext fun A => (A.minor_minor eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm : _)

theorem transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) : (reindex eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ :=
  rfl

theorem conj_transpose_reindex [HasStar α] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᴴ = reindex eₙ eₘ Mᴴ :=
  rfl

@[simp]
theorem minor_mul_transpose_minor [Fintype n] [Fintype m] [Semiringₓ α] (e : n ≃ m) (M : Matrix n m α) :
    M.minor id e ⬝ Mᵀ.minor e id = M ⬝ Mᵀ := by
  rw [minor_mul_equiv, minor_id_id]

/-- The left `n × l` part of a `n × (l+r)` matrix. -/
@[reducible]
def subLeft {m l r : Nat} (A : Matrix (Finₓ m) (Finₓ (l + r)) α) : Matrix (Finₓ m) (Finₓ l) α :=
  minor A id (Finₓ.castAdd r)

/-- The right `n × r` part of a `n × (l+r)` matrix. -/
@[reducible]
def subRight {m l r : Nat} (A : Matrix (Finₓ m) (Finₓ (l + r)) α) : Matrix (Finₓ m) (Finₓ r) α :=
  minor A id (Finₓ.natAdd l)

/-- The top `u × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def subUp {d u n : Nat} (A : Matrix (Finₓ (u + d)) (Finₓ n) α) : Matrix (Finₓ u) (Finₓ n) α :=
  minor A (Finₓ.castAdd d) id

/-- The bottom `d × n` part of a `(u+d) × n` matrix. -/
@[reducible]
def subDown {d u n : Nat} (A : Matrix (Finₓ (u + d)) (Finₓ n) α) : Matrix (Finₓ d) (Finₓ n) α :=
  minor A (Finₓ.natAdd u) id

/-- The top-right `u × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subUpRight {d u l r : Nat} (A : Matrix (Finₓ (u + d)) (Finₓ (l + r)) α) : Matrix (Finₓ u) (Finₓ r) α :=
  subUp (subRight A)

/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subDownRight {d u l r : Nat} (A : Matrix (Finₓ (u + d)) (Finₓ (l + r)) α) : Matrix (Finₓ d) (Finₓ r) α :=
  subDown (subRight A)

/-- The top-left `u × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subUpLeft {d u l r : Nat} (A : Matrix (Finₓ (u + d)) (Finₓ (l + r)) α) : Matrix (Finₓ u) (Finₓ l) α :=
  subUp (subLeft A)

/-- The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix. -/
@[reducible]
def subDownLeft {d u l r : Nat} (A : Matrix (Finₓ (u + d)) (Finₓ (l + r)) α) : Matrix (Finₓ d) (Finₓ l) α :=
  subDown (subLeft A)

section RowCol

/-!
### `row_col` section

Simplification lemmas for `matrix.row` and `matrix.col`.
-/


open_locale Matrix

@[simp]
theorem col_add [Add α] (v w : m → α) : colₓ (v + w) = colₓ v + colₓ w := by
  ext
  rfl

@[simp]
theorem col_smul [HasScalar R α] (x : R) (v : m → α) : colₓ (x • v) = x • colₓ v := by
  ext
  rfl

@[simp]
theorem row_add [Add α] (v w : m → α) : rowₓ (v + w) = rowₓ v + rowₓ w := by
  ext
  rfl

@[simp]
theorem row_smul [HasScalar R α] (x : R) (v : m → α) : rowₓ (x • v) = x • rowₓ v := by
  ext
  rfl

@[simp]
theorem col_apply (v : m → α) i j : Matrix.colₓ v i j = v i :=
  rfl

@[simp]
theorem row_apply (v : m → α) i j : Matrix.rowₓ v i j = v j :=
  rfl

@[simp]
theorem transpose_col (v : m → α) : (Matrix.colₓ v)ᵀ = Matrix.rowₓ v := by
  ext
  rfl

@[simp]
theorem transpose_row (v : m → α) : (Matrix.rowₓ v)ᵀ = Matrix.colₓ v := by
  ext
  rfl

@[simp]
theorem conj_transpose_col [HasStar α] (v : m → α) : (colₓ v)ᴴ = rowₓ (star v) := by
  ext
  rfl

@[simp]
theorem conj_transpose_row [HasStar α] (v : m → α) : (rowₓ v)ᴴ = colₓ (star v) := by
  ext
  rfl

theorem row_vec_mul [Fintype m] [Semiringₓ α] (M : Matrix m n α) (v : m → α) :
    Matrix.rowₓ (Matrix.vecMulₓ v M) = Matrix.rowₓ v ⬝ M := by
  ext
  rfl

theorem col_vec_mul [Fintype m] [Semiringₓ α] (M : Matrix m n α) (v : m → α) :
    Matrix.colₓ (Matrix.vecMulₓ v M) = (Matrix.rowₓ v ⬝ M)ᵀ := by
  ext
  rfl

theorem col_mul_vec [Fintype n] [Semiringₓ α] (M : Matrix m n α) (v : n → α) :
    Matrix.colₓ (Matrix.mulVecₓ M v) = M ⬝ Matrix.colₓ v := by
  ext
  rfl

theorem row_mul_vec [Fintype n] [Semiringₓ α] (M : Matrix m n α) (v : n → α) :
    Matrix.rowₓ (Matrix.mulVecₓ M v) = (M ⬝ Matrix.colₓ v)ᵀ := by
  ext
  rfl

@[simp]
theorem row_mul_col_apply [Fintype m] [Mul α] [AddCommMonoidₓ α] (v w : m → α) i j : (rowₓ v ⬝ colₓ w) i j = v ⬝ᵥ w :=
  rfl

end RowCol

section Update

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def updateRow [DecidableEq n] (M : Matrix n m α) (i : n) (b : m → α) : Matrix n m α :=
  Function.update M i b

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def updateColumn [DecidableEq m] (M : Matrix n m α) (j : m) (b : n → α) : Matrix n m α := fun i =>
  Function.update (M i) j (b i)

variable {M : Matrix n m α} {i : n} {j : m} {b : m → α} {c : n → α}

@[simp]
theorem update_row_self [DecidableEq n] : updateRow M i b i = b :=
  Function.update_same i b M

@[simp]
theorem update_column_self [DecidableEq m] : updateColumn M j c i j = c i :=
  Function.update_same j (c i) (M i)

@[simp]
theorem update_row_ne [DecidableEq n] {i' : n} (i_ne : i' ≠ i) : updateRow M i b i' = M i' :=
  Function.update_noteq i_ne b M

@[simp]
theorem update_column_ne [DecidableEq m] {j' : m} (j_ne : j' ≠ j) : updateColumn M j c i j' = M i j' :=
  Function.update_noteq j_ne (c i) (M i)

theorem update_row_apply [DecidableEq n] {i' : n} : updateRow M i b i' j = if i' = i then b j else M i' j := by
  by_cases' i' = i
  · rw [h, update_row_self, if_pos rfl]
    
  · rwa [update_row_ne h, if_neg h]
    

theorem update_column_apply [DecidableEq m] {j' : m} : updateColumn M j c i j' = if j' = j then c i else M i j' := by
  by_cases' j' = j
  · rw [h, update_column_self, if_pos rfl]
    
  · rwa [update_column_ne h, if_neg h]
    

@[simp]
theorem update_column_subsingleton [Subsingleton m] (A : Matrix n m R) (i : m) (b : n → R) :
    A.updateColumn i b = (colₓ b).minor id (Function.const m ()) := by
  ext x y
  simp [update_column_apply, Subsingleton.elimₓ i y]

@[simp]
theorem update_row_subsingleton [Subsingleton n] (A : Matrix n m R) (i : n) (b : m → R) :
    A.updateRow i b = (rowₓ b).minor (Function.const n ()) id := by
  ext x y
  simp [update_column_apply, Subsingleton.elimₓ i x]

theorem map_update_row [DecidableEq n] (f : α → β) : map (updateRow M i b) f = updateRow (M.map f) i (f ∘ b) := by
  ext i' j'
  rw [update_row_apply, map_apply, map_apply, update_row_apply]
  exact apply_ite f _ _ _

theorem map_update_column [DecidableEq m] (f : α → β) : map (updateColumn M j c) f = updateColumn (M.map f) j (f ∘ c) :=
  by
  ext i' j'
  rw [update_column_apply, map_apply, map_apply, update_column_apply]
  exact apply_ite f _ _ _

theorem update_row_transpose [DecidableEq m] : updateRow Mᵀ j c = (updateColumn M j c)ᵀ := by
  ext i' j
  rw [transpose_apply, update_row_apply, update_column_apply]
  rfl

theorem update_column_transpose [DecidableEq n] : updateColumn Mᵀ i b = (updateRow M i b)ᵀ := by
  ext i' j
  rw [transpose_apply, update_row_apply, update_column_apply]
  rfl

theorem update_row_conj_transpose [DecidableEq m] [HasStar α] : updateRow Mᴴ j (star c) = (updateColumn M j c)ᴴ := by
  rw [conj_transpose, conj_transpose, transpose_map, transpose_map, update_row_transpose, map_update_column]
  rfl

theorem update_column_conj_transpose [DecidableEq n] [HasStar α] : updateColumn Mᴴ i (star b) = (updateRow M i b)ᴴ := by
  rw [conj_transpose, conj_transpose, transpose_map, transpose_map, update_column_transpose, map_update_row]
  rfl

@[simp]
theorem update_row_eq_self [DecidableEq m] (A : Matrix m n α) {i : m} : A.updateRow i (A i) = A :=
  Function.update_eq_self i A

@[simp]
theorem update_column_eq_self [DecidableEq n] (A : Matrix m n α) {i : n} : (A.updateColumn i fun j => A j i) = A :=
  funext fun j => Function.update_eq_self i (A j)

end Update

end Matrix

namespace RingHom

variable [Fintype n] [Semiringₓ α] [Semiringₓ β]

theorem map_matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α →+* β) :
    f (Matrix.mul M N i j) = Matrix.mul (fun i j => f (M i j)) (fun i j => f (N i j)) i j := by
  simp [Matrix.mul_apply, RingHom.map_sum]

theorem map_dot_product [Semiringₓ R] [Semiringₓ S] (f : R →+* S) (v w : n → R) : f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w := by
  simp only [Matrix.dotProduct, f.map_sum, f.map_mul]

theorem map_vec_mul [Semiringₓ R] [Semiringₓ S] (f : R →+* S) (M : Matrix n m R) (v : n → R) (i : m) :
    f (M.vecMul v i) = (M.map f).vecMul (f ∘ v) i := by
  simp only [Matrix.vecMulₓ, Matrix.map_apply, RingHom.map_dot_product]

theorem map_mul_vec [Semiringₓ R] [Semiringₓ S] (f : R →+* S) (M : Matrix m n R) (v : n → R) (i : m) :
    f (M.mulVec v i) = (M.map f).mulVec (f ∘ v) i := by
  simp only [Matrix.mulVecₓ, Matrix.map_apply, RingHom.map_dot_product]

end RingHom

