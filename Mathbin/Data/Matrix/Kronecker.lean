import Mathbin.Data.Matrix.Basic
import Mathbin.LinearAlgebra.TensorProduct
import Mathbin.RingTheory.TensorProduct

/-!
# Kronecker product of matrices

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `matrix.kronecker_map`: A generalization of the Kronecker product: given a map `f : α → β → γ`
  and matrices `A` and `B` with coefficients in `α` and `β`, respectively, it is defined as the
  matrix with coefficients in `γ` such that
  `kronecker_map f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `matrix.kronecker_map_bilinear`: when `f` is bilinear, so is `kronecker_map f`.

## Specializations

* `matrix.kronecker`: An alias of `kronecker_map (*)`. Prefer using the notation.
* `matrix.kronecker_bilinear`: `matrix.kronecker` is bilinear

* `matrix.kronecker_tmul`: An alias of `kronecker_map (⊗ₜ)`. Prefer using the notation.
* `matrix.kronecker_tmul_bilinear`: `matrix.tmul_kronecker` is bilinear

## Notations

These require `open_locale kronecker`:

* `A ⊗ₖ B` for `kronecker_map (*) A B`. Lemmas about this notation use the token `kronecker`.
* `A ⊗ₖₜ B` and `A ⊗ₖₜ[R] B` for `kronecker_map (⊗ₜ) A B`.  Lemmas about this notation use the token
  `kronecker_tmul`.

-/


namespace Matrix

open_locale Matrix

variable {R α α' β β' γ γ' : Type _}

variable {l m n p : Type _} {q r : Type _} {l' m' n' p' : Type _}

section KroneckerMap

/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B`. -/
@[simp]
def kronecker_map (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) : Matrix (l × n) (m × p) γ
  | i, j => f (A i.1 j.1) (B i.2 j.2)

theorem kronecker_map_transpose (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) :
    kronecker_map f (A)ᵀ (B)ᵀ = (kronecker_map f A B)ᵀ :=
  ext $ fun i j => rfl

theorem kronecker_map_map_left (f : α' → β → γ) (g : α → α') (A : Matrix l m α) (B : Matrix n p β) :
    kronecker_map f (A.map g) B = kronecker_map (fun a b => f (g a) b) A B :=
  ext $ fun i j => rfl

theorem kronecker_map_map_right (f : α → β' → γ) (g : β → β') (A : Matrix l m α) (B : Matrix n p β) :
    kronecker_map f A (B.map g) = kronecker_map (fun a b => f a (g b)) A B :=
  ext $ fun i j => rfl

theorem kronecker_map_map (f : α → β → γ) (g : γ → γ') (A : Matrix l m α) (B : Matrix n p β) :
    (kronecker_map f A B).map g = kronecker_map (fun a b => g (f a b)) A B :=
  ext $ fun i j => rfl

@[simp]
theorem kronecker_map_zero_left [HasZero α] [HasZero γ] (f : α → β → γ) (hf : ∀ b, f 0 b = 0) (B : Matrix n p β) :
    kronecker_map f (0 : Matrix l m α) B = 0 :=
  ext $ fun i j => hf _

@[simp]
theorem kronecker_map_zero_right [HasZero β] [HasZero γ] (f : α → β → γ) (hf : ∀ a, f a 0 = 0) (A : Matrix l m α) :
    kronecker_map f A (0 : Matrix n p β) = 0 :=
  ext $ fun i j => hf _

theorem kronecker_map_add_left [Add α] [Add γ] (f : α → β → γ) (hf : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b)
    (A₁ A₂ : Matrix l m α) (B : Matrix n p β) :
    kronecker_map f (A₁ + A₂) B = kronecker_map f A₁ B + kronecker_map f A₂ B :=
  ext $ fun i j => hf _ _ _

theorem kronecker_map_add_right [Add β] [Add γ] (f : α → β → γ) (hf : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂)
    (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    kronecker_map f A (B₁ + B₂) = kronecker_map f A B₁ + kronecker_map f A B₂ :=
  ext $ fun i j => hf _ _ _

theorem kronecker_map_smul_left [HasScalar R α] [HasScalar R γ] (f : α → β → γ) (r : R)
    (hf : ∀ a b, f (r • a) b = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kronecker_map f (r • A) B = r • kronecker_map f A B :=
  ext $ fun i j => hf _ _

theorem kronecker_map_smul_right [HasScalar R β] [HasScalar R γ] (f : α → β → γ) (r : R)
    (hf : ∀ a b, f a (r • b) = r • f a b) (A : Matrix l m α) (B : Matrix n p β) :
    kronecker_map f A (r • B) = r • kronecker_map f A B :=
  ext $ fun i j => hf _ _

theorem kronecker_map_diagonal_diagonal [HasZero α] [HasZero β] [HasZero γ] [DecidableEq m] [DecidableEq n]
    (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : m → α) (b : n → β) :
    kronecker_map f (diagonal a) (diagonal b) = diagonal fun mn => f (a mn.1) (b mn.2) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂]

@[simp]
theorem kronecker_map_one_one [HasZero α] [HasZero β] [HasZero γ] [HasOne α] [HasOne β] [HasOne γ] [DecidableEq m]
    [DecidableEq n] (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (hf₃ : f 1 1 = 1) :
    kronecker_map f (1 : Matrix m m α) (1 : Matrix n n β) = 1 :=
  (kronecker_map_diagonal_diagonal _ hf₁ hf₂ _ _).trans $ by
    simp only [hf₃, diagonal_one]

theorem kronecker_map_reindex (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (en : n ≃ n') (ep : p ≃ p') (M : Matrix l m α)
    (N : Matrix n p β) :
    kronecker_map f (reindex el em M) (reindex en ep N) =
      reindex (el.prod_congr en) (em.prod_congr ep) (kronecker_map f M N) :=
  by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  rfl

theorem kronecker_map_reindex_left (f : α → β → γ) (el : l ≃ l') (em : m ≃ m') (M : Matrix l m α) (N : Matrix n n' β) :
    kronecker_map f (Matrix.reindex el em M) N =
      reindex (el.prod_congr (Equivₓ.refl _)) (em.prod_congr (Equivₓ.refl _)) (kronecker_map f M N) :=
  kronecker_map_reindex _ _ _ (Equivₓ.refl _) (Equivₓ.refl _) _ _

theorem kronecker_map_reindex_right (f : α → β → γ) (em : m ≃ m') (en : n ≃ n') (M : Matrix l l' α) (N : Matrix m n β) :
    kronecker_map f M (reindex em en N) =
      reindex ((Equivₓ.refl _).prodCongr em) ((Equivₓ.refl _).prodCongr en) (kronecker_map f M N) :=
  kronecker_map_reindex _ (Equivₓ.refl _) (Equivₓ.refl _) _ _ _ _

theorem kronecker_map_assoc {δ ξ ω ω' : Type _} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω') (g' : β → δ → ξ)
    (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ) (φ : ω ≃ ω')
    (hφ : ∀ a b d, φ (g (f a b) d) = f' a (g' b d)) :
    (reindex (Equivₓ.prodAssoc l n q) (Equivₓ.prodAssoc m p r)).trans (Equivₓ.mapMatrix φ)
        (kronecker_map g (kronecker_map f A B) D) =
      kronecker_map f' A (kronecker_map g' B D) :=
  ext $ fun i j => hφ _ _ _

theorem kronecker_map_assoc₁ {δ ξ ω : Type _} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω) (g' : β → δ → ξ)
    (A : Matrix l m α) (B : Matrix n p β) (D : Matrix q r δ) (h : ∀ a b d, g (f a b) d = f' a (g' b d)) :
    reindex (Equivₓ.prodAssoc l n q) (Equivₓ.prodAssoc m p r) (kronecker_map g (kronecker_map f A B) D) =
      kronecker_map f' A (kronecker_map g' B D) :=
  ext $ fun i j => h _ _ _

/-- When `f` is bilinear then `matrix.kronecker_map f` is also bilinear. -/
@[simps]
def kronecker_map_bilinear [CommSemiringₓ R] [AddCommMonoidₓ α] [AddCommMonoidₓ β] [AddCommMonoidₓ γ] [Module R α]
    [Module R β] [Module R γ] (f : α →ₗ[R] β →ₗ[R] γ) :
    Matrix l m α →ₗ[R] Matrix n p β →ₗ[R] Matrix (l × n) (m × p) γ :=
  LinearMap.mk₂ R (kronecker_map fun r s => f r s) (kronecker_map_add_left _ $ f.map_add₂)
    (fun r => kronecker_map_smul_left _ _ $ f.map_smul₂ _) (kronecker_map_add_right _ $ fun a => (f a).map_add) fun r =>
    kronecker_map_smul_right _ _ $ fun a => (f a).map_smul r

/-- `matrix.kronecker_map_bilinear` commutes with `⬝` if `f` commutes with `*`.

This is primarily used with `R = ℕ` to prove `matrix.mul_kronecker_mul`. -/
theorem kronecker_map_bilinear_mul_mul [CommSemiringₓ R] [Fintype m] [Fintype m'] [NonUnitalNonAssocSemiring α]
    [NonUnitalNonAssocSemiring β] [NonUnitalNonAssocSemiring γ] [Module R α] [Module R β] [Module R γ]
    (f : α →ₗ[R] β →ₗ[R] γ) (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b') (A : Matrix l m α)
    (B : Matrix m n α) (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    kronecker_map_bilinear f (A ⬝ B) (A' ⬝ B') = kronecker_map_bilinear f A A' ⬝ kronecker_map_bilinear f B B' := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp only [kronecker_map_bilinear_apply_apply, mul_apply, ← Finset.univ_product_univ, Finset.sum_product,
    kronecker_map]
  simp_rw [f.map_sum, LinearMap.sum_apply, LinearMap.map_sum, h_comm]

end KroneckerMap

/-! ### Specialization to `matrix.kronecker_map (*)` -/


section Kronecker

variable (R)

open_locale Matrix

/-- The Kronecker product. This is just a shorthand for `kronecker_map (*)`. Prefer the notation
`⊗ₖ` rather than this definition. -/
@[simp]
def kronecker [Mul α] : Matrix l m α → Matrix n p α → Matrix (l × n) (m × p) α :=
  kronecker_map (· * ·)

localized [Kronecker] infixl:100 " ⊗ₖ " => Matrix.kroneckerMapₓ (· * ·)

@[simp]
theorem kronecker_apply [Mul α] (A : Matrix l m α) (B : Matrix n p α) i₁ i₂ j₁ j₂ :
    (A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂ :=
  rfl

/-- `matrix.kronecker` as a bilinear map. -/
def kronecker_bilinear [CommSemiringₓ R] [Semiringₓ α] [Algebra R α] :
    Matrix l m α →ₗ[R] Matrix n p α →ₗ[R] Matrix (l × n) (m × p) α :=
  kronecker_map_bilinear (Algebra.lmul R α).toLinearMap

/-! What follows is a copy, in order, of every `matrix.kronecker_map` lemma above that has
hypotheses which can be filled by properties of `*`. -/


@[simp]
theorem zero_kronecker [MulZeroClass α] (B : Matrix n p α) : (0 : Matrix l m α) ⊗ₖ B = 0 :=
  kronecker_map_zero_left _ zero_mul B

@[simp]
theorem kronecker_zero [MulZeroClass α] (A : Matrix l m α) : A ⊗ₖ (0 : Matrix n p α) = 0 :=
  kronecker_map_zero_right _ mul_zero A

theorem add_kronecker [Distrib α] (A₁ A₂ : Matrix l m α) (B : Matrix n p α) : (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B :=
  kronecker_map_add_left _ add_mulₓ _ _ _

theorem kronecker_add [Distrib α] (A : Matrix l m α) (B₁ B₂ : Matrix n p α) : A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ :=
  kronecker_map_add_right _ mul_addₓ _ _ _

theorem smul_kronecker [Monoidₓ R] [Monoidₓ α] [MulAction R α] [IsScalarTower R α α] (r : R) (A : Matrix l m α)
    (B : Matrix n p α) : (r • A) ⊗ₖ B = r • A ⊗ₖ B :=
  kronecker_map_smul_left _ _ (fun _ _ => smul_mul_assoc _ _ _) _ _

theorem kronecker_smul [Monoidₓ R] [Monoidₓ α] [MulAction R α] [SmulCommClass R α α] (r : R) (A : Matrix l m α)
    (B : Matrix n p α) : A ⊗ₖ (r • B) = r • A ⊗ₖ B :=
  kronecker_map_smul_right _ _ (fun _ _ => mul_smul_comm _ _ _) _ _

theorem diagonal_kronecker_diagonal [MulZeroClass α] [DecidableEq m] [DecidableEq n] (a : m → α) (b : n → α) :
    diagonal a ⊗ₖ diagonal b = diagonal fun mn => a mn.1 * b mn.2 :=
  kronecker_map_diagonal_diagonal _ zero_mul mul_zero _ _

@[simp]
theorem one_kronecker_one [MulZeroOneClass α] [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m α) ⊗ₖ (1 : Matrix n n α) = 1 :=
  kronecker_map_one_one _ zero_mul mul_zero (one_mulₓ _)

theorem mul_kronecker_mul [Fintype m] [Fintype m'] [CommSemiringₓ α] (A : Matrix l m α) (B : Matrix m n α)
    (A' : Matrix l' m' α) (B' : Matrix m' n' α) : (A ⬝ B) ⊗ₖ (A' ⬝ B') = A ⊗ₖ A' ⬝ B ⊗ₖ B' :=
  kronecker_map_bilinear_mul_mul (Algebra.lmul ℕ α).toLinearMap mul_mul_mul_commₓ A B A' B'

@[simp]
theorem kronecker_assoc [Semigroupₓ α] (A : Matrix l m α) (B : Matrix n p α) (C : Matrix q r α) :
    reindex (Equivₓ.prodAssoc l n q) (Equivₓ.prodAssoc m p r) (A ⊗ₖ B ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C) :=
  kronecker_map_assoc₁ _ _ _ _ A B C mul_assocₓ

end Kronecker

/-! ### Specialization to `matrix.kronecker_map (⊗ₜ)` -/


section KroneckerTmul

variable (R)

open TensorProduct

open_locale Matrix TensorProduct

section Module

variable [CommSemiringₓ R] [AddCommMonoidₓ α] [AddCommMonoidₓ β] [AddCommMonoidₓ γ]

variable [Module R α] [Module R β] [Module R γ]

/-- The Kronecker tensor product. This is just a shorthand for `kronecker_map (⊗ₜ)`.
Prefer the notation `⊗ₖₜ` rather than this definition. -/
@[simp]
def kronecker_tmul : Matrix l m α → Matrix n p β → Matrix (l × n) (m × p) (α ⊗[R] β) :=
  kronecker_map (· ⊗ₜ ·)

localized [Kronecker] infixl:100 " ⊗ₖₜ " => Matrix.kroneckerMapₓ (· ⊗ₜ ·)

localized [Kronecker] notation:100 x " ⊗ₖₜ[" R "] " y:100 => Matrix.kroneckerMapₓ (TensorProduct.tmul R) x y

@[simp]
theorem kronecker_tmul_apply (A : Matrix l m α) (B : Matrix n p β) i₁ i₂ j₁ j₂ :
    (A ⊗ₖₜ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ ⊗ₜ[R] B i₂ j₂ :=
  rfl

/-- `matrix.kronecker` as a bilinear map. -/
def kronecker_tmul_bilinear : Matrix l m α →ₗ[R] Matrix n p β →ₗ[R] Matrix (l × n) (m × p) (α ⊗[R] β) :=
  kronecker_map_bilinear (TensorProduct.mk R α β)

/-! What follows is a copy, in order, of every `matrix.kronecker_map` lemma above that has
hypotheses which can be filled by properties of `⊗ₜ`. -/


@[simp]
theorem zero_kronecker_tmul (B : Matrix n p β) : (0 : Matrix l m α) ⊗ₖₜ[R] B = 0 :=
  kronecker_map_zero_left _ (zero_tmul α) B

@[simp]
theorem kronecker_tmul_zero (A : Matrix l m α) : A ⊗ₖₜ[R] (0 : Matrix n p β) = 0 :=
  kronecker_map_zero_right _ (tmul_zero β) A

theorem add_kronecker_tmul (A₁ A₂ : Matrix l m α) (B : Matrix n p α) : (A₁ + A₂) ⊗ₖₜ[R] B = A₁ ⊗ₖₜ B + A₂ ⊗ₖₜ B :=
  kronecker_map_add_left _ add_tmul _ _ _

theorem kronecker_tmul_add (A : Matrix l m α) (B₁ B₂ : Matrix n p α) : A ⊗ₖₜ[R] (B₁ + B₂) = A ⊗ₖₜ B₁ + A ⊗ₖₜ B₂ :=
  kronecker_map_add_right _ tmul_add _ _ _

theorem smul_kronecker_tmul (r : R) (A : Matrix l m α) (B : Matrix n p α) : (r • A) ⊗ₖₜ[R] B = r • A ⊗ₖₜ B :=
  kronecker_map_smul_left _ _ (fun _ _ => smul_tmul' _ _ _) _ _

theorem kronecker_tmul_smul (r : R) (A : Matrix l m α) (B : Matrix n p α) : A ⊗ₖₜ[R] (r • B) = r • A ⊗ₖₜ B :=
  kronecker_map_smul_right _ _ (fun _ _ => tmul_smul _ _ _) _ _

theorem diagonal_kronecker_tmul_diagonal [DecidableEq m] [DecidableEq n] (a : m → α) (b : n → α) :
    diagonal a ⊗ₖₜ[R] diagonal b = diagonal fun mn => a mn.1 ⊗ₜ b mn.2 :=
  kronecker_map_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _

@[simp]
theorem kronecker_tmul_assoc (A : Matrix l m α) (B : Matrix n p β) (C : Matrix q r γ) :
    reindex (Equivₓ.prodAssoc l n q) (Equivₓ.prodAssoc m p r)
        (((A ⊗ₖₜ[R] B) ⊗ₖₜ[R] C).map (TensorProduct.assoc _ _ _ _)) =
      A ⊗ₖₜ[R] B ⊗ₖₜ[R] C :=
  ext $ fun i j => assoc_tmul _ _ _

end Module

section Algebra

variable [CommSemiringₓ R] [Semiringₓ α] [Semiringₓ β] [Algebra R α] [Algebra R β]

open_locale Kronecker

open Algebra.TensorProduct

@[simp]
theorem one_kronecker_tmul_one [DecidableEq m] [DecidableEq n] : (1 : Matrix m m α) ⊗ₖₜ[R] (1 : Matrix n n α) = 1 :=
  kronecker_map_one_one _ (zero_tmul _) (tmul_zero _) rfl

theorem mul_kronecker_tmul_mul [Fintype m] [Fintype m'] (A : Matrix l m α) (B : Matrix m n α) (A' : Matrix l' m' β)
    (B' : Matrix m' n' β) : (A ⬝ B) ⊗ₖₜ[R] (A' ⬝ B') = A ⊗ₖₜ A' ⬝ B ⊗ₖₜ B' :=
  kronecker_map_bilinear_mul_mul (TensorProduct.mk R α β) tmul_mul_tmul A B A' B'

end Algebra

end KroneckerTmul

end Matrix

