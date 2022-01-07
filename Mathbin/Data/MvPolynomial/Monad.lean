import Mathbin.Data.MvPolynomial.Rename

/-!

# Monad operations on `mv_polynomial`

This file defines two monadic operations on `mv_polynomial`. Given `p : mv_polynomial σ R`,

* `mv_polynomial.bind₁` and `mv_polynomial.join₁` operate on the variable type `σ`.
* `mv_polynomial.bind₂` and `mv_polynomial.join₂` operate on the coefficient type `R`.

- `mv_polynomial.bind₁ f φ` with `f : σ → mv_polynomial τ R` and `φ : mv_polynomial σ R`,
  is the polynomial `φ(f 1, ..., f i, ...) : mv_polynomial τ R`.
- `mv_polynomial.join₁ φ` with `φ : mv_polynomial (mv_polynomial σ R) R` collapses `φ` to
  a `mv_polynomial σ R`, by evaluating `φ` under the map `X f ↦ f` for `f : mv_polynomial σ R`.
  In other words, if you have a polynomial `φ` in a set of variables indexed by a polynomial ring,
  you evaluate the polynomial in these indexing polynomials.
- `mv_polynomial.bind₂ f φ` with `f : R →+* mv_polynomial σ S` and `φ : mv_polynomial σ R`
  is the `mv_polynomial σ S` obtained from `φ` by mapping the coefficients of `φ` through `f`
  and considering the resulting polynomial as polynomial expression in `mv_polynomial σ R`.
- `mv_polynomial.join₂ φ` with `φ : mv_polynomial σ (mv_polynomial σ R)` collapses `φ` to
  a `mv_polynomial σ R`, by considering `φ` as polynomial expression in `mv_polynomial σ R`.

These operations themselves have algebraic structure: `mv_polynomial.bind₁`
and `mv_polynomial.join₁` are algebra homs and
`mv_polynomial.bind₂` and `mv_polynomial.join₂` are ring homs.

They interact in convenient ways with `mv_polynomial.rename`, `mv_polynomial.map`,
`mv_polynomial.vars`, and other polynomial operations.
Indeed, `mv_polynomial.rename` is the "map" operation for the (`bind₁`, `join₁`) pair,
whereas `mv_polynomial.map` is the "map" operation for the other pair.

## Implementation notes

We add an `is_lawful_monad` instance for the (`bind₁`, `join₁`) pair.
The second pair cannot be instantiated as a `monad`,
since it is not a monad in `Type` but in `CommRing` (or rather `CommSemiRing`).

-/


open_locale BigOperators

noncomputable section

namespace MvPolynomial

open Finsupp

variable {σ : Type _} {τ : Type _}

variable {R S T : Type _} [CommSemiringₓ R] [CommSemiringₓ S] [CommSemiringₓ T]

/-- `bind₁` is the "left hand side" bind operation on `mv_polynomial`, operating on the variable type.
Given a polynomial `p : mv_polynomial σ R` and a map `f : σ → mv_polynomial τ R` taking variables
in `p` to polynomials in the variable type `τ`, `bind₁ f p` replaces each variable in `p` with
its value under `f`, producing a new polynomial in `τ`. The coefficient type remains the same.
This operation is an algebra hom.
-/
def bind₁ (f : σ → MvPolynomial τ R) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval f

/-- `bind₂` is the "right hand side" bind operation on `mv_polynomial`,
operating on the coefficient type.
Given a polynomial `p : mv_polynomial σ R` and
a map `f : R → mv_polynomial σ S` taking coefficients in `p` to polynomials over a new ring `S`,
`bind₂ f p` replaces each coefficient in `p` with its value under `f`,
producing a new polynomial over `S`.
The variable type remains the same. This operation is a ring hom.
-/
def bind₂ (f : R →+* MvPolynomial σ S) : MvPolynomial σ R →+* MvPolynomial σ S :=
  eval₂_hom f X

/-- `join₁` is the monadic join operation corresponding to `mv_polynomial.bind₁`. Given a polynomial `p`
with coefficients in `R` whose variables are polynomials in `σ` with coefficients in `R`,
`join₁ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is an algebra hom.
-/
def join₁ : MvPolynomial (MvPolynomial σ R) R →ₐ[R] MvPolynomial σ R :=
  aeval id

/-- `join₂` is the monadic join operation corresponding to `mv_polynomial.bind₂`. Given a polynomial `p`
with variables in `σ` whose coefficients are polynomials in `σ` with coefficients in `R`,
`join₂ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is a ring hom.
-/
def join₂ : MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ R :=
  eval₂_hom (RingHom.id _) X

@[simp]
theorem aeval_eq_bind₁ (f : σ → MvPolynomial τ R) : aeval f = bind₁ f :=
  rfl

@[simp]
theorem eval₂_hom_C_eq_bind₁ (f : σ → MvPolynomial τ R) : eval₂_hom C f = bind₁ f :=
  rfl

@[simp]
theorem eval₂_hom_eq_bind₂ (f : R →+* MvPolynomial σ S) : eval₂_hom f X = bind₂ f :=
  rfl

section

variable (σ R)

@[simp]
theorem aeval_id_eq_join₁ : aeval id = @join₁ σ R _ :=
  rfl

theorem eval₂_hom_C_id_eq_join₁ (φ : MvPolynomial (MvPolynomial σ R) R) : eval₂_hom C id φ = join₁ φ :=
  rfl

@[simp]
theorem eval₂_hom_id_X_eq_join₂ : eval₂_hom (RingHom.id _) X = @join₂ σ R _ :=
  rfl

end

attribute [-simp] aeval_eq_bind₁ eval₂_hom_C_eq_bind₁ eval₂_hom_eq_bind₂ aeval_id_eq_join₁ eval₂_hom_id_X_eq_join₂

@[simp]
theorem bind₁_X_right (f : σ → MvPolynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
  aeval_X f i

@[simp]
theorem bind₂_X_right (f : R →+* MvPolynomial σ S) (i : σ) : bind₂ f (X i) = X i :=
  eval₂_hom_X' f X i

@[simp]
theorem bind₁_X_left : bind₁ (X : σ → MvPolynomial σ R) = AlgHom.id R _ := by
  ext1 i
  simp

theorem aeval_X_left : aeval (X : σ → MvPolynomial σ R) = AlgHom.id R _ := by
  rw [aeval_eq_bind₁, bind₁_X_left]

theorem aeval_X_left_apply (φ : MvPolynomial σ R) : aeval X φ = φ := by
  rw [aeval_eq_bind₁, bind₁_X_left, AlgHom.id_apply]

variable (f : σ → MvPolynomial τ R)

@[simp]
theorem bind₁_C_right (f : σ → MvPolynomial τ R) x : bind₁ f (C x) = C x := by
  simp [bind₁, algebra_map_eq]

@[simp]
theorem bind₂_C_right (f : R →+* MvPolynomial σ S) (r : R) : bind₂ f (C r) = f r :=
  eval₂_hom_C f X r

@[simp]
theorem bind₂_C_left : bind₂ (C : R →+* MvPolynomial σ R) = RingHom.id _ := by
  ext : 2 <;> simp

@[simp]
theorem bind₂_comp_C (f : R →+* MvPolynomial σ S) : (bind₂ f).comp C = f :=
  RingHom.ext $ bind₂_C_right _

@[simp]
theorem join₂_map (f : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) : join₂ (map f φ) = bind₂ f φ := by
  simp only [join₂, bind₂, eval₂_hom_map_hom, RingHom.id_comp]

@[simp]
theorem join₂_comp_map (f : R →+* MvPolynomial σ S) : join₂.comp (map f) = bind₂ f :=
  RingHom.ext $ join₂_map _

theorem aeval_id_rename (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) : aeval id (rename f p) = aeval f p := by
  rw [aeval_rename, Function.comp.left_id]

@[simp]
theorem join₁_rename (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) : join₁ (rename f φ) = bind₁ f φ :=
  aeval_id_rename _ _

@[simp]
theorem bind₁_id : bind₁ (@id (MvPolynomial σ R)) = join₁ :=
  rfl

@[simp]
theorem bind₂_id : bind₂ (RingHom.id (MvPolynomial σ R)) = join₂ :=
  rfl

theorem bind₁_bind₁ {υ : Type _} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R) (φ : MvPolynomial σ R) :
    (bind₁ g) (bind₁ f φ) = bind₁ (fun i => bind₁ g (f i)) φ := by
  simp [bind₁, ← comp_aeval]

theorem bind₁_comp_bind₁ {υ : Type _} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R) :
    (bind₁ g).comp (bind₁ f) = bind₁ fun i => bind₁ g (f i) := by
  ext1
  apply bind₁_bind₁

theorem bind₂_comp_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T) :
    (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) := by
  ext : 2 <;> simp

theorem bind₂_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T) (φ : MvPolynomial σ R) :
    (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
  RingHom.congr_fun (bind₂_comp_bind₂ f g) φ

theorem rename_comp_bind₁ {υ : Type _} (f : σ → MvPolynomial τ R) (g : τ → υ) :
    (rename g).comp (bind₁ f) = bind₁ fun i => rename g $ f i := by
  ext1 i
  simp

theorem rename_bind₁ {υ : Type _} (f : σ → MvPolynomial τ R) (g : τ → υ) (φ : MvPolynomial σ R) :
    rename g (bind₁ f φ) = bind₁ (fun i => rename g $ f i) φ :=
  AlgHom.congr_fun (rename_comp_bind₁ f g) φ

theorem map_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* T) (φ : MvPolynomial σ R) :
    map g (bind₂ f φ) = bind₂ ((map g).comp f) φ := by
  simp only [bind₂, eval₂_comp_right, coe_eval₂_hom, eval₂_map]
  congr 1 with : 1
  simp only [Function.comp_app, map_X]

theorem bind₁_comp_rename {υ : Type _} (f : τ → MvPolynomial υ R) (g : σ → τ) :
    (bind₁ f).comp (rename g) = bind₁ (f ∘ g) := by
  ext1 i
  simp

theorem bind₁_rename {υ : Type _} (f : τ → MvPolynomial υ R) (g : σ → τ) (φ : MvPolynomial σ R) :
    bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
  AlgHom.congr_fun (bind₁_comp_rename f g) φ

theorem bind₂_map (f : S →+* MvPolynomial σ T) (g : R →+* S) (φ : MvPolynomial σ R) :
    bind₂ f (map g φ) = bind₂ (f.comp g) φ := by
  simp [bind₂]

@[simp]
theorem map_comp_C (f : R →+* S) : (map f).comp (C : R →+* MvPolynomial σ R) = C.comp f := by
  ext1
  apply map_C

theorem hom_bind₁ (f : MvPolynomial τ R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    f (bind₁ g φ) = eval₂_hom (f.comp C) (fun i => f (g i)) φ := by
  rw [bind₁, map_aeval, algebra_map_eq]

theorem map_bind₁ (f : R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g i)) (map f φ) := by
  rw [hom_bind₁, map_comp_C, ← eval₂_hom_map_hom]
  rfl

@[simp]
theorem eval₂_hom_comp_C (f : R →+* S) (g : σ → S) : (eval₂_hom f g).comp C = f := by
  ext1 r
  exact eval₂_C f g r

theorem eval₂_hom_bind₁ (f : R →+* S) (g : τ → S) (h : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval₂_hom f g (bind₁ h φ) = eval₂_hom f (fun i => eval₂_hom f g (h i)) φ := by
  rw [hom_bind₁, eval₂_hom_comp_C]

theorem aeval_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    aeval f (bind₁ g φ) = aeval (fun i => aeval f (g i)) φ :=
  eval₂_hom_bind₁ _ _ _ _

theorem aeval_comp_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) :
    (aeval f).comp (bind₁ g) = aeval fun i => aeval f (g i) := by
  ext1
  apply aeval_bind₁

theorem eval₂_hom_comp_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S) :
    (eval₂_hom f g).comp (bind₂ h) = eval₂_hom ((eval₂_hom f g).comp h) g := by
  ext : 2 <;> simp

theorem eval₂_hom_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    eval₂_hom f g (bind₂ h φ) = eval₂_hom ((eval₂_hom f g).comp h) g φ :=
  RingHom.congr_fun (eval₂_hom_comp_bind₂ f g h) φ

theorem aeval_bind₂ [Algebra S T] (f : σ → T) (g : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    aeval f (bind₂ g φ) = eval₂_hom ((↑(aeval f : _ →ₐ[S] _) : _ →+* _).comp g) f φ :=
  eval₂_hom_bind₂ _ _ _ _

theorem eval₂_hom_C_left (f : σ → MvPolynomial τ R) : eval₂_hom C f = bind₁ f :=
  rfl

theorem bind₁_monomial (f : σ → MvPolynomial τ R) (d : σ →₀ ℕ) (r : R) :
    bind₁ f (monomial d r) = C r * ∏ i in d.support, f i ^ d i := by
  simp only [monomial_eq, AlgHom.map_mul, bind₁_C_right, Finsupp.prod, AlgHom.map_prod, AlgHom.map_pow, bind₁_X_right]

theorem bind₂_monomial (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) (r : R) :
    bind₂ f (monomial d r) = f r * monomial d 1 := by
  simp only [monomial_eq, RingHom.map_mul, bind₂_C_right, Finsupp.prod, RingHom.map_prod, RingHom.map_pow,
    bind₂_X_right, C_1, one_mulₓ]

@[simp]
theorem bind₂_monomial_one (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) : bind₂ f (monomial d 1) = monomial d 1 := by
  rw [bind₂_monomial, f.map_one, one_mulₓ]

instance Monadₓ : Monadₓ fun σ => MvPolynomial σ R where
  map := fun α β f p => rename f p
  pure := fun _ => X
  bind := fun _ _ p f => bind₁ f p

instance IsLawfulFunctor : IsLawfulFunctor fun σ => MvPolynomial σ R where
  id_map := by
    intros <;> simp [· <$> ·]
  comp_map := by
    intros <;> simp [· <$> ·]

instance IsLawfulMonad : IsLawfulMonad fun σ => MvPolynomial σ R where
  pure_bind := by
    intros <;> simp [pure, bind]
  bind_assoc := by
    intros <;> simp [bind, ← bind₁_comp_bind₁]

end MvPolynomial

