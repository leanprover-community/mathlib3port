import Mathbin.LinearAlgebra.Basic

/-!
# Basics on bilinear maps

This file provides basics on bilinear maps.

## Main declarations

* `linear_map.mk₂`: a constructor for bilinear maps,
  taking an unbundled function together with proof witnesses of bilinearity
* `linear_map.flip`: turns a bilinear map `M × N → P` into `N × M → P`
* `linear_map.lcomp` and `linear_map.llcomp`: composition of linear maps as a bilinear map
* `linear_map.compl₂`: composition of a bilinear map `M × N → P` with a linear map `Q → M`
* `linear_map.compr₂`: composition of a bilinear map `M × N → P` with a linear map `Q → N`
* `linear_map.lsmul`: scalar multiplication as a bilinear map `R × M → M`

## Tags

bilinear
-/


namespace LinearMap

section Semiringₓ

variable{R : Type _}[Semiringₓ R]{S : Type _}[Semiringₓ S]

variable{M : Type _}{N : Type _}{P : Type _}

variable{M' : Type _}{N' : Type _}{P' : Type _}

variable[AddCommMonoidₓ M][AddCommMonoidₓ N][AddCommMonoidₓ P]

variable[AddCommGroupₓ M'][AddCommGroupₓ N'][AddCommGroupₓ P']

variable[Module R M][Module S N][Module R P][Module S P]

variable[Module R M'][Module S N'][Module R P'][Module S P']

variable[SmulCommClass S R P][SmulCommClass S R P']

include R

variable(R S)

/-- Create a bilinear map from a function that is linear in each component.
See `mk₂` for the special case where both arguments come from modules over the same ring. -/
def mk₂' (f : M → N → P) (H1 : ∀ m₁ m₂ n, f (m₁+m₂) n = f m₁ n+f m₂ n) (H2 : ∀ c : R m n, f (c • m) n = c • f m n)
  (H3 : ∀ m n₁ n₂, f m (n₁+n₂) = f m n₁+f m n₂) (H4 : ∀ c : S m n, f m (c • n) = c • f m n) : M →ₗ[R] N →ₗ[S] P :=
  { toFun := fun m => { toFun := f m, map_add' := H3 m, map_smul' := fun c => H4 c m },
    map_add' := fun m₁ m₂ => LinearMap.ext$ H1 m₁ m₂, map_smul' := fun c m => LinearMap.ext$ H2 c m }

variable{R S}

@[simp]
theorem mk₂'_apply (f : M → N → P) {H1 H2 H3 H4} (m : M) (n : N) :
  (mk₂' R S f H1 H2 H3 H4 : M →ₗ[R] N →ₗ[S] P) m n = f m n :=
  rfl

theorem ext₂ {f g : M →ₗ[R] N →ₗ[S] P} (H : ∀ m n, f m n = g m n) : f = g :=
  LinearMap.ext fun m => LinearMap.ext$ fun n => H m n

section 

attribute [local instance] SmulCommClass.symm

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to
`P`, change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def flip (f : M →ₗ[R] N →ₗ[S] P) : N →ₗ[S] M →ₗ[R] P :=
  mk₂' S R (fun n m => f m n) (fun n₁ n₂ m => (f m).map_add _ _) (fun c n m => (f m).map_smul _ _)
    (fun n m₁ m₂ =>
      by 
        rw [f.map_add] <;> rfl)
    fun c n m =>
      by 
        rw [f.map_smul] <;> rfl

end 

@[simp]
theorem flip_apply (f : M →ₗ[R] N →ₗ[S] P) (m : M) (n : N) : flip f n m = f m n :=
  rfl

open_locale BigOperators

variable{R}

theorem flip_inj {f g : M →ₗ[R] N →ₗ[S] P} (H : flip f = flip g) : f = g :=
  ext₂$
    fun m n =>
      show flip f n m = flip g n m by 
        rw [H]

theorem map_zero₂ (f : M →ₗ[R] N →ₗ[S] P) y : f 0 y = 0 :=
  (flip f y).map_zero

theorem map_neg₂ (f : M' →ₗ[R] N →ₗ[S] P') x y : f (-x) y = -f x y :=
  (flip f y).map_neg _

theorem map_sub₂ (f : M' →ₗ[R] N →ₗ[S] P') x y z : f (x - y) z = f x z - f y z :=
  (flip f z).map_sub _ _

theorem map_add₂ (f : M →ₗ[R] N →ₗ[S] P) x₁ x₂ y : f (x₁+x₂) y = f x₁ y+f x₂ y :=
  (flip f y).map_add _ _

theorem map_smul₂ (f : M →ₗ[R] N →ₗ[S] P) (r : R) x y : f (r • x) y = r • f x y :=
  (flip f y).map_smul _ _

theorem map_sum₂ {ι : Type _} (f : M →ₗ[R] N →ₗ[S] P) (t : Finset ι) (x : ι → M) y :
  f (∑i in t, x i) y = ∑i in t, f (x i) y :=
  (flip f y).map_sum

end Semiringₓ

section CommSemiringₓ

variable{R : Type _}[CommSemiringₓ R]

variable{M : Type _}{N : Type _}{P : Type _}{Q : Type _}

variable[AddCommMonoidₓ M][AddCommMonoidₓ N][AddCommMonoidₓ P][AddCommMonoidₓ Q]

variable[Module R M][Module R N][Module R P][Module R Q]

variable(R)

/-- Create a bilinear map from a function that is linear in each component.

This is a shorthand for `mk₂'` for the common case when `R = S`. -/
def mk₂ (f : M → N → P) (H1 : ∀ m₁ m₂ n, f (m₁+m₂) n = f m₁ n+f m₂ n) (H2 : ∀ c : R m n, f (c • m) n = c • f m n)
  (H3 : ∀ m n₁ n₂, f m (n₁+n₂) = f m n₁+f m n₂) (H4 : ∀ c : R m n, f m (c • n) = c • f m n) : M →ₗ[R] N →ₗ[R] P :=
  mk₂' R R f H1 H2 H3 H4

@[simp]
theorem mk₂_apply (f : M → N → P) {H1 H2 H3 H4} (m : M) (n : N) :
  (mk₂ R f H1 H2 H3 H4 : M →ₗ[R] N →ₗ[R] P) m n = f m n :=
  rfl

variable(R M N P)

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map `M → N → P`,
change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def lflip : (M →ₗ[R] N →ₗ[R] P) →ₗ[R] N →ₗ[R] M →ₗ[R] P :=
  { toFun := flip, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

variable{R M N P}

variable(f : M →ₗ[R] N →ₗ[R] P)

@[simp]
theorem lflip_apply (m : M) (n : N) : lflip R M N P f n m = f m n :=
  rfl

variable(R P)

/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def lcomp (f : M →ₗ[R] N) : (N →ₗ[R] P) →ₗ[R] M →ₗ[R] P :=
  flip$ LinearMap.comp (flip id) f

variable{R P}

@[simp]
theorem lcomp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (x : M) : lcomp R P f g x = g (f x) :=
  rfl

variable(R M N P)

/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def llcomp : (N →ₗ[R] P) →ₗ[R] (M →ₗ[R] N) →ₗ[R] M →ₗ[R] P :=
  flip
    { toFun := lcomp R P, map_add' := fun f f' => ext₂$ fun g x => g.map_add _ _,
      map_smul' := fun c : R f => ext₂$ fun g x => g.map_smul _ _ }

variable{R M N P}

section 

@[simp]
theorem llcomp_apply (f : N →ₗ[R] P) (g : M →ₗ[R] N) (x : M) : llcomp R M N P f g x = f (g x) :=
  rfl

end 

/-- Composing a linear map `Q → N` and a bilinear map `M → N → P` to
form a bilinear map `M → Q → P`. -/
def compl₂ (g : Q →ₗ[R] N) : M →ₗ[R] Q →ₗ[R] P :=
  (lcomp R _ g).comp f

@[simp]
theorem compl₂_apply (g : Q →ₗ[R] N) (m : M) (q : Q) : f.compl₂ g m q = f m (g q) :=
  rfl

/-- Composing a linear map `P → Q` and a bilinear map `M → N → P` to
form a bilinear map `M → N → Q`. -/
def compr₂ (g : P →ₗ[R] Q) : M →ₗ[R] N →ₗ[R] Q :=
  LinearMap.comp (llcomp R N P Q g) f

@[simp]
theorem compr₂_apply (g : P →ₗ[R] Q) (m : M) (n : N) : f.compr₂ g m n = g (f m n) :=
  rfl

variable(R M)

/-- Scalar multiplication as a bilinear map `R → M → M`. -/
def lsmul : R →ₗ[R] M →ₗ[R] M :=
  mk₂ R (· • ·) add_smul (fun _ _ _ => mul_smul _ _ _) smul_add
    fun r s m =>
      by 
        simp only [smul_smul, smul_eq_mul, mul_commₓ]

variable{R M}

@[simp]
theorem lsmul_apply (r : R) (m : M) : lsmul R M r m = r • m :=
  rfl

end CommSemiringₓ

section CommRingₓ

variable{R M : Type _}[CommRingₓ R][AddCommGroupₓ M][Module R M]

theorem lsmul_injective [NoZeroSmulDivisors R M] {x : R} (hx : x ≠ 0) : Function.Injective (lsmul R M x) :=
  smul_right_injective _ hx

theorem ker_lsmul [NoZeroSmulDivisors R M] {a : R} (ha : a ≠ 0) : (LinearMap.lsmul R M a).ker = ⊥ :=
  LinearMap.ker_eq_bot_of_injective (LinearMap.lsmul_injective ha)

end CommRingₓ

end LinearMap

